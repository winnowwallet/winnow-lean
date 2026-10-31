import Oracle.Base
import Winnow.Tx

/-! Oracle ops for the Tx area (Lean side of LeanOracle/Tx). -/

namespace Oracle
open Lean Winnow

/-! ## JSON plumbing -/

/-- A present, non-null field. -/
def opt (j : Json) (k : String) : Option Json :=
  match j.getObjVal? k with
  | .ok .null => none
  | .ok v => some v
  | .error _ => none

def arr (j : Json) (k : String) : Except String (Array Json) := do (← j.getObjVal? k).getArr?
def int (j : Json) (k : String) : Except String Int := j.getObjValAs? Int k
def bool (j : Json) (k : String) : Except String Bool := j.getObjValAs? Bool k
def hexOf (j : Json) : Except String ByteArray := do
  match ofHex? (← j.getStr?) with
  | some b => pure b
  | none => throw "not hex"
def i64 (j : Json) (k : String) : Except String Int64 := do
  match (← str j k).toInt? with
  | some n => pure (Int64.ofInt n)
  | none => throw s!"{k}: not a decimal string"
def bytesArr (j : Json) (k : String) : Except String (Array ByteArray) := do (← arr j k).mapM hexOf
def optBytes (j : Json) (k : String) : Except String (Option ByteArray) :=
  match opt j k with
  | none => pure none
  | some v => some <$> hexOf v

def hexArr (bs : Array ByteArray) : Json := Json.arr (bs.map hexJ)
def i64J (n : Int64) : Json := Json.str (toString n.toInt)
def u64J (n : UInt64) : Json := Json.str (toString n.toNat)
def natJ (n : Nat) : Json := toJson n
def intJ (n : Int) : Json := toJson n
def optJ {α} (f : α → Json) : Option α → Json
  | some a => f a
  | none => .null

/-! ## Transactions as JSON -/

def txOfJson (j : Json) : Except String Transaction := do
  let inputs ← (← arr j "inputs").mapM fun i => do
    pure ({ previousOutput := ⟨← bytes i "txid", (← nat i "vout").toUInt32⟩, scriptSig := ← bytes i "scriptSig",
            sequence := (← nat i "sequence").toUInt32,
            witness := ← (match opt i "witness" with | some _ => bytesArr i "witness" | none => pure #[]) }
          : Transaction.Input)
  let outputs ← (← arr j "outputs").mapM fun o => do
    pure ({ value := ← i64 o "value", scriptPubKey := ← bytes o "scriptPubKey" } : Transaction.Output)
  pure { version := (← int j "version").toInt32, inputs, outputs, locktime := (← nat j "locktime").toUInt32 }

def txJson (tx : Transaction) : Json := Json.mkObj [
  ("version", intJ tx.version.toInt),
  ("inputs", Json.arr (tx.inputs.map fun i => Json.mkObj [
    ("txid", hexJ i.previousOutput.txid), ("vout", natJ i.previousOutput.vout.toNat),
    ("scriptSig", hexJ i.scriptSig), ("sequence", natJ i.sequence.toNat), ("witness", hexArr i.witness)])),
  ("outputs", Json.arr (tx.outputs.map fun o => Json.mkObj [
    ("value", i64J o.value), ("scriptPubKey", hexJ o.scriptPubKey)])),
  ("locktime", natJ tx.locktime.toNat)]

def txInfo (tx : Transaction) : Json := Json.mkObj [
  ("tx", txJson tx), ("txid", hexJ tx.txid), ("wtxid", hexJ tx.wtxid), ("segwit", toJson tx.isSegwit),
  ("base", hexJ (tx.serialized false)), ("full", hexJ (tx.serialized true))]

/-! ## Wire -/

/-- One read step of `wire.read`: `u8`, `u16`, `u32`, `u64`, `i32`, `i64`, `varint`, `bytes:N`,
`vardata[:max]`, `varstring[:max]`, `remaining`, `end`. -/
def wireStep (s : String) : Except String (ByteReader.M Json) := do
  let parts := s.splitOn ":"
  let arg : Option Nat := (parts[1]?).bind String.toNat?
  match parts[0]! with
  | "u8" => pure do return natJ (← ByteReader.readUInt8).toNat
  | "u16" => pure do return natJ (← ByteReader.readUInt16).toNat
  | "u32" => pure do return natJ (← ByteReader.readUInt32).toNat
  | "u64" => pure do return u64J (← ByteReader.readUInt64)
  | "i32" => pure do return intJ (← ByteReader.readInt32).toInt
  | "i64" => pure do return i64J (← ByteReader.readInt64)
  | "varint" => pure do return u64J (← ByteReader.readVarInt)
  | "bytes" => pure do return hexJ (← ByteReader.readBytes (arg.getD 0))
  | "vardata" => pure do return hexJ (← ByteReader.readVarData (arg.getD 4_000_000))
  | "varstring" => pure do return Json.str (← ByteReader.readVarString (arg.getD 1_000))
  | "remaining" => pure do return natJ (← ByteReader.remainingM)
  | "end" => pure do ByteReader.requireEnd; return .null
  | other => throw s!"step {other}"

def wireWrite (item : Json) : Except String (ByteArray → ByteArray) := do
  let a ← item.getArr?
  let kind ← a[0]!.getStr?
  let v := a[1]!
  let num : Except String Nat := v.getNat?
  let dec : Except String Int := do
    match (← v.getStr?).toInt? with | some n => pure n | none => throw "not decimal"
  match kind with
  | "u8" => let n ← num; pure (Wire.appendUInt8 · n.toUInt8)
  | "u16" => let n ← num; pure (Wire.appendUInt16 · n.toUInt16)
  | "u32" => let n ← num; pure (Wire.appendUInt32 · n.toUInt32)
  | "u64" => let n ← dec; pure (Wire.appendUInt64 · n.toNat.toUInt64)
  | "i32" => let n ← v.getInt?; pure (Wire.appendInt32 · n.toInt32)
  | "i64" => let n ← dec; pure (Wire.appendInt64 · (Int64.ofInt n))
  | "compact" => let n ← dec; pure (Wire.appendCompactSize · n.toNat.toUInt64)
  | "vardata" => let b ← hexOf v; pure (Wire.appendVarData · b)
  | "varstring" => let s ← v.getStr?; pure (Wire.appendVarString · s)
  | other => throw s!"item {other}"

def wireOps : List (String × Handler) := [
  ("wire.read", fun j => do
    let steps ← (← arr j "steps").mapM fun s => do wireStep (← s.getStr?)
    let prog : ByteReader.M (Array Json) := steps.mapM id
    match prog.run (ByteReader.init (← bytes j "data")) with
    | .ok (vs, r) => return ok (Json.mkObj [("values", Json.arr vs), ("offset", natJ r.offset)])
    | .error e => return err e.name),
  ("wire.write", fun j => do
    let fs ← (← arr j "items").mapM wireWrite
    return ok (hexJ (fs.foldl (fun d f => f d) .empty))),
  ("wire.hex", fun j => do
    return ok (optJ (fun b => Json.str (Wire.dataHex b)) (Wire.dataOfHex? (← str j "text"))))
]

def transactionOps : List (String × Handler) := [
  ("tx.decode", fun j => do
    match Transaction.decode (← bytes j "data") with
    | .ok tx => return ok (txInfo tx)
    | .error e => return err e.name),
  ("tx.decodePrefix", fun j => do
    match Transaction.decodeFrom.run (ByteReader.init (← bytes j "data")) with
    | .ok (tx, r) => return ok (Json.mkObj [("info", txInfo tx), ("consumed", natJ r.offset)])
    | .error e => return err e.name),
  ("tx.encode", fun j => do return ok (txInfo (← txOfJson (← j.getObjVal? "tx"))))
]


/-! ## Script, Multisig, the Taproot helpers -/

def scriptStep (s : Script) (step : Json) : Except String Script := do
  let a ← step.getArr?
  let v := a[1]!
  match ← a[0]!.getStr? with
  | "op" => return s.appendOpcode (← v.getNat?).toUInt8
  | "opn" => return s.appendOpcode (Script.Op.n (← v.getNat?))
  | "push" => return s.appendPush (← hexOf v)
  | "num" => match (← v.getStr?).toNat? with
    | some n => return s.appendScriptNumber n
    | none => throw "num"
  | other => throw s!"step {other}"

def controlBlockJ (c : Tx.Taproot.ControlBlock) : Json := Json.mkObj [
  ("leafVersion", natJ c.leafVersion.toNat), ("parity", toJson c.outputKeyParity),
  ("internalKey", hexJ c.internalKey), ("path", hexArr c.path), ("serialized", hexJ c.serialized)]

def scriptOps : List (String × Handler) := [
  ("script.build", fun j => do
    let s ← (← arr j "steps").foldlM scriptStep Script.empty
    return ok (Json.str s.hex)),
  ("script.fromHex", fun j => do return ok (optJ (fun s => Json.str s.hex) (Script.ofHex? (← str j "text")))),
  ("multisig.script", fun j => do
    match Multisig.script (← int j "threshold") (← bytesArr j "keys") (← bool j "sorted") with
    | .ok s => return ok (Json.str s.hex)
    | .error e => return err e.name),
  ("multisig.parse", fun j => do
    return ok (optJ (fun (k, keys) => Json.mkObj [("threshold", Json.str (toString k)), ("keys", hexArr keys)])
      (Multisig.parse ⟨← bytes j "script"⟩))),
  ("tap.controlBlock", fun j => do
    match Tx.Taproot.ControlBlock.parse? (← bytes j "data") with
    | some c => return ok (controlBlockJ c)
    | none => return err "invalidControlBlock"),
  ("tap.leafHash", fun j => do
    return ok (hexJ (Tx.Taproot.leafHash (← nat j "version").toUInt8 ⟨← bytes j "script"⟩))),
  ("tap.branchHash", fun j => do return ok (hexJ (Tx.Taproot.branchHash (← bytes j "a") (← bytes j "b")))),
  ("tap.outputKey", fun j => do
    let key ← bytes j "internalKey"
    match Tx.Taproot.tweakedOutputKey key (← optBytes j "merkleRoot") with
    | some (q, parity) => return ok (Json.mkObj [("key", hexJ q), ("parity", toJson parity)])
    | none => return err (if key.size != 32 then "invalidInternalKey" else "tweakFailed"))
]

/-! ## Addresses, sighash, builder, funding sources -/

def network (j : Json) : Except String Tx.BitcoinNetwork := do
  match Tx.BitcoinNetwork.ofString? (← str j "network") with
  | some n => pure n
  | none => throw "network"

def spentOf (j : Json) : Except String SighashBIP341.SpentOutput := do
  pure { amount := ← i64 j "amount", scriptPubKey := ← bytes j "scriptPubKey" }

def outputOf (j : Json) : Except String Transaction.Output := do
  pure { value := ← i64 j "value", scriptPubKey := ← bytes j "scriptPubKey" }

def paymentOf (j : Json) : Except String Payment := do
  pure { amount := ← i64 j "amount", scriptPubKey := ← bytes j "scriptPubKey" }

def addressOps : List (String × Handler) := [
  ("address.hrp", fun j => do return ok (Json.str (AddressDecoder.hrp (← network j)))),
  ("address.scriptPubKey", fun j => do
    match AddressDecoder.scriptPubKey (← str j "address") (← network j) with
    | .ok s => return ok (hexJ s)
    | .error e => return err e.name),
  ("address.fromScript", fun j => do
    return ok (optJ Json.str (AddressDecoder.address (← bytes j "script") (← network j)))),
  ("address.isP2TR", fun j => do return ok (toJson (AddressDecoder.isP2TR (← bytes j "script")))),
  ("payment.address", fun j => do
    match Payment.ofAddress (← i64 j "amount") (← str j "address") (← network j) with
    | .ok p => return ok (Json.mkObj [("amount", i64J p.amount), ("scriptPubKey", hexJ p.scriptPubKey)])
    | .error e => return err e.name)
]

def sighashOps : List (String × Handler) := [
  ("sighash.hashType", fun j => do
    let h : SighashBIP341.HashType := ⟨(← nat j "raw").toUInt8⟩
    return ok (Json.mkObj [("isValid", toJson h.isValid), ("isAnyoneCanPay", toJson h.isAnyoneCanPay),
      ("baseType", natJ h.baseType.toNat), ("commitsToAllOutputs", toJson h.commitsToAllOutputs),
      ("anyoneCanPay", natJ h.anyoneCanPay.rawValue.toNat)])),
  ("sighash.common", fun j => do
    match SighashBIP341.commonHashes (← txOfJson (← j.getObjVal? "tx")) (← (← arr j "spent").mapM spentOf) with
    | .ok c => return ok (Json.mkObj [("prevouts", hexJ c.prevouts), ("amounts", hexJ c.amounts),
        ("scriptPubKeys", hexJ c.scriptPubKeys), ("sequences", hexJ c.sequences), ("outputs", hexJ c.outputs)])
    | .error e => return err e.name),
  ("sighash.message", fun j => do
    let tx ← txOfJson (← j.getObjVal? "tx")
    let spent ← (← arr j "spent").mapM spentOf
    let hashType : SighashBIP341.HashType := ⟨(← nat j "hashType").toUInt8⟩
    let scriptPath : Option SighashBIP341.ScriptPath ← match opt j "scriptPath", opt j "leafScript" with
      | some sp, _ => pure (some { tapleafHash := ← bytes sp "tapleafHash", keyVersion := (← nat sp "keyVersion").toUInt8,
                                   codeseparatorPosition := (← nat sp "codeseparatorPosition").toUInt32 })
      | none, some _ => do
        let v := match opt j "leafVersion" with | some v => (v.getNat?.toOption.getD 0xC0).toUInt8 | none => 0xC0
        pure (some (SighashBIP341.ScriptPath.ofLeaf ⟨← bytes j "leafScript"⟩ v))
      | none, none => pure none
    let annex ← optBytes j "annex"
    let idx ← int j "inputIndex"
    match SighashBIP341.signatureMessage tx idx spent hashType scriptPath annex,
          SighashBIP341.sighash tx idx spent hashType scriptPath annex with
    | .ok m, .ok h => return ok (Json.mkObj [("message", hexJ m), ("sighash", hexJ h)])
    | .error e, _ => return err e.name
    | _, .error e => return err e.name)
]

def builderOps : List (String × Handler) := [
  ("builder.locktime", fun j => do
    let draws ← (← arr j "draws").mapM fun d => do
      match (← d.getStr?).toNat? with | some n => pure (Float.ofBits n.toUInt64) | none => throw "draw"
    return ok (natJ (TransactionBuilder.antiFeeSnipingLocktime (← nat j "tip").toUInt32 draws[0]! draws[1]!).toNat)),
  ("builder.build", fun j => do
    let inputs ← (← arr j "inputs").mapM fun i => do pure (⟨← bytes i "txid", (← nat i "vout").toUInt32⟩ : Transaction.Outpoint)
    let payments ← (← arr j "payments").mapM paymentOf
    let change ← match opt j "change" with | some c => some <$> paymentOf c | none => pure none
    let changePosition ← match opt j "changePosition" with | some p => some <$> p.getInt? | none => pure none
    let sequence := match opt j "sequence" with
      | some s => (s.getNat?.toOption.getD 0).toUInt32 | none => TransactionBuilder.defaultSequence
    let locktime := match opt j "locktime" with | some s => (s.getNat?.toOption.getD 0).toUInt32 | none => 0
    match TransactionBuilder.build inputs payments change changePosition id sequence locktime with
    | .ok tx => return ok (Json.mkObj [("info", txInfo tx), ("vsize", natJ (TransactionBuilder.vsize tx))])
    | .error e => return err e.name),
  ("builder.signedVSize", fun j => do
    let w := match opt j "witnessBytesPerInput" with | some v => v.getInt?.toOption.getD 66 | none => 66
    return ok (intJ (TransactionBuilder.signedVSize (← nat j "inputCount") (← (← arr j "outputs").mapM outputOf) w))),
  ("builder.vsize", fun j => do return ok (natJ (TransactionBuilder.vsize (← txOfJson (← j.getObjVal? "tx"))))),
  ("builder.compactSizeLength", fun j => do return ok (natJ (TransactionBuilder.compactSizeLength (← u64 j "value"))))
]

def fundingOps : List (String × Handler) := [
  ("funding.sources", fun j => do
    let tx ← txOfJson (← j.getObjVal? "tx")
    let srcs := (FundingSources.sources tx).map fun s => Json.mkObj [("inputIndex", natJ s.inputIndex),
      ("revelation", Json.str s.revelation.name), ("scriptPubKey", optJ hexJ s.scriptPubKey)]
    return ok (Json.mkObj [("sources", Json.arr srcs), ("fundingScripts", hexArr (FundingSources.fundingScripts tx))]))
]

/-! ## PSBT -/

def pairsJ (ps : Array PSBT.KeyValue) : Json := Json.arr (ps.map fun p => Json.arr #[hexJ p.key, hexJ p.value])

def pairsOf (j : Json) : Except String (Array PSBT.KeyValue) := do
  (← j.getArr?).mapM fun p => do
    let a ← p.getArr?
    pure ⟨← hexOf a[0]!, ← hexOf a[1]!⟩

def originsJ (os : Array (ByteArray × PSBT.KeyOrigin)) : Json := Json.arr (os.map fun (k, o) => Json.mkObj [
  ("key", hexJ k), ("leafHashes", hexArr o.leafHashes), ("fingerprint", natJ o.masterFingerprint.toNat),
  ("path", Json.arr (o.path.map (natJ ·.toNat)))])

def psbtInputJ (i : PSBT.Input) : Json := Json.mkObj [
  ("previousTxid", optJ hexJ i.previousTxid), ("outputIndex", optJ (natJ ·.toNat) i.outputIndex),
  ("sequence", optJ (natJ ·.toNat) i.sequence), ("sighashType", optJ (natJ ·.toNat) i.sighashType),
  ("witnessUTXO", optJ (fun (o : SighashBIP341.SpentOutput) => Json.mkObj [("amount", i64J o.amount),
    ("scriptPubKey", hexJ o.scriptPubKey)]) i.witnessUTXO),
  ("tapInternalKey", optJ hexJ i.tapInternalKey), ("tapKeySignature", optJ hexJ i.tapKeySignature),
  ("tapBIP32Derivation", originsJ i.tapBIP32Derivation),
  ("finalScriptWitness", optJ hexArr i.finalScriptWitness),
  ("tapLeafScripts", Json.arr (i.tapLeafScripts.map fun l => Json.mkObj [("controlBlock", controlBlockJ l.controlBlock),
    ("script", hexJ l.script), ("leafVersion", natJ l.leafVersion.toNat), ("leafHash", hexJ l.leafHash)])),
  ("tapScriptSignatures", Json.arr (i.tapScriptSignatures.map fun (id, sig) => Json.mkObj [
    ("publicKey", hexJ id.publicKey), ("leafHash", hexJ id.leafHash), ("signature", hexJ sig)]))]

def psbtOutputJ (o : PSBT.Output) : Json := Json.mkObj [
  ("amount", optJ i64J o.amount), ("script", optJ hexJ o.script), ("tapInternalKey", optJ hexJ o.tapInternalKey),
  ("tapBIP32Derivation", originsJ o.tapBIP32Derivation),
  ("tapTree", optJ (fun (ts : Array (UInt8 × UInt8 × ByteArray)) => Json.arr (ts.map fun (d, l, s) => Json.mkObj [
    ("depth", natJ d.toNat), ("leafVersion", natJ l.toNat), ("script", hexJ s)])) o.tapTree)]

def psbtJ (p : PSBT) : Json := Json.mkObj [
  ("globals", pairsJ p.globals), ("inputs", Json.arr (p.inputs.map (pairsJ ·.pairs))),
  ("outputs", Json.arr (p.outputs.map (pairsJ ·.pairs))),
  ("version", optJ (natJ ·.toNat) p.version), ("txVersion", intJ p.txVersion.toInt),
  ("fallbackLocktime", natJ p.fallbackLocktime.toNat),
  ("in", Json.arr (p.inputs.map psbtInputJ)), ("out", Json.arr (p.outputs.map psbtOutputJ)),
  ("serialized", hexJ p.serialized), ("base64", Json.str p.base64),
  ("v0", match p.base64V0 with | .ok s => Json.mkObj [("ok", Json.str s)] | .error e => err e.name),
  ("unsigned", match p.unsignedTransaction with | .ok tx => ok (txInfo tx) | .error e => err e.name)]

def originsOf (v : Json) : Except String (Array (ByteArray × PSBT.KeyOrigin)) := do
  (← v.getArr?).mapM fun o => do
    pure (← bytes o "key", { leafHashes := ← bytesArr o "leafHashes", masterFingerprint := (← nat o "fingerprint").toUInt32,
                             path := ← (← arr o "path").mapM fun n => do pure (← n.getNat?).toUInt32 })

def optField {α} (v : Json) (f : Json → Except String α) : Except String (Option α) :=
  match v with | .null => pure none | v => some <$> f v

def editInput (i : PSBT.Input) (field : String) (v : Json) : Except String PSBT.Input := do
  let u32 (x : Json) : Except String UInt32 := do pure (← x.getNat?).toUInt32
  match field with
  | "previousTxid" => return i.setPreviousTxid (← optField v hexOf)
  | "outputIndex" => return i.setOutputIndex (← optField v u32)
  | "sequence" => return i.setSequence (← optField v u32)
  | "sighashType" => return i.setSighashType (← optField v u32)
  | "witnessUTXO" => return i.setWitnessUTXO (← optField v spentOf)
  | "tapInternalKey" => return i.setTapInternalKey (← optField v hexOf)
  | "tapKeySignature" => return i.setTapKeySignature (← optField v hexOf)
  | "tapBIP32Derivation" => return i.setTapBIP32Derivation (← originsOf v)
  | "finalScriptWitness" => return i.setFinalScriptWitness (← optField v fun x => do (← x.getArr?).mapM hexOf)
  | "tapLeafScripts" => return i.setTapLeafScripts (← (← v.getArr?).mapM fun l => do
      let c ← l.getObjVal? "controlBlock"
      pure { controlBlock := { leafVersion := (← nat c "leafVersion").toUInt8, outputKeyParity := ← bool c "parity",
                               internalKey := ← bytes c "internalKey", path := ← bytesArr c "path" },
             script := ← bytes l "script", leafVersion := (← nat l "leafVersion").toUInt8 })
  | "tapScriptSignatures" => return i.setTapScriptSignatures (← (← v.getArr?).mapM fun s => do
      pure (({ publicKey := ← bytes s "publicKey", leafHash := ← bytes s "leafHash" } : PSBT.TapScriptSignatureID),
            ← bytes s "signature"))
  | other => throw s!"input field {other}"

def editOutput (o : PSBT.Output) (field : String) (v : Json) : Except String PSBT.Output := do
  match field with
  | "amount" => return o.setAmount (← optField v fun x => do
      match (← x.getStr?).toInt? with | some n => pure (Int64.ofInt n) | none => throw "amount")
  | "script" => return o.setScript (← optField v hexOf)
  | "tapInternalKey" => return o.setTapInternalKey (← optField v hexOf)
  | "tapBIP32Derivation" => return o.setTapBIP32Derivation (← originsOf v)
  | "tapTree" => return o.setTapTree (← optField v fun x => do (← x.getArr?).mapM fun t => do
      pure ((← nat t "depth").toUInt8, (← nat t "leafVersion").toUInt8, ← bytes t "script"))
  | other => throw s!"output field {other}"

def psbtOps : List (String × Handler) := [
  ("psbt.parse", fun j => do
    match PSBT.parse (← bytes j "data") with
    | .ok p => return ok (psbtJ p)
    | .error e => return err e.name),
  ("psbt.base64", fun j => do
    match PSBT.ofBase64 (← str j "text") with
    | .ok p => return ok (psbtJ p)
    | .error e => return err e.name),
  ("psbt.edit", fun j => do
    let globals ← pairsOf (← j.getObjVal? "globals")
    let inputs ← (← arr j "inputs").mapM fun i => do pure (⟨← pairsOf i⟩ : PSBT.Input)
    let outputs ← (← arr j "outputs").mapM fun o => do pure (⟨← pairsOf o⟩ : PSBT.Output)
    let mut p : PSBT := { globals, inputs, outputs }
    for e in ← arr j "edits" do
      let k ← nat e "index"
      let field ← str e "field"
      let v := (e.getObjVal? "value").toOption.getD .null
      if (← str e "scope") == "in" then
        p := { p with inputs := p.inputs.set! k (← editInput p.inputs[k]! field v) }
      else
        p := { p with outputs := p.outputs.set! k (← editOutput p.outputs[k]! field v) }
    return ok (psbtJ p))
]

def txOps : List (String × Handler) := wireOps ++ transactionOps ++ scriptOps ++ addressOps ++ sighashOps ++
  builderOps ++ fundingOps ++ psbtOps

end Oracle
