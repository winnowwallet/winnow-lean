import Oracle.Base
import Winnow.Wallet

/-! Oracle ops for the Wallet area (Lean side of LeanOracle/Wallet). Doubles cross as JSON numbers
printed with 17 significant digits by both sides (`fmtF`). -/

namespace Oracle
open Lean Winnow

/-- A Float as a decimal string both sides print identically (shortest round-trip form is not available
in Lean, so both use `%.17g`-style output: Lean `Float.toString` gives that). -/
def fmtF (f : Float) : Json := Json.str (toString f)

def floats (j : Json) (k : String) : Except String (Array Float) := do
  let arr ← j.getObjValAs? (Array String) k
  arr.mapM fun s => match s.toNat? with
    | some n => pure n.toFloat
    | none => throw s!"{k}: integer milli-sat/vB strings expected"

/-! ## Shared request plumbing -/

def field (j : Json) (k : String) : Json := (j.getObjVal? k).toOption.getD Json.null

def hxJ (v : Json) : Except String ByteArray := do
  let .str s := v | throw "hex"
  match ofHex? s with | some b => pure b | none => throw "hex"

def i64J (v : Json) : Except String Int64 := do
  let .str s := v | throw "int64"
  match s.toInt? with | some n => pure (Int64.ofInt n) | none => throw "int64"

def optI64J (v : Json) : Except String (Option Int64) :=
  match v with | .null => pure none | v => some <$> i64J v

/-- Doubles cross as IEEE-754 bit patterns (hex). -/
def dblJ (v : Json) : Except String Float := do
  let .str s := v | throw "double bits"
  let mut n : Nat := 0
  for c in s.toList do
    let some d := SwiftJSON.hexVal c | throw "double bits"
    n := n * 16 + d
  return Float.ofBits n.toUInt64

def bitsJ (f : Float) : Json := Json.str (String.ofList (Nat.toDigits 16 f.toBits.toNat))

def txJ (v : Json) : Except String Transaction := do
  (Transaction.decode (← hxJ v)).mapError (·.name)

def optJ {α} (f : α → Json) : Option α → Json | some a => f a | none => Json.null

/-- A Lean failure carrying a Swift error name becomes that error reply. -/
def orErr (r : Except String Json) : Except String Json :=
  match r with | .ok v => pure v | .error e => pure (err e)

def jsonText (j : Json) : Except String String := str j "json"

def utxoInfo (u : WalletUTXO) : Json :=
  Json.mkObj [("json", Json.str (SwiftJSON.write u.toJV)), ("outpoint", Json.str (hex u.outpoint.txid ++ ":" ++ toString u.outpoint.vout)),
    ("spentAmount", Json.str (toString u.spentOutput.amount.toInt)), ("spentScript", hexJ u.spentOutput.scriptPubKey),
    ("isSpent", Json.bool u.isSpent)]

def coinJ (v : Json) : Except String WalletUTXO := do
  return { txid := ← hxJ (field v "txid"), vout := (← i64J (field v "vout")).toInt.toNat.toUInt32, amount := ← i64J (field v "amount"),
           scriptPubKey := ← hxJ (field v "script"), chain := .receive, index := 0, height := 0 }

def paymentJ (v : Json) : Except String Payment := do
  return { amount := ← i64J (field v "amount"), scriptPubKey := ← hxJ (field v "script") }

def listJ {α} (f : Json → Except String α) (v : Json) : Except String (Array α) :=
  match v with | .arr xs => xs.mapM f | .null => pure #[] | _ => throw "array"

/-- Ops that touch the file system run outside `Except`; they are answered before the pure table. -/
def walletIOOps : List (String × (Json → IO Json)) := [
  ("export.write", fun j => do
    let tmp := (← IO.getEnv "TMPDIR").getD "/tmp"
    let staging ← ExportStagingFile.new tmp
    let some contents := (str j "contents").toOption | return err "bad-request: contents"
    let some name := (str j "name").toOption | return err "bad-request: name"
    let first ← if (j.getObjValAs? Bool "twice").toOption == some true then some <$> staging.write "first" "first.json" else pure none
    let url ← staging.write contents name
    let dir := url.parent.getD tmp
    let back ← IO.FS.readFile url
    let firstGone ← match first with
      | some f => do pure !(← (f.parent.getD tmp).pathExists)
      | none => pure true
    staging.remove
    return ok (Json.mkObj [("name", Json.str (url.fileName.getD "")), ("contents", Json.str back),
      ("prefixed", Json.bool ((dir.fileName.getD "").startsWith ExportStagingFile.prefix_)),
      ("previousRemoved", Json.bool firstGone), ("removed", Json.bool !(← dir.pathExists)),
      ("url", optJ (fun (p : System.FilePath) => Json.str p.toString) (← staging.url.get))])),
  ("export.sweep", fun j => do
    let tmp := (← IO.getEnv "TMPDIR").getD "/tmp"
    let root := System.FilePath.mk tmp / s!"winnow-sweep-test-{← ExportStagingFile.uuidString}"
    IO.FS.createDirAll root
    let entries := match j.getObjVal? "entries" with | .ok (.arr xs) => xs | _ => #[]
    for e in entries do
      let some name := (str e "name").toOption | return err "bad-request: name"
      if (e.getObjValAs? Bool "dir").toOption == some true then
        IO.FS.createDirAll (root / name)
        IO.FS.writeFile (root / name / "wallet.json") "x"
      else IO.FS.writeFile (root / name) "x"
    ExportStagingFile.sweep root
    let left := ((← root.readDir).map (·.fileName)).toList.mergeSort (fun a b => !(b < a))
    IO.FS.removeDirAll root
    return ok (Json.arr (left.map Json.str).toArray))
]

partial def treeJ : Keys.Taproot.Tree → Json
  | .leaf v sc => Json.mkObj [("v", Json.num v.toNat), ("s", hexJ sc)]
  | .branch a b => Json.arr #[treeJ a, treeJ b]

def descJ (j : Json) : Except String (Except String Descriptor) := do
  return (Descriptor.parse (← str j "s")).mapError (·.name)

def topKey (d : Descriptor) : Descriptor.SingleKey :=
  d.key

/-- Run a refusable computation: its error name becomes the reply. -/
def answerE (r : Except String Json) : Json := match r with | .ok v => ok v | .error e => err e

def spentListJ (v : Json) : Except String (Array SighashBIP341.SpentOutput) :=
  listJ (fun o => do return { amount := ← i64J (field o "amount"), scriptPubKey := ← hxJ (field o "script") }) v

def hashTypeJ (j : Json) : SighashBIP341.HashType := ⟨((j.getObjValAs? Nat "hashType").toOption.getD 0).toUInt8⟩

def pairsJ (v : Json) : Except String (Array (ByteArray × ByteArray)) :=
  listJ (fun kv => do
    let .arr #[a, b] := kv | throw "pair"
    return (← hxJ a, ← hxJ b)) v

def taprootKeyJ (v : Json) : Except String (Option PSBT.TaprootKey) := do
  match v with
  | .obj _ =>
    let path ← listJ (fun x => do return (← x.getNat?).toUInt32) (field v "path")
    return some { internalKey := ← hxJ (field v "internalKey"), masterFingerprint := (← i64J (field v "fp")).toInt.toNat.toUInt32, path }
  | _ => return none

def editPairs (pairs : Array PSBT.KeyValue) (e : Json) : Except String (Array PSBT.KeyValue) := do
  let key ← hxJ (field e "key")
  let ps := pairs.filter (·.key != key)
  let ps ← match field e "value" with
    | .str _ => do pure (ps.push ⟨key, ← hxJ (field e "value")⟩)
    | _ => pure ps
  return PSBT.sortPairs ps

structure FlowState where
  psbt : PSBT
  saved : Array PSBT := #[]

/-- One role; `.error (.inl badRequest)` for a malformed step, `.error (.inr name)` for a refusal (with the
extra fields of the reply so far). -/
def flowStep (st : Json) (s : FlowState) : Except String (Except (String × List (String × Json)) (FlowState × List (String × Json))) := do
  let role ← str st "role"
  let index : Int := (st.getObjValAs? Int "index").toOption.getD 0
  let refuse {α} (r : PSBT.RM α) : Except String (Except (String × List (String × Json)) α) :=
    pure (r.mapError fun e => (e.name, []))
  let done (p : PSBT) (o : List (String × Json) := []) : Except String (Except (String × List (String × Json)) (FlowState × List (String × Json))) :=
    pure (.ok ({ s with psbt := p }, o))
  let p := s.psbt
  match role with
  | "signKeyPath" =>
    match ← refuse (p.signKeyPath index (← hxJ (field st "key")) (← hxJ (field st "aux"))) with
    | .ok q => done q | .error e => pure (.error e)
  | "attachScriptPath" =>
    let some cb := Tx.Taproot.ControlBlock.parse? (← hxJ (field st "controlBlock")) | return .error ("invalidControlBlock", [])
    let origins ← listJ (fun o => do
      let path ← listJ (fun x => do return (← x.getNat?).toUInt32) (field o "path")
      return (← hxJ (field o "key"), ({ masterFingerprint := (← i64J (field o "fp")).toInt.toNat.toUInt32, path } : PSBT.KeyOrigin)))
      (field st "origins")
    let version := ((st.getObjValAs? Nat "leafVersion").toOption.getD 0xC0).toUInt8
    match ← refuse (p.attachScriptPath index cb ⟨← hxJ (field st "script")⟩ version origins) with
    | .ok q => done q | .error e => pure (.error e)
  | "signScriptPath" =>
    match ← refuse (p.signScriptPath index (← listJ hxJ (field st "keys")) (← hxJ (field st "aux"))) with
    | .ok q => done q | .error e => pure (.error e)
  | "save" => pure (.ok ({ s with saved := s.saved.push p }, []))
  | "restore" => done (s.saved[(st.getObjValAs? Nat "n").toOption.getD 0]!)
  | "combine" =>
    let ns ← listJ (fun x => x.getNat?) (field st "with")
    match ← refuse (p.combined (ns.map (s.saved[·]!))) with
    | .ok q => done q | .error e => pure (.error e)
  | "finalize" =>
    match ← refuse p.finalize with
    | .ok q => done q | .error e => pure (.error e)
  | "extract" =>
    match ← refuse p.extractedTransaction with
    | .ok tx => done p [("tx", hexJ (tx.serialized true))]
    | .error e => pure (.error e)
  | "verifiedSigners" =>
    let r : PSBT.RM (Array ByteArray) := do
      -- The leaf named by `leafHash`, else the input's first leaf (the pre-1cf93fb single-leaf call).
      let first := ((p.inputs[index.toNat]?.bind (·.tapLeafScripts[0]?)).map (·.leafHash)).getD .empty
      let leafHash := ((st.getObjValAs? String "leafHash").toOption.bind Wire.dataOfHex?).getD first
      p.verifiedScriptPathSigners index leafHash (← PSBT.liftP p.unsignedTransaction) (← PSBT.liftP p.spentOutputs)
    match r with
    | .ok xs => done p [("signers", Json.arr ((sortBytes id xs).map hexJ))]
    | .error e => pure (.error (e.name, []))
  | "spentOutputs" =>
    match p.spentOutputs with
    | .ok xs => done p [("spent", Json.arr (xs.map fun o => Json.mkObj [("amount", Json.str (toString o.amount.toInt)), ("script", hexJ o.scriptPubKey)]))]
    | .error e => pure (.error (e.name, []))
  | "editInput" =>
    let k := index.toNat
    let ps ← editPairs p.inputs[k]!.pairs st
    done { p with inputs := p.inputs.set! k ⟨ps⟩ }
  | "editOutput" =>
    let k := index.toNat
    let ps ← editPairs p.outputs[k]!.pairs st
    done { p with outputs := p.outputs.set! k ⟨ps⟩ }
  | "editGlobal" => done { p with globals := ← editPairs p.globals st }
  | _ => throw s!"role {role}"

def runFlow (j : Json) : Except String Json := do
  let start : Except String (Except String PSBT) := do
    match field j "create" with
    | .obj _ =>
      let c := field j "create"
      let inputs ← listJ (fun i => do
        return ({ spentOutput := { amount := ← i64J (field i "amount"), scriptPubKey := ← hxJ (field i "script") },
                  key := ← taprootKeyJ (field i "key") } : PSBT.InputInfo)) (field c "inputs")
      let outputs ← listJ (fun o => do return ({ key := ← taprootKeyJ o } : PSBT.OutputInfo)) (field c "outputs")
      let tx ← txJ (field c "tx")
      return (PSBT.create tx inputs outputs).mapError (·.name)
    | _ => return (PSBT.parse (← hxJ (field j "psbt"))).mapError (·.name)
  let p ← match ← start with
    | .ok p => pure p
    | .error e => return ok (Json.arr #[Json.mkObj [("error", Json.str e)]])
  let mut out : Array Json := #[Json.mkObj [("psbt", hexJ p.serialized)]]
  let mut s : FlowState := { psbt := p }
  let steps := match field j "steps" with | .arr xs => xs | _ => #[]
  for st in steps do
    match ← flowStep st s with
    | .ok (s', extra) =>
      s := s'
      out := out.push (Json.mkObj (extra ++ [("psbt", hexJ s.psbt.serialized)]))
    | .error (e, extra) =>
      out := out.push (Json.mkObj (extra ++ [("error", Json.str e)]))
      break
  return ok (Json.arr out)

def walletOps : List (String × Handler) := [
  ("psbt.flow", runFlow),
  ("signer.witness", fun j => do
    let r := Signer.witness (← txJ (field j "tx")) (← j.getObjValAs? Int "index") (← spentListJ (field j "spent"))
      (← bytes j "key") (hashTypeJ j) (← bytes j "aux")
    return answerE (r.mapError (·.name) |>.map fun w => Json.arr (w.map hexJ))),
  ("signer.sign", fun j => do
    let keys ← pairsJ (field j "keys")
    let lookup (script : ByteArray) : Option ByteArray :=
      -- a dictionary: the last entry per key wins
      (keys.reverse.find? (·.1 == script)).map (·.2)
    let r := Signer.sign (← txJ (field j "tx")) (← spentListJ (field j "spent")) (hashTypeJ j) (← bytes j "aux") lookup
    return answerE (r.mapError (·.name) |>.map fun tx => hexJ (tx.serialized true))),
  ("signer.scriptPathSignature", fun j => do
    let annex ← match field j "annex" with | .str _ => some <$> bytes j "annex" | _ => pure none
    let r := Signer.scriptPathSignature (← txJ (field j "tx")) (← j.getObjValAs? Int "index") (← spentListJ (field j "spent"))
      ⟨← bytes j "script"⟩ (← nat j "leafVersion").toUInt8 (hashTypeJ j) annex (← bytes j "key") (← bytes j "aux")
    return answerE (r.mapError (·.name) |>.map hexJ)),
  ("signer.multisigWitness", fun j => do
    let sigs ← pairsJ (field j "signatures")
    let sigs := sigs.foldl (fun acc (k, v) => (acc.filter (·.1 != k)).push (k, v)) #[]
    let some cb := Tx.Taproot.ControlBlock.parse? (← bytes j "controlBlock") | return err "invalidControlBlock"
    let r := Signer.multisigWitness sigs ⟨← bytes j "script"⟩ cb
    return answerE (r.mapError (·.name) |>.map fun w => Json.arr (w.map hexJ))),
  ("desc.parse", fun j => do
    let d? ← descJ j
    return answerE do
      let d ← d?
      return Json.mkObj [("serialized", Json.str d.serialized), ("isRanged", Json.bool d.isRanged)]),
  ("desc.derive", fun j => do
    let d? ← descJ j
    let index := (← nat j "index").toUInt32
    let net? : Except String (Option Tx.BitcoinNetwork) := match str j "keyNetwork" with
      | .ok _ => pure none
      | .error _ => do
        let some n := Tx.BitcoinNetwork.ofString? (← str j "network") | throw "network"
        pure (some n)
    let net ← net?
    let kn : Keys.HDKey.Network := if (str j "keyNetwork").toOption == some "mainnet" then .mainnet else .testnet
    return answerE do
      let d ← d?
      let r : Descriptor.DM (Array Descriptor.DerivedOutput) := match net with
        | some n => d.derived index n
        | none => d.derivedForKeyNetwork index kn
      let outs ← r.mapError DescriptorFailure.name
      return Json.arr (outs.map fun (o : Descriptor.DerivedOutput) => Json.mkObj [("spk", hexJ o.scriptPubKey), ("address", Json.str o.address)])),
  ("desc.resolvedTaproot", fun j => do
    let d? ← descJ j
    let index := (← nat j "index").toUInt32
    let choice ← nat j "choice"
    return answerE do
      let d ← d?
      let (k, t) ← (d.resolvedTaproot index choice).mapError (·.name)
      return Json.mkObj [("internalKey", hexJ k), ("tree", treeJ t)]),
  ("desc.publicKey", fun j => do
    let d? ← descJ j
    let index := (← nat j "index").toUInt32
    let choice ← nat j "choice"
    return answerE do
      let d ← d?
      return hexJ (← (Descriptor.publicKey (topKey d) index choice).mapError (·.name))),
  ("desc.networkHrp", fun j => do
    return ok (Json.str (if (← str j "network") == "mainnet" then Keys.HDKey.Network.mainnet else .testnet).hrp)),
  ("desc.checksum", fun j => do
    let body ← str j "body"
    let mut o := [("create", Json.str (Descriptor.Checksum.create body))]
    if let .ok c := str j "checksum" then o := o ++ [("verify", Json.bool (Descriptor.Checksum.verify body c))]
    return ok (Json.mkObj o)),
  ("coin.dust", fun j => do
    let script ← bytes j "script"
    match str j "relay" with
    | .ok relay =>
      let some n := relay.toInt? | throw "relay"
      return ok (Json.str (toString (CoinSelection.dustThreshold script (Int64.ofInt n))))
    | .error _ => return ok (Json.str (toString (CoinSelection.dustThreshold script)))),
  ("coin.select", fun j => do
    let utxos ← listJ coinJ (field j "utxos")
    let payments ← listJ paymentJ (field j "payments")
    let change ← bytes j "change"
    let rate ← dblJ (field j "rate")
    let w : Int := (j.getObjValAs? Int "witness").toOption.getD 66
    match CoinSelection.select utxos payments change rate w with
    | .error e => return err e.name
    | .ok s => return ok (Json.mkObj [("selected", Json.arr (s.selected.map fun u => Json.str (hex u.txid ++ ":" ++ toString u.vout))),
        ("fee", Json.str (toString s.fee.toInt)), ("change", optJ (fun (c : Int64) => Json.str (toString c.toInt)) s.changeAmount)])),
  ("coinError.describe", fun j => do
    let a := fun (_ : Unit) => i64J (field j "a")
    let b := fun (_ : Unit) => i64J (field j "b")
    let e : CoinSelectionError ← match ← str j "case" with
      | "noUTXOs" => pure .noUTXOs
      | "insufficientFunds" => pure (.insufficientFunds (← a ()) (← b ()))
      | "invalidFeeRate" => pure (.invalidFeeRate (← dblJ (field j "x")))
      | "dustOutput" => pure (.dustOutput (← a ()) (← b ()))
      | "transactionTooLarge" => pure (.transactionTooLarge (← a ()).toInt (← b ()).toInt)
      | "invalidAmount" => pure (.invalidAmount (← a ()))
      | "duplicateUTXO" => pure .duplicateUTXO
      | "invalidOutpoint" => pure .invalidOutpoint
      | "emptyScript" => pure .emptyScript
      | "invalidWitnessSize" => pure (.invalidWitnessSize (← a ()).toInt)
      | "amountOverflow" => pure .amountOverflow
      | _ => throw "case"
    return ok (Json.mkObj [("name", Json.str e.name), ("text", Json.str e.description)])),
  ("export.safeFileName", fun j => do return ok (Json.str (ExportStagingFile.safeFileName (← str j "name")))),
  ("double.format", fun j => do
    let d ← dblJ (field j "bits")
    let mut o : List (String × Json) := [("description", Json.str (SwiftDouble.description d)),
      ("formatted", Json.str (SwiftDouble.formatted2 d))]
    if d.isFinite then o := o ++ [("json", Json.str ("[" ++ SwiftDouble.jsonText d ++ "]"))]
    if let .ok t := str j "text" then
      let parsed := SwiftJSON.decodeText ("[" ++ t ++ "]") (SwiftJSON.asArray SwiftJSON.asDouble)
      o := o ++ [("parsed", match parsed with | .ok #[x] => bitsJ x | _ => Json.null)]
    return ok (Json.mkObj o)),
  ("utxo.decode", fun j => do
    let t ← jsonText j
    orErr do
      let u ← SwiftJSON.decodeText t WalletUTXO.ofJV
      return ok (utxoInfo u)),
  ("history.decode", fun j => do
    let t ← jsonText j
    orErr do
      let h ← SwiftJSON.decodeText t HistoryEntry.ofJV
      let tx ← h.transaction
      return ok (Json.mkObj [("json", Json.str (SwiftJSON.write h.toJV)), ("tx", optJ (fun (t : Transaction) => hexJ t.txid) tx)])),
  ("pending.decode", fun j => do
    let t ← jsonText j
    orErr do
      let p ← SwiftJSON.decodeText t PendingSend.ofJV
      let txid := (Transaction.decode p.rawTransaction).toOption.map (·.txid)
      return ok (Json.mkObj [("json", Json.str (SwiftJSON.write p.toJV)), ("txid", optJ hexJ txid)])),
  ("state.decode", fun j => do
    let t ← jsonText j
    orErr do
      let s ← WalletState.decode t
      let bal := s.utxos.foldl (fun a u => a + u.amount.toInt) 0
      return ok (Json.mkObj [("json", Json.str (← s.encode)), ("live", Json.num s.utxos.size),
        ("balance", Json.str (toString bal))])),
  ("walletError.describe", fun j => do
    let e : WalletError ← match ← str j "case" with
      | "invalidDescriptor" => pure (.invalidDescriptor (← str j "s"))
      | "descriptorMismatch" => pure .descriptorMismatch
      | "invalidBundle" => pure (.invalidBundle (← str j "s"))
      | "noPayments" => pure .noPayments
      | "changeOutputMissing" => pure .changeOutputMissing
      | "transactionTooLarge" => pure (.transactionTooLarge (← j.getObjValAs? Int "a") (← j.getObjValAs? Int "b"))
      | "mnemonicUnavailable" => pure .mnemonicUnavailable
      | "exportWhilePending" => pure .exportWhilePending
      | "invalidTransactionAmounts" => pure .invalidTransactionAmounts
      | "unsupportedWalletData" => pure .unsupportedWalletData
      | "storageTooLarge" => pure (.storageTooLarge (← j.getObjValAs? Int "a"))
      | _ => throw "case"
    return ok (Json.mkObj [("name", Json.str e.name), ("text", Json.str e.description)])),
  ("feeBumpError.describe", fun j => do
    let e : FeeBumpError ← match ← str j "case" with
      | "transactionNotPending" => pure .transactionNotPending
      | "noChangeOutput" => pure .noChangeOutput
      | "changeAlreadySpent" => pure .changeAlreadySpent
      | "invalidFeeRate" => pure (.invalidFeeRate (← dblJ (field j "x")))
      | "feeRateNotHigher" => pure (.feeRateNotHigher (← dblJ (field j "x")) (← dblJ (field j "y")))
      | "insufficientChange" => pure (.insufficientChange (← i64J (field j "a")) (← i64J (field j "b")))
      | _ => throw "case"
    return ok (Json.mkObj [("name", Json.str e.name), ("text", Json.str e.description)])),
  ("feeBump.authorizes", fun j => do
    let preview : FeeBumpPreview :=
      { originalTxid := ← hxJ (field j "original"), currentFeeRateSatPerVByte := ← dblJ (field j "current"),
        feeRateSatPerVByte := ← dblJ (field j "rate"), fee := ← i64J (field j "fee"),
        changeAmount := ← optI64J (field j "change"), replacementTransaction := ← txJ (field j "reviewed") }
    let built : BuiltTransaction :=
      { psbt := { globals := #[], inputs := #[], outputs := #[] }, transaction := ← txJ (field j "built"),
        fee := ← i64J (field j "builtFee"), changeAmount := ← optI64J (field j "builtChange") }
    return ok (Json.bool (preview.authorizes built))),
  ("fee.resolve", fun j => do
    let some p := FeePolicy.Priority.ofString? (← str j "priority") | throw "priority"
    -- rates cross as integers in thousandths of a sat/vB, so both sides start from the same doubles
    let milli (k : String) : Except String (Option Float) := do
      match j.getObjVal? k with
      | .ok Json.null | .error _ => pure none
      | .ok v => match v.getNat? with
        | .ok n => pure (some (n.toFloat / 1000))
        | .error _ => throw k
    let observed := (← floats j "observed").map (· / 1000)
    let r := FeePolicy.resolve p (← milli "override") observed (← milli "floor")
    return ok (Json.str (toString (r * 1000).round.toUInt64.toNat)))
]

end Oracle
