import Std.Data.HashSet
import Winnow.Tx.Transaction
import Winnow.Tx.Taproot
import Winnow.Tx.SighashBIP341
import Winnow.Tx.Base64

/-! # PSBT: the BIP174 / BIP370 document

Port of `Sources/WalletCore/PSBT/PSBT.swift`: PSBTv2 in memory with BIP174 v0 import/export, generic
key-value maps kept in canonical key order, the typed field accessors (BIP370/371) and every validation
the parser applies. MuSig2's BIP373 fields are carried as unknown pairs, never interpreted (upstream
removed MuSig2).

Also `unsignedTransaction` from `PSBTRoles.swift`, which `base64V0` needs; the rest of PSBTRoles (signer,
finalizer) needs the Keys area and is not ported here. -/

namespace Winnow

inductive PSBTError where
  | invalidMagic
  | truncated
  | duplicateKey (key : ByteArray)
  | unsupportedVersion (version : UInt32)
  | missingField (field : String)
  | malformed (reason : String)
  | inconsistentCounts
  | conflict (key : ByteArray)
  /-- A `WireError` thrown through (the Swift original lets those propagate as they are). -/
  | wire (e : WireError)
  deriving Inhabited

def PSBTError.name : PSBTError → String
  | .invalidMagic => "invalidMagic" | .truncated => "truncated" | .duplicateKey _ => "duplicateKey"
  | .unsupportedVersion _ => "unsupportedVersion" | .missingField _ => "missingField"
  | .malformed _ => "malformed" | .inconsistentCounts => "inconsistentCounts" | .conflict _ => "conflict"
  | .wire e => e.name

namespace PSBT

def maxSerializedSize : Nat := 4_000_000
def maxBase64Length : Nat := 5_333_336
def maxMapKeySize : Nat := 10_000
def maxMapPairs : Nat := 10_000
def maxInputOutputCount : Nat := 100_000
def magic : ByteArray := ByteArray.mk #[0x70, 0x73, 0x62, 0x74, 0xFF]

namespace GlobalType
def unsignedTx : UInt8 := 0x00
def txVersion : UInt8 := 0x02
def fallbackLocktime : UInt8 := 0x03
def inputCount : UInt8 := 0x04
def outputCount : UInt8 := 0x05
def version : UInt8 := 0xFB
end GlobalType

namespace InType
def witnessUTXO : UInt8 := 0x01
def sighashType : UInt8 := 0x03
def finalScriptWitness : UInt8 := 0x08
def previousTxid : UInt8 := 0x0E
def outputIndex : UInt8 := 0x0F
def sequence : UInt8 := 0x10
def tapKeySignature : UInt8 := 0x13
def tapScriptSignature : UInt8 := 0x14
def tapLeafScript : UInt8 := 0x15
def tapBIP32Derivation : UInt8 := 0x16
def tapInternalKey : UInt8 := 0x17
end InType

namespace OutType
def amount : UInt8 := 0x03
def script : UInt8 := 0x04
def tapInternalKey : UInt8 := 0x05
def tapTree : UInt8 := 0x06
def tapBIP32Derivation : UInt8 := 0x07
end OutType

/-- A generic key-value pair; `key` is the type byte followed by any key data. -/
structure KeyValue where
  key : ByteArray
  value : ByteArray
  deriving Inhabited

instance : BEq KeyValue := ⟨fun a b => a.key == b.key && a.value == b.value⟩

namespace KeyValue
def make (type : UInt8) (keyData : ByteArray := .empty) (value : ByteArray) : KeyValue :=
  ⟨ByteArray.mk #[type] ++ keyData, value⟩
def type (p : KeyValue) : UInt8 := if p.key.size > 0 then p.key[0]! else 0
def keyData (p : KeyValue) : ByteArray := p.key.extract 1 p.key.size
end KeyValue

/-- Pairs in canonical (bytewise key) order. -/
def sortPairs (ps : Array KeyValue) : Array KeyValue := sortBytes (·.key) ps

/-- BIP32 key origin for a Taproot key (BIP371 derivation value). -/
structure KeyOrigin where
  leafHashes : Array ByteArray := #[]
  masterFingerprint : UInt32
  path : Array UInt32
  deriving Inhabited

structure TapScriptSignatureID where
  publicKey : ByteArray
  leafHash : ByteArray
  deriving Inhabited

structure TapLeafScript where
  controlBlock : Tx.Taproot.ControlBlock
  script : ByteArray
  leafVersion : UInt8
  deriving Inhabited

def TapLeafScript.leafHash (l : TapLeafScript) : ByteArray := Tx.Taproot.leafHash l.leafVersion ⟨l.script⟩

/-! ## Maps: shared pair plumbing of inputs and outputs -/

def findPair (pairs : Array KeyValue) (type : UInt8) (keyData : ByteArray := .empty) : Option KeyValue :=
  pairs.find? fun p => p.type == type && p.keyData == keyData

/-- Replace the pair with the same key, or insert it before the first key not below it. -/
def setPair (pairs : Array KeyValue) (pair : KeyValue) : Array KeyValue :=
  match pairs.findIdx? (·.key == pair.key) with
  | some i => pairs.set! i pair
  | none =>
    let pos := (pairs.findIdx? fun p => !bytesLt p.key pair.key).getD pairs.size
    pairs.insertIdxIfInBounds pos pair

def removePair (pairs : Array KeyValue) (type : UInt8) (keyData : ByteArray := .empty) : Array KeyValue :=
  pairs.filter fun p => !(p.type == type && p.keyData == keyData)

def removeType (pairs : Array KeyValue) (type : UInt8) : Array KeyValue := pairs.filter (·.type != type)

def u32Value? (v : ByteArray) : Option UInt32 := if v.size == 4 then some (readLE v 0 4).toUInt32 else none

/-- A dictionary as Swift builds it from distinct keys: the last value per key, ordered by key. -/
def dictSorted {α} (key : α → ByteArray) (xs : Array α) : Array α := Id.run do
  let mut out : Array α := #[]
  for x in xs do
    match out.findIdx? (key · == key x) with
    | some i => out := out.set! i x
    | none => out := out.push x
  return sortBytes key out

def readDerivations (pairs : Array KeyValue) (type : UInt8) : Array (ByteArray × KeyOrigin) := Id.run do
  let mut result : Array (ByteArray × KeyOrigin) := #[]
  for pair in pairs do
    if pair.type != type || pair.keyData.size != 32 then continue
    let r := ByteReader.init pair.value
    let parsed : ByteReader.M (Option KeyOrigin) := do
      let count ← ByteReader.readVarInt
      if count.toNat > (← ByteReader.remainingM) / 32 then return none
      let mut hashes : Array ByteArray := #[]
      for _ in [0:count.toNat] do hashes := hashes.push (← ByteReader.readBytes 32)
      let fp ← ByteReader.readUInt32
      let mut path : Array UInt32 := #[]
      while (← ByteReader.remainingM) ≥ 4 do path := path.push (← ByteReader.readUInt32)
      -- the fingerprint is read little-endian and byte-swapped (`.bigEndian`)
      let be := (readBE (u32LE fp) 0 4).toUInt32
      return some { leafHashes := hashes, masterFingerprint := be, path }
    match parsed.run r with
    | .ok (some o, _) => result := result.push (pair.keyData, o)
    | _ => pure ()
  return dictSorted (·.1) result

def writeDerivations (pairs : Array KeyValue) (type : UInt8) (origins : Array (ByteArray × KeyOrigin)) :
    Array KeyValue := Id.run do
  let mut ps := removeType pairs type
  for (pubkey, origin) in dictSorted (·.1) origins do
    let mut v := compactSize origin.leafHashes.size.toUInt64
    for h in origin.leafHashes do v := v ++ h
    v := v ++ u32BE origin.masterFingerprint
    for step in origin.path do v := v ++ u32LE step
    ps := setPair ps (KeyValue.make type pubkey v)
  return ps

/-! ## Inputs -/

structure Input where
  pairs : Array KeyValue := #[]
  deriving Inhabited

namespace Input

def pair (i : Input) (type : UInt8) (keyData : ByteArray := .empty) : Option KeyValue := findPair i.pairs type keyData
def set (i : Input) (p : KeyValue) : Input := ⟨setPair i.pairs p⟩
def remove (i : Input) (type : UInt8) (keyData : ByteArray := .empty) : Input := ⟨removePair i.pairs type keyData⟩

def previousTxid (i : Input) : Option ByteArray :=
  (i.pair InType.previousTxid).bind fun p => if p.value.size == 32 then some p.value else none
def setPreviousTxid (i : Input) : Option ByteArray → Input
  | none => i.remove InType.previousTxid
  | some v => i.set (KeyValue.make InType.previousTxid .empty v)

def outputIndex (i : Input) : Option UInt32 := (i.pair InType.outputIndex).bind (u32Value? ·.value)
def setOutputIndex (i : Input) : Option UInt32 → Input
  | none => i.remove InType.outputIndex
  | some v => i.set (KeyValue.make InType.outputIndex .empty (u32LE v))

def sequence (i : Input) : Option UInt32 := (i.pair InType.sequence).bind (u32Value? ·.value)
def setSequence (i : Input) : Option UInt32 → Input
  | none => i.remove InType.sequence
  | some v => i.set (KeyValue.make InType.sequence .empty (u32LE v))

def sighashType (i : Input) : Option UInt32 := (i.pair InType.sighashType).bind (u32Value? ·.value)
def setSighashType (i : Input) : Option UInt32 → Input
  | none => i.remove InType.sighashType
  | some v => i.set (KeyValue.make InType.sighashType .empty (u32LE v))

def witnessUTXO (i : Input) : Option SighashBIP341.SpentOutput := do
  let p ← i.pair InType.witnessUTXO
  let m : ByteReader.M SighashBIP341.SpentOutput := do
    let amount ← ByteReader.readInt64
    let scriptPubKey ← ByteReader.readVarData
    ByteReader.requireEnd
    return { amount, scriptPubKey }
  m.runAll p.value |>.toOption
def setWitnessUTXO (i : Input) : Option SighashBIP341.SpentOutput → Input
  | none => i.remove InType.witnessUTXO
  | some o => i.set (KeyValue.make InType.witnessUTXO .empty (Wire.appendVarData (i64LE o.amount) o.scriptPubKey))

def tapInternalKey (i : Input) : Option ByteArray := (i.pair InType.tapInternalKey).map (·.value)
def setTapInternalKey (i : Input) : Option ByteArray → Input
  | none => i.remove InType.tapInternalKey
  | some v => i.set (KeyValue.make InType.tapInternalKey .empty v)

def tapKeySignature (i : Input) : Option ByteArray := (i.pair InType.tapKeySignature).map (·.value)
def setTapKeySignature (i : Input) : Option ByteArray → Input
  | none => i.remove InType.tapKeySignature
  | some v => i.set (KeyValue.make InType.tapKeySignature .empty v)

def tapBIP32Derivation (i : Input) : Array (ByteArray × KeyOrigin) := readDerivations i.pairs InType.tapBIP32Derivation
def setTapBIP32Derivation (i : Input) (o : Array (ByteArray × KeyOrigin)) : Input :=
  ⟨writeDerivations i.pairs InType.tapBIP32Derivation o⟩

def finalScriptWitness (i : Input) : Option (Array ByteArray) := do
  let p ← i.pair InType.finalScriptWitness
  let m : ByteReader.M (Array ByteArray) := do
    let count ← ByteReader.readVarInt
    let mut items : Array ByteArray := #[]
    -- a count beyond the bytes left fails at the first missing item, as the Swift loop does
    for _ in [0:min count.toNat (p.value.size + 1)] do items := items.push (← ByteReader.readVarData)
    return items
  (m.run (ByteReader.init p.value)).toOption.map (·.1)
def setFinalScriptWitness (i : Input) : Option (Array ByteArray) → Input
  | none => i.remove InType.finalScriptWitness
  | some items => i.set (KeyValue.make InType.finalScriptWitness .empty
      (items.foldl Wire.appendVarData (compactSize items.size.toUInt64)))

def tapLeafScripts (i : Input) : Array TapLeafScript :=
  i.pairs.filterMap fun p =>
    if p.type != InType.tapLeafScript || p.value.size < 1 then none
    else (Tx.Taproot.ControlBlock.parse? p.keyData).map fun cb =>
      { controlBlock := cb, script := p.value.extract 0 (p.value.size - 1), leafVersion := p.value[p.value.size - 1]! }
def setTapLeafScripts (i : Input) (leaves : Array TapLeafScript) : Input := Id.run do
  let mut ps := removeType i.pairs InType.tapLeafScript
  for l in sortBytes (·.controlBlock.serialized) leaves do
    ps := setPair ps (KeyValue.make InType.tapLeafScript l.controlBlock.serialized (l.script.push l.leafVersion))
  return ⟨ps⟩

def tapScriptSignatures (i : Input) : Array (TapScriptSignatureID × ByteArray) :=
  dictSorted (fun (x : TapScriptSignatureID × ByteArray) => x.1.publicKey ++ x.1.leafHash) <|
    i.pairs.filterMap fun p =>
      if p.type != InType.tapScriptSignature || p.keyData.size != 64 then none
      else some ({ publicKey := p.keyData.extract 0 32, leafHash := p.keyData.extract 32 64 }, p.value)
def setTapScriptSignatures (i : Input) (sigs : Array (TapScriptSignatureID × ByteArray)) : Input := Id.run do
  let mut ps := removeType i.pairs InType.tapScriptSignature
  for (id, sig) in dictSorted (fun (x : TapScriptSignatureID × ByteArray) => x.1.publicKey ++ x.1.leafHash) sigs do
    ps := setPair ps (KeyValue.make InType.tapScriptSignature (id.publicKey ++ id.leafHash) sig)
  return ⟨ps⟩


end Input

/-! ## Outputs -/

structure Output where
  pairs : Array KeyValue := #[]
  deriving Inhabited

namespace Output

def pair (o : Output) (type : UInt8) (keyData : ByteArray := .empty) : Option KeyValue := findPair o.pairs type keyData
def set (o : Output) (p : KeyValue) : Output := ⟨setPair o.pairs p⟩
def remove (o : Output) (type : UInt8) (keyData : ByteArray := .empty) : Output := ⟨removePair o.pairs type keyData⟩

def amount (o : Output) : Option Int64 :=
  (o.pair OutType.amount).bind fun p => if p.value.size == 8 then some (readLE p.value 0 8).toInt64 else none
def setAmount (o : Output) : Option Int64 → Output
  | none => o.remove OutType.amount
  | some v => o.set (KeyValue.make OutType.amount .empty (i64LE v))

def script (o : Output) : Option ByteArray := (o.pair OutType.script).map (·.value)
def setScript (o : Output) : Option ByteArray → Output
  | none => o.remove OutType.script
  | some v => o.set (KeyValue.make OutType.script .empty v)

def tapInternalKey (o : Output) : Option ByteArray := (o.pair OutType.tapInternalKey).map (·.value)
def setTapInternalKey (o : Output) : Option ByteArray → Output
  | none => o.remove OutType.tapInternalKey
  | some v => o.set (KeyValue.make OutType.tapInternalKey .empty v)

def tapBIP32Derivation (o : Output) : Array (ByteArray × KeyOrigin) := readDerivations o.pairs OutType.tapBIP32Derivation
def setTapBIP32Derivation (o : Output) (d : Array (ByteArray × KeyOrigin)) : Output :=
  ⟨writeDerivations o.pairs OutType.tapBIP32Derivation d⟩

/-- depth ‖ leaf version ‖ CompactSize length ‖ script tuples (BIP371). -/
def tapTree (o : Output) : Option (Array (UInt8 × UInt8 × ByteArray)) := do
  let p ← o.pair OutType.tapTree
  let m : ByteReader.M (Array (UInt8 × UInt8 × ByteArray)) := do
    let mut tuples := #[]
    -- each tuple takes at least 3 bytes, so this many rounds always reach the end
    for _ in [0:p.value.size] do
      if (← ByteReader.remainingM) == 0 then break
      let depth ← ByteReader.readUInt8
      let leafVersion ← ByteReader.readUInt8
      let script ← ByteReader.readVarData
      tuples := tuples.push (depth, leafVersion, script)
    return tuples
  (m.run (ByteReader.init p.value)).toOption.map (·.1)
def setTapTree (o : Output) : Option (Array (UInt8 × UInt8 × ByteArray)) → Output
  | none => ⟨removeType o.pairs OutType.tapTree⟩
  | some tuples => o.set (KeyValue.make OutType.tapTree .empty
      (tuples.foldl (fun v (d, l, s) => Wire.appendVarData ((v.push d).push l) s) .empty))

end Output
end PSBT

structure PSBT where
  globals : Array PSBT.KeyValue
  inputs : Array PSBT.Input
  outputs : Array PSBT.Output
  deriving Inhabited

namespace PSBT

def globalPair (p : PSBT) (type : UInt8) : Option KeyValue := p.globals.find? (·.type == type)

/-- PSBT_GLOBAL_VERSION (four bytes, else absent). -/
def version (p : PSBT) : Option UInt32 := (p.globalPair GlobalType.version).bind (u32Value? ·.value)
/-- PSBT_GLOBAL_TX_VERSION, default 2. -/
def txVersion (p : PSBT) : Int32 :=
  match (p.globalPair GlobalType.txVersion).bind (u32Value? ·.value) with | some v => v.toInt32 | none => 2
/-- PSBT_GLOBAL_FALLBACK_LOCKTIME, default 0. -/
def fallbackLocktime (p : PSBT) : UInt32 :=
  ((p.globalPair GlobalType.fallbackLocktime).bind (u32Value? ·.value)).getD 0

/-! ## Serialization -/

def serializeMap (pairs : Array KeyValue) (d : ByteArray) : ByteArray :=
  (sortPairs pairs).foldl (fun d p => d ++ compactSize p.key.size.toUInt64 ++ p.key ++ compactSize p.value.size.toUInt64 ++ p.value) d
    |>.push 0

def serialized (p : PSBT) : ByteArray :=
  let d := serializeMap p.globals magic
  let d := p.inputs.foldl (fun d i => serializeMap i.pairs d) d
  p.outputs.foldl (fun d o => serializeMap o.pairs d) d

def base64 (p : PSBT) : String := Base64.encode p.serialized

/-! ## Parsing -/

abbrev M := StateT ByteReader (Except PSBTError)

def w {α} (m : ByteReader.M α) : M α := fun s =>
  match m.run s with
  | .ok r => .ok r
  | .error e => .error (.wire e)

def readMap : M (Array KeyValue) := do
  let mut pairs : Array KeyValue := #[]
  let mut seen : Std.HashSet ByteArray := {}
  for _ in [0:maxMapPairs + 1] do
    let keyLength ← w ByteReader.readVarInt
    if keyLength == 0 then return sortPairs pairs
    if pairs.size ≥ maxMapPairs then throw (.malformed s!"map exceeds {maxMapPairs} fields")
    if keyLength.toNat > maxMapKeySize || keyLength.toNat > (← get).remaining then
      throw (.malformed s!"map key length {keyLength} is out of bounds")
    let key ← w (ByteReader.readBytes keyLength.toNat)
    let valueLength ← w ByteReader.readVarInt
    if valueLength.toNat > (← get).remaining then throw (.malformed s!"map value length {valueLength} is out of bounds")
    let value ← w (ByteReader.readBytes valueLength.toNat)
    if seen.contains key then throw (.duplicateKey key)
    seen := seen.insert key
    pairs := pairs.push ⟨key, value⟩
  throw (.malformed "map exceeds its field limit")

def unsignedV0Transaction (globals : Array KeyValue) : Except PSBTError (Option Transaction) := do
  let global (t : UInt8) := globals.find? (·.type == t)
  let versionPair := global GlobalType.version
  if let some vp := versionPair then
    if vp.value.size != 4 then throw (.malformed "global version must be four bytes")
  let version : UInt32 := (versionPair.bind (u32Value? ·.value)).getD 0
  unless version == 0 || version == 2 do throw (.unsupportedVersion version)
  if version == 0 then
    if globals.any (fun p => 0x02 ≤ p.type && p.type ≤ 0x06) then throw (.malformed "v0 contains v2 transaction fields")
    let some pair := global GlobalType.unsignedTx | throw (.missingField "v0 unsigned transaction")
    if pair.key.size != 1 then throw (.missingField "v0 unsigned transaction")
    let tx ← (Transaction.decode pair.value).mapError PSBTError.wire
    unless tx.inputs.size ≤ maxInputOutputCount && tx.outputs.size ≤ maxInputOutputCount &&
        tx.inputs.all (fun i => i.scriptSig.isEmpty && i.witness.isEmpty) && tx.serialized false == pair.value do
      throw (.malformed "v0 requires an unsigned non-witness transaction")
    return some tx
  else if (global GlobalType.unsignedTx).isSome then throw (.malformed "v2 contains a v0 unsigned transaction")
  return none

def validateKnownFields (globals : Array KeyValue) (inputs : Array Input) (outputs : Array Output) :
    Except PSBTError Unit := do
  let single (p : KeyValue) (length : Option Nat := none) : Except PSBTError Unit := do
    if p.key.size != 1 then throw (.malformed "field must not carry key data")
    if let some n := length then
      if p.value.size != n then throw (.malformed s!"field must be {n} bytes")
  for p in globals do
    let t := p.type
    if t == GlobalType.unsignedTx || t == GlobalType.inputCount || t == GlobalType.outputCount then single p
    else if t == GlobalType.version || t == GlobalType.txVersion || t == GlobalType.fallbackLocktime then single p (some 4)
  for i in inputs do
    for p in i.pairs do
      let t := p.type
      if t == InType.previousTxid then single p (some 32)
      else if t == InType.outputIndex || t == InType.sequence || t == InType.sighashType then single p (some 4)
      else if t == InType.tapInternalKey then single p (some 32)
      else if t == InType.tapKeySignature then
        single p
        unless p.value.size == 64 || p.value.size == 65 do throw (.malformed "Taproot key signature must be 64 or 65 bytes")
      else if t == InType.witnessUTXO || t == InType.finalScriptWitness then single p
  for o in outputs do
    for p in o.pairs do
      let t := p.type
      if t == OutType.amount then single p (some 8)
      else if t == OutType.tapInternalKey then single p (some 32)
      else if t == OutType.script || t == OutType.tapTree then single p

/-- The v0 → v2 normalization (`init(v0:globals:inputs:outputs:)`). -/
def ofV0 (unsigned : Transaction) (globals : Array KeyValue) (inputs : Array Input) (outputs : Array Output) :
    Except PSBTError PSBT := do
  if inputs.any (fun i => i.pairs.any fun p => 0x0E ≤ p.type && p.type ≤ 0x12) ||
     outputs.any (fun o => o.pairs.any fun p => p.type == 0x03 || p.type == 0x04) then
    throw (.malformed "v0 contains v2 input/output fields")
  let globals := globals.filter fun p => p.type != GlobalType.unsignedTx && p.type != GlobalType.version
  let globals := globals ++ #[KeyValue.make GlobalType.version .empty (u32LE 2),
    KeyValue.make GlobalType.txVersion .empty (i32LE unsigned.version),
    KeyValue.make GlobalType.fallbackLocktime .empty (u32LE unsigned.locktime),
    KeyValue.make GlobalType.inputCount .empty (compactSize unsigned.inputs.size.toUInt64),
    KeyValue.make GlobalType.outputCount .empty (compactSize unsigned.outputs.size.toUInt64)]
  let inputs := inputs.mapIdx fun k i =>
    let ti := unsigned.inputs[k]!
    ⟨sortPairs (i.pairs ++ #[KeyValue.make InType.previousTxid .empty ti.previousOutput.txid,
      KeyValue.make InType.outputIndex .empty (u32LE ti.previousOutput.vout),
      KeyValue.make InType.sequence .empty (u32LE ti.sequence)])⟩
  let outputs := outputs.mapIdx fun k o =>
    let to := unsigned.outputs[k]!
    ⟨sortPairs (o.pairs ++ #[KeyValue.make OutType.amount .empty (i64LE to.value),
      KeyValue.make OutType.script .empty to.scriptPubKey])⟩
  return { globals := sortPairs globals, inputs, outputs }

def parseM : M PSBT := do
  let m ← w (ByteReader.readBytes 5)
  if m != magic then throw .invalidMagic
  let globals ← readMap
  let unsigned ← StateT.lift (unsignedV0Transaction globals)
  let count (t : UInt8) : Except PSBTError Nat := do
    let some pair := globals.find? (·.type == t) | throw (.missingField s!"global {t}")
    let n ← (ByteReader.readVarInt.runAll pair.value).mapError PSBTError.wire
    if n.toNat > maxInputOutputCount then throw (.malformed s!"input/output count {n} exceeds {maxInputOutputCount}")
    return n.toNat
  let inputCount ← match unsigned with
    | some tx => pure tx.inputs.size
    | none => StateT.lift (count GlobalType.inputCount)
  let outputCount ← match unsigned with
    | some tx => pure tx.outputs.size
    | none => StateT.lift (count GlobalType.outputCount)
  let mut inputs : Array Input := #[]
  let mut outputs : Array Output := #[]
  for _ in [0:inputCount] do inputs := inputs.push ⟨← readMap⟩
  for _ in [0:outputCount] do outputs := outputs.push ⟨← readMap⟩
  w ByteReader.requireEnd
  StateT.lift (validateKnownFields globals inputs outputs)
  match unsigned with
  | some tx => StateT.lift (ofV0 tx globals inputs outputs)
  | none => return { globals, inputs, outputs }

/-- `PSBT(serialized:)`: either envelope, v0 transaction fields normalized to v2. -/
def parse (data : ByteArray) : Except PSBTError PSBT := do
  if data.size > maxSerializedSize then throw (.malformed s!"document exceeds {maxSerializedSize} bytes")
  let (p, _) ← parseM.run (ByteReader.init data)
  return p

/-- `PSBT(base64:)`. -/
def ofBase64 (text : String) : Except PSBTError PSBT := do
  if text.utf8ByteSize > maxBase64Length then throw (.malformed s!"Base64 text exceeds {maxBase64Length} bytes")
  let some data := Base64.decode? text | throw .invalidMagic
  parse data

/-- `unsignedTransaction()` (PSBTRoles.swift): the transaction the v2 fields describe. -/
def unsignedTransaction (p : PSBT) : Except PSBTError Transaction := do
  let mut ins : Array Transaction.Input := #[]
  for h : k in [0:p.inputs.size] do
    let i := p.inputs[k]
    let some txid := i.previousTxid | throw (.missingField s!"input {k} previous txid")
    let some vout := i.outputIndex | throw (.missingField s!"input {k} output index")
    ins := ins.push { previousOutput := ⟨txid, vout⟩, scriptSig := .empty, sequence := i.sequence.getD 0xFFFF_FFFF }
  let mut outs : Array Transaction.Output := #[]
  for h : k in [0:p.outputs.size] do
    let o := p.outputs[k]
    let (some amount, some script) := (o.amount, o.script) | throw (.missingField s!"output {k} amount/script")
    outs := outs.push { value := amount, scriptPubKey := script }
  return { version := p.txVersion, inputs := ins, outputs := outs, locktime := p.fallbackLocktime }

/-- The BIP174 v0 envelope (validated first; per-input locktime requirements refused). -/
def base64V0 (p : PSBT) : Except PSBTError String := do
  let checked ← parse p.serialized
  if checked.inputs.any (fun i => i.pairs.any fun q => q.type == 0x11 || q.type == 0x12) then
    throw (.malformed "per-input locktime requirements are unsupported")
  let unsigned := (← checked.unsignedTransaction).serialized false
  let globals := checked.globals.filter (fun q => ![(0x02 : UInt8), 0x03, 0x04, 0x05, 0x06, 0xFB].contains q.type)
    |>.push (KeyValue.make GlobalType.unsignedTx .empty unsigned)
  let d := serializeMap globals magic
  let d := checked.inputs.foldl (fun d i => serializeMap (i.pairs.filter fun q => ![(0x0E : UInt8), 0x0F, 0x10].contains q.type) d) d
  let d := checked.outputs.foldl (fun d o => serializeMap (o.pairs.filter fun q => q.type != 0x03 && q.type != 0x04) d) d
  return Base64.encode d

end PSBT
end Winnow
