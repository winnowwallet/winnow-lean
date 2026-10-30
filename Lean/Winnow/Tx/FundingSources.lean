import Winnow.Tx.Transaction
import Winnow.Tx.Taproot

/-! # FundingSources: the addresses a transaction's inputs reveal

Port of `Sources/WalletCore/Transactions/FundingSources.swift`: per-input reconstruction of the spent
script from the scriptSig / witness alone (no prevouts, no network). -/

namespace Winnow.FundingSources

inductive Revelation where
  | publicKeyHash | scriptHash | witnessKeyHash | witnessScriptHash | taprootScriptPath
  | coinbase | taprootKeyPath | unrecognized
  deriving Repr, BEq, Inhabited

def Revelation.name : Revelation → String
  | .publicKeyHash => "publicKeyHash" | .scriptHash => "scriptHash" | .witnessKeyHash => "witnessKeyHash"
  | .witnessScriptHash => "witnessScriptHash" | .taprootScriptPath => "taprootScriptPath"
  | .coinbase => "coinbase" | .taprootKeyPath => "taprootKeyPath" | .unrecognized => "unrecognized"

structure Source where
  inputIndex : Nat
  revelation : Revelation
  scriptPubKey : Option ByteArray
  deriving Inhabited

/-- DER-encoded ECDSA signature plus sighash byte (shape only). -/
def looksLikeSignature (d : ByteArray) : Bool := d.size ≥ 9 && d.size ≤ 73 && d[0]! == 0x30

/-- SEC public key, compressed or uncompressed (shape only). -/
def looksLikePublicKey (d : ByteArray) : Bool :=
  (d.size == 33 && (d[0]! == 0x02 || d[0]! == 0x03)) || (d.size == 65 && d[0]! == 0x04)

/-- The push at `i` (just after the opcode `op`): its length-prefix size and data length, if `op` is a
push whose prefix fits. -/
def pushHeader (s : ByteArray) (op : UInt8) (i : Nat) : Option (Nat × Nat) :=
  let avail := s.size - i
  if op == 0x00 then some (0, 0)
  else if op ≤ 0x4B then some (0, op.toNat)
  else if op == 0x4C then if avail < 1 then none else some (1, s[i]!.toNat)
  else if op == 0x4D then if avail < 2 then none else some (2, (readLE s i 2).toNat)
  else if op == 0x4E then if avail < 4 then none else some (4, (readLE s i 4).toNat)
  else none

/-- A scriptSig's pushed items; `none` for any non-push opcode or a truncated push. -/
def pushedItems (s : ByteArray) : Option (Array ByteArray) := Id.run do
  let mut items : Array ByteArray := #[]
  let mut i := 0
  while i < s.size do
    let op := s[i]!
    i := i + 1
    match pushHeader s op i with
    | none => return none
    | some (hdr, l) =>
      i := i + hdr
      if s.size - i < l then return none
      items := items.push (s.extract i (i + l))
      i := i + l
  return some items

def p2pkh (h : ByteArray) : ByteArray := ByteArray.mk #[0x76, 0xA9, 0x14] ++ h ++ ByteArray.mk #[0x88, 0xAC]
def p2sh (h : ByteArray) : ByteArray := ByteArray.mk #[0xA9, 0x14] ++ h ++ ByteArray.mk #[0x87]

def legacyRevelation (scriptSig : ByteArray) : Revelation × Option ByteArray :=
  match pushedItems scriptSig with
  | none => (.unrecognized, none)
  | some items =>
    match items.back? with
    | none => (.unrecognized, none)
    | some last =>
      if items.size == 2 && looksLikeSignature items[0]! && looksLikePublicKey items[1]! then
        (.publicKeyHash, some (p2pkh (hash160 items[1]!)))
      else if !last.isEmpty && !looksLikeSignature last && !looksLikePublicKey last then
        (.scriptHash, some (p2sh (hash160 last)))
      else (.unrecognized, none)

/-- Script-path taproot spend: `<stack…> <tapscript> <control block>`, BIP342 leaf version only, the
recomputed output key's parity matching the control block. -/
def taprootScriptPath (witness : Array ByteArray) : Option (Revelation × Option ByteArray) := do
  let controlData ← witness.back?
  guard (witness.size ≥ 2)
  let control ← Tx.Taproot.ControlBlock.parse? controlData
  guard (control.leafVersion == Tx.Taproot.leafVersion)
  let scriptData := witness[witness.size - 2]!
  guard (!scriptData.isEmpty)
  let root := control.path.foldl Tx.Taproot.branchHash (Tx.Taproot.leafHash control.leafVersion ⟨scriptData⟩)
  let (key, parity) ← Tx.Taproot.tweakedOutputKey control.internalKey (some root)
  guard (parity == control.outputKeyParity)
  return (.taprootScriptPath, some (ByteArray.mk #[0x51, 0x20] ++ key))

def classify (w : Array ByteArray) : Revelation × Option ByteArray :=
  if w.size == 2 && looksLikeSignature w[0]! && looksLikePublicKey w[1]! then
    (.witnessKeyHash, some (ByteArray.mk #[0x00, 0x14] ++ hash160 w[1]!))
  else if w.size == 1 && (w[0]!.size == 64 || w[0]!.size == 65) then (.taprootKeyPath, none)
  else match (if w.size ≥ 2 then taprootScriptPath w else none) with
    | some r => r
    | none =>
      match w.back? with
      | some s => if !s.isEmpty then (.witnessScriptHash, some (ByteArray.mk #[0x00, 0x20] ++ sha256 s))
                  else (.unrecognized, none)
      | none => (.unrecognized, none)

/-- Strip a BIP341 annex (last item starting 0x50) only when the rest then reads as taproot. -/
def segwitRevelation (full : Array ByteArray) : Revelation × Option ByteArray :=
  let annexed := full.size ≥ 2 && (full.back?.bind fun a => if a.isEmpty then none else some a[0]!) == some 0x50
  let trimmed := classify full.pop
  if annexed && (trimmed.1 == .taprootKeyPath || trimmed.1 == .taprootScriptPath) then trimmed
  else classify full

def revelation (input : Transaction.Input) : Revelation × Option ByteArray :=
  if input.previousOutput.txid == ByteArray.mk (Array.replicate 32 0) && input.previousOutput.vout == 0xFFFF_FFFF then
    (.coinbase, none)
  else if !input.scriptSig.isEmpty then legacyRevelation input.scriptSig
  else if input.witness.isEmpty then (.unrecognized, none)
  else segwitRevelation input.witness

/-- Per-input reconstruction, in input order. -/
def sources (tx : Transaction) : Array Source :=
  tx.inputs.mapIdx fun i input =>
    let (r, s) := revelation input
    { inputIndex := i, revelation := r, scriptPubKey := s }

/-- The distinct revealed funding scripts, in first-seen order. -/
def fundingScripts (tx : Transaction) : Array ByteArray := Id.run do
  let mut seen : Array ByteArray := #[]
  for input in tx.inputs do
    if let (_, some s) := revelation input then
      if !seen.contains s then seen := seen.push s
  return seen

end Winnow.FundingSources
