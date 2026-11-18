import Winnow.Wallet.SpendReview
import Winnow.Tx.SighashBIP143

/-! # Spend review for SegWit v0 multisig accounts: `wsh(sortedmulti(k, KEY, …))`

The account beside the Taproot one (`Wallet/SpendReview.lean`): the oldest kind of SegWit multisig, signed
with ECDSA, for a wallet one of whose keys can only sign that way (a key held in a cloud provider's key
service, which offers nothing else). Each key is either one fixed compressed public key, used as it is at
every address, or an extended public key carrying its origin and deriving `/<0;1>/*`. At least one key is
extended, so the account has an address of its own for each payment.

Here, as pure functions of public data: reading the descriptor and the rules a key must meet, the witness
script and the address at a coordinate (BIP141, BIP173; `sortedmulti` is BIP67's order, BIP383), the scripts
to watch, and `reviewSpend`, what a PSBT spends from the account and where it pays. It answers with the same
`SpendReview` and refuses with the same errors as the Taproot account's review, and takes the same care:
every input a unique known coin of the account, output ownership only from the caller's coordinates, a fee of
at most 10%. This module is in the core library (`WinnowCore`); `Wallet/SegwitMultisigAccount.lean` adds
signing, counting signatures and finalizing.

**Where the amounts come from.** A Taproot signature commits to the amount of every coin the transaction
spends. A SegWit v0 signature commits only to the amount of the one coin it spends (`SighashBIP143`), so a
PSBT that lies about another input's amount still gets a good signature, and the difference goes to the fee.
The review therefore takes every amount from `knownUTXOs`, the wallet's own record of the coins its scan
found, never from the PSBT. What the PSBT says of a coin (BIP174's witness UTXO, or the whole transaction the
coin came from, whose hash the input names) must agree with that record where it says anything.

Not here: building a spend. The wallet this was written for is spent from by whoever holds its fixed key,
who makes the PSBT; this account reviews, signs and finalizes one. -/

namespace Winnow
open Keys
open Tx (BitcoinNetwork)

/-- A k-of-n SegWit v0 script account `wsh(sortedmulti(k, KEY, …))`. -/
structure SegwitMultisigAccount where
  network : BitcoinNetwork
  /-- How many of the keys must sign. -/
  threshold : Nat
  /-- The keys in the descriptor's order. The script sorts them at each address. -/
  keys : Array Descriptor.SingleKey
  deriving Inhabited

namespace SegwitMultisigAccount
open MultisigAccount (invalid refuse lift OutputCoordinate SpendReview maxMoney)

/-- The most keys an account may list: what the script's one-byte numbers go up to. -/
def maxKeys : Nat := 16

/-- Whether a descriptor's text is of this kind, to choose which account to read it as. Only the opening is
looked at; `parse` decides whether it is one. -/
def isDescriptor (text : String) : Bool := text.startsWith "wsh("

/-! ## The descriptor -/

/-- `wsh(sortedmulti(k,KEY,…))`, with the descriptor module's reading of each key. -/
def parseExpression : Descriptor.PM (Int × Array Descriptor.SingleKey) := do
  unless ← Descriptor.consumeStr "wsh(sortedmulti(" do throw (.unknownExpression "wsh")
  let arguments ← Descriptor.parseMultiArguments
  Descriptor.expect ')'
  return arguments

/-- What tells two of a descriptor's keys apart: the public key, for a key given by itself and for an
extended key alike. -/
def identity (key : Descriptor.SingleKey) : ByteArray :=
  match key.base with
  | .publicKey data => data
  | .extended extended _ => extended.publicKey
  | .privateKey .. => ByteArray.empty

/-- Whether no two of `keys` are the same bytes. -/
def allDifferent (keys : Array ByteArray) : Bool :=
  (List.range keys.size).all fun a => (List.range a).all fun b => keys[a]! != keys[b]!

/-- What a key must be to be one of the account's: one compressed public key that is a point of the curve,
or an extended public key of this network that says where it comes from and derives `/<0;1>/*` (the Taproot
account's rule for a signer, `MultisigAccount.requireAccountKey`). Never a private key. -/
def requireKey (key : Descriptor.SingleKey) (network : BitcoinNetwork) : MAM Unit :=
  match key.base with
  | .publicKey data => do
    unless data.size == 33 do invalid "a key given by itself must be a compressed public key of 33 bytes"
    unless key.derivation.elements.isEmpty do invalid "a key given by itself derives nothing"
    match Keys.parsePublicKey data with
    | .ok _ => pure ()
    | .error _ => invalid "a key given by itself is not a point of the curve"
  | .extended extended _ => do
    if extended.privateKey.isSome then invalid "the descriptor holds a private key"
    discard (MultisigAccount.requireAccountKey key network)
  | .privateKey .. => invalid "the descriptor holds a private key"

/-- Admission: two to `maxKeys` keys, a threshold within them, each key as `requireKey` wants it, no key
twice (a key listed twice could sign twice), and at least one of them extended. -/
def make (threshold : Int) (keys : Array Descriptor.SingleKey) (network : BitcoinNetwork) :
    MAM SegwitMultisigAccount := do
  unless keys.size ≥ 2 do invalid "a multisig account needs at least two signers"
  unless keys.size ≤ maxKeys do invalid s!"a wsh(sortedmulti(…)) account lists at most {maxKeys} keys"
  unless 1 ≤ threshold && threshold ≤ keys.size do
    invalid "the threshold must be between one and the number of signers"
  for key in keys do requireKey key network
  unless allDifferent (keys.map identity) do
    invalid "the same signing key appears more than once, so this account needs fewer signers than it claims"
  unless keys.any (·.base.isExtended) do
    invalid "at least one signer must be an extended public key, so the account has an address for each payment"
  return { network, threshold := threshold.toNat, keys }

/-- Reads a descriptor of this kind, with or without its checksum, or says why it is not one. -/
def parse (string : String) (network : BitcoinNetwork) : MAM SegwitMultisigAccount := do
  let characters := string.toList.toArray
  let mut body := characters
  if let some mark := (characters.toList.zipIdx.filter (·.1 == '#')).getLast?.map (·.2) then
    let checksum := characters.extract (mark + 1) characters.size
    body := characters.extract 0 mark
    unless checksum.size == 8 &&
        Descriptor.Checksum.verify (String.ofList body.toList) (String.ofList checksum.toList) do
      throw (.named DescriptorError.invalidChecksum.name)
  let ((threshold, keys), rest) ← lift (·.name) (parseExpression.run ⟨body, 0⟩)
  if let some unexpected := rest.cs[rest.i]? then throw (.named (DescriptorError.unexpectedCharacter unexpected).name)
  make threshold keys network

/-- The descriptor in canonical form, checksum included. -/
def serialized (a : SegwitMultisigAccount) : String :=
  let body := s!"wsh(sortedmulti({a.threshold},{",".intercalate (a.keys.toList.map Descriptor.serializeSingle)}))"
  body ++ "#" ++ Descriptor.Checksum.create body

/-- The account's stable identifier: the descriptor's BIP380 checksum. -/
def id (a : SegwitMultisigAccount) : String :=
  let s := a.serialized
  String.ofList (s.toList.drop (s.length - 8))

/-- "2 of 3". -/
def policySummary (a : SegwitMultisigAccount) : String := s!"{a.threshold} of {a.keys.size}"

/-- Whether one key of the account is this account public key, whatever origin label it carries. -/
def includes (a : SegwitMultisigAccount) (accountKey : HDKey) : Bool :=
  a.keys.any fun key => match MultisigAccount.extendedKey? key with
    | some (base, _) => base.publicKey == accountKey.publicKey
    | none => false

/-- Whether `key` (a master, or an account key itself) holds one of the account's keys. -/
def hasSigner (a : SegwitMultisigAccount) (key : HDKey) : Bool :=
  a.keys.any fun k => match MultisigAccount.accountSecretKey k key with | .ok (some _) => true | _ => false

/-! ## Scripts and addresses -/

def checkMultisig : UInt8 := 0xae

/-- `k KEY … n OP_CHECKMULTISIG`, the keys in byte order: what `sortedmulti` stands for (BIP67, BIP383). -/
def witnessScript (threshold : Nat) (keys : Array ByteArray) : ByteArray :=
  let start := Script.empty.appendOpcode (Script.Op.n threshold)
  let listed := (sortBytes (fun key => key) keys).foldl (fun script key => script.appendPush key) start
  ((listed.appendOpcode (Script.Op.n keys.size)).appendOpcode checkMultisig).bytes

/-- What locks a coin to a witness script: version 0, then the script's hash. -/
def scriptPubKeyOf (script : ByteArray) : ByteArray := ByteArray.mk #[0x00, 0x20] ++ sha256 script

/-- One (choice, index) resolved: the public key each of the account's keys is there (in `keys` order), the
witness script, and the output it locks. -/
structure Resolved where
  keys : Array ByteArray
  witnessScript : ByteArray
  output : Descriptor.DerivedOutput
  deriving Inhabited

/-- (choice, index) resolved from the descriptor: choice 0 receives, 1 is change. Refused where two of the
keys come out the same there: one signature would then count for both. -/
def resolved (a : SegwitMultisigAccount) (choice : Nat) (index : UInt32) : MAM Resolved := do
  unless choice < 2 do throw (.named "indexOutOfRange")
  let keys ← a.keys.mapM fun key => lift (·.name) (Descriptor.publicKey key index choice)
  unless allDifferent keys do invalid "two of the account's keys are the same key at one address"
  let script := witnessScript a.threshold keys
  let address ← lift (·.name) (SegwitAddress.encode (AddressDecoder.hrp a.network) 0 (sha256 script))
  return { keys, witnessScript := script, output := { scriptPubKey := scriptPubKeyOf script, address } }

def derivedOutput (a : SegwitMultisigAccount) (index : UInt32) (choice : Nat) : MAM Descriptor.DerivedOutput :=
  return (← a.resolved choice index).output

/-- scriptPubKey at (multipath choice, index): choice 0 receive, 1 change. -/
def scriptPubKey (a : SegwitMultisigAccount) (index : UInt32) (choice : Nat := 0) : MAM ByteArray :=
  return (← a.derivedOutput index choice).scriptPubKey

def address (a : SegwitMultisigAccount) (index : UInt32) (choice : Nat := 0) : MAM String :=
  return (← a.derivedOutput index choice).address

/-- Both choices for indices `0 ..< count`. -/
def watchScripts (a : SegwitMultisigAccount) (count : UInt32) : MAM (Array ByteArray) := do
  let mut scripts := #[]
  for index in [0:count.toNat] do
    for choice in [0:2] do
      scripts := scripts.push (← a.derivedOutput index.toUInt32 choice).scriptPubKey
  return scripts

/-! ## Review -/

/-- The output `vout` of the transaction whose bytes are `raw`, if that transaction's identifier is `txid`:
what an input's BIP174 non-witness UTXO says its coin is. A signature commits to the identifier, so an amount
read this way is the coin's amount whatever else a PSBT says. -/
def previousOutput? (raw txid : ByteArray) (vout : UInt32) : Option Transaction.Output := do
  let previous ← (Transaction.decode raw).toOption
  guard (previous.txid == txid)
  previous.outputs[vout.toNat]?

def checkInput (a : SegwitMultisigAccount) (input : PSBT.Input) (inputIndex : Nat) (known : WalletUTXO)
    (chainTip : UInt32) : MAM Unit := do
  let n := inputIndex + 1
  unless known.amount > 0 && known.amount.toInt ≤ maxMoney do
    refuse s!"input {n} has the wrong amount or locking script"
  if (input.pair PSBT.InType.witnessUTXO).isSome then
    let claimedOK := match input.witnessUTXO with
      | some c => c.amount == known.amount && c.scriptPubKey == known.scriptPubKey
      | none => false
    unless claimedOK do refuse s!"input {n} has the wrong amount or locking script"
  if let some raw := input.nonWitnessUTXO then
    match previousOutput? raw known.txid known.vout with
    | some output =>
      unless output.value == known.amount && output.scriptPubKey == known.scriptPubKey do
        refuse s!"input {n} has the wrong amount or locking script"
    | none => refuse s!"input {n} comes with a transaction that is not the one its coin is from"
  if known.isCoinbase then
    let matureAt := known.height.toNat + Wallet.coinbaseMaturity.toNat - 1
    unless chainTip.toNat ≥ matureAt do
      refuse s!"input {n} spends a coinbase that matures in {matureAt - chainTip.toNat} blocks"
  let expected ← a.resolved known.chain.rawValue known.index
  unless expected.output.scriptPubKey == known.scriptPubKey do
    refuse s!"input {n} does not belong to this descriptor"
  unless input.sighashType.getD SighashBIP143.hashTypeAll.toUInt32 == SighashBIP143.hashTypeAll.toUInt32 do
    refuse s!"input {n} does not commit to every output"
  if let some attached := input.witnessScript then
    unless attached == expected.witnessScript do refuse s!"input {n} changes the spending policy"

def reviewedInputTotal (a : SegwitMultisigAccount) (psbt : PSBT) (knownUTXOs : Array WalletUTXO)
    (chainTip : UInt32) : MAM Int64 := do
  let mut seen : Array Transaction.Outpoint := #[]
  let mut total : Int := 0
  for h : k in [0:psbt.inputs.size] do
    let input := psbt.inputs[k]
    let some (txid, vout) := MultisigAccount.inputTxid? input | refuse s!"input {k + 1} has no complete outpoint"
    let outpoint : Transaction.Outpoint := ⟨txid, vout⟩
    if seen.contains outpoint then refuse s!"input {k + 1} repeats an earlier outpoint"
    seen := seen.push outpoint
    let some known := knownUTXOs.find? (·.outpoint == outpoint)
      | refuse s!"input {k + 1} is not an available coin of this account"
    a.checkInput input k known chainTip
    let sum := total + known.amount.toInt
    unless sum ≤ maxMoney do refuse "input amounts exceed Bitcoin's supply"
    total := sum
  return Int64.ofInt total

/-- Validates a PSBT before it is shown, signed, finalized or broadcast, as the Taproot account's
`reviewSpend` does: every input a unique known coin of this account, with the amount and script the wallet
recorded and nothing in the PSBT that says otherwise; every signature committing to all outputs; the witness
script, where one is attached, the account's own; valid amounts; a fee of at most 10%. Output ownership
comes only from the caller's coordinates. -/
def reviewSpend (a : SegwitMultisigAccount) (psbt : PSBT) (knownUTXOs : Array WalletUTXO)
    (ownedOutputCoordinates : Array OutputCoordinate) (chainTip : UInt32) : MAM SpendReview := do
  if psbt.inputs.isEmpty then refuse "it has no inputs"
  unless !psbt.outputs.isEmpty && psbt.outputs.size ≤ 1_000 do refuse "it has no outputs or more than 1,000"
  unless psbt.txVersion == 1 || psbt.txVersion == 2 do
    refuse s!"transaction version {psbt.txVersion.toInt} is not supported"
  discard (lift (·.name) psbt.unsignedTransaction)
  let inputTotal ← a.reviewedInputTotal psbt knownUTXOs chainTip
  let candidates ← MultisigAccount.outputCandidates ownedOutputCoordinates
  let ownedScripts ← candidates.mapM fun c => a.scriptPubKey c.index c.choice.toNat
  let (outputs, outputTotal) ← MultisigAccount.reviewedOutputsAmong psbt inputTotal ownedScripts
  let fee := inputTotal - outputTotal
  MultisigAccount.checkFeeCeiling fee inputTotal
  return { outputs, inputTotal, outputTotal, fee, path := .signers }

end SegwitMultisigAccount
end Winnow
