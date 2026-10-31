import Winnow.Ledger.Client
import Winnow.Wallet.PSBTRoles
import Winnow.Wallet.SwiftJSON

/-! # A Ledger as a signer of a multisig account

Port of `Sources/WalletCore/Ledger/LedgerMultisig.swift` (upstream 1cf93fb). The phone builds and reviews
every spend itself; the Ledger shows the payment on its own screen and adds its signature; the phone
keeps a Ledger signature only after verifying it against the recomputed sighash.

The account-level functions (`register`, `displayAddress`, `sign`) are what the app calls. Each is a
thin wrapper over a `…With` function that takes what Swift reads from the account (its signers, the
policy built from it, the address it derives) as arguments. The stored registration is Phase B's
`Winnow.LedgerRegistration` (`Wallet/MultisigAccount.lean`); `MultisigAccountRecord.checkLedgerRegistration`
is here because it needs the policy. -/

namespace Winnow.Ledger
open Keys SwiftJSON

/-- `LedgerRegistration`, as Phase B stores it in `MultisigAccountRecord.ledger`. -/
abbrev Registration := LedgerRegistration

/-- What `LedgerMultisig.sign` can throw: the Ledger's errors, or the PSBT's while it is checked. -/
inductive SignError where
  | ledger (e : LedgerError)
  | psbt (e : PSBTError)
  | signing (e : SignFailure)
  deriving Inhabited

def SignError.name : SignError → String
  | .ledger e => e.name | .psbt e => e.name | .signing e => e.name

def SignError.ofRole : PSBTRoleError → SignError
  | .psbt e => .psbt e | .sign e => .signing e

namespace Multisig

/-- The Ledger's signer key: BIP87 multisig account 0, `m/87'/coin'/0'`, which the app exports
without a warning. -/
def keyPath (network : Tx.BitcoinNetwork) : Array UInt32 :=
  let coin : UInt32 := if network == .mainnet then 0 else 1
  #[87 + HDKey.hardenedOffset, coin + HDKey.hardenedOffset, HDKey.hardenedOffset]

/-- `signerExpression(client:network:)`: the Ledger's signer key expression,
`[fp/87'/1'/0']tpub…/<0;1>/*`, and its fingerprint. The key must sit where its origin says. -/
def signerExpression (network : Tx.BitcoinNetwork) : Program (String × UInt32) := do
  let fingerprint ← Client.masterFingerprint
  let path := keyPath network
  let text ← Client.extendedPublicKey path false
  let key ← match HDKey.deserialize text with
    | .ok k => pure k
    | .error _ => throw (LedgerError.protocolViolation "an extended key that does not parse")
  let isTestKey := text.startsWith "tpub"
  unless isTestKey == (network != .mainnet) && key.depth.toNat == path.size && some key.childIndex == path.back?
      && key.privateKey.isNone do
    throw (LedgerError.mismatch "the Ledger's key is for another network or path; open the Bitcoin app for this network")
  let origin := "/".intercalate (path.toList.map fun s => s!"{(s &&& ~~~HDKey.hardenedOffset).toNat}'")
  return (s!"[{Descriptor.hex8 fingerprint}/{origin}]{text}/<0;1>/*", fingerprint)

/-- `ledgerSigner(of:fingerprint:path:)` over the account's keys (`allKeys`): the key, on any leaf, whose
origin is the Ledger's fingerprint and key path. -/
def ledgerSigner (signers : Array Descriptor.SingleKey) (fingerprint : UInt32) (path : Array UInt32) :
    Option Descriptor.SingleKey :=
  signers.find? fun s => match s.origin with
    | some o => o.fingerprint == fingerprint && o.path == path
    | none => false

/-- The body of `register(_:name:fingerprint:client:)` once the account's policy is built: registers
it after the user approves it on the Ledger, then checks that the Ledger derives the account's first
receive address `firstAddress` (`account.address(index: 0, choice: 0)`). -/
def registerPolicy (policy : WalletPolicy) (fingerprint : UInt32) (path : Array UInt32) (firstAddress : String) :
    Program Registration := do
  let (id, hmac) ← Client.register policy
  let registration : Registration :=
    { policyName := policy.name, policyID := id, hmac, masterFingerprint := fingerprint, keyPath := path }
  let first ← Client.address policy hmac false 0 false
  unless first == firstAddress do throw (LedgerError.mismatch "the Ledger derives a different first address")
  return registration

/-- `register(_:name:fingerprint:client:)` with the account given by its signers, its network, the
policy built from it under a name and its first receive address. -/
def registerWith (signers : Array Descriptor.SingleKey) (network : Tx.BitcoinNetwork)
    (makePolicy : String → Except LedgerError WalletPolicy) (name : String) (fingerprint : UInt32)
    (firstAddress : String) : Program Registration := do
  let path := keyPath network
  if (ledgerSigner signers fingerprint path).isNone then
    throw (LedgerError.mismatch "this account has no signer for this Ledger")
  let policy ← Program.ofExcept (makePolicy name)
  registerPolicy policy fingerprint path firstAddress

/-- `policy(_:_:)`: the account's policy under the stored name, which must be the registered one. -/
def policy (makePolicy : String → Except LedgerError WalletPolicy) (registration : Registration) :
    Except LedgerError WalletPolicy := do
  let policy ← makePolicy registration.policyName
  unless policy.id == registration.policyID do
    throw (.mismatch "the stored Ledger registration belongs to another account")
  return policy

/-- `displayAddress(_:registration:choice:index:client:)`: shows the address at (choice, index) on
the Ledger; it must equal `expected`, the phone's own derivation. -/
def displayAddressWith (makePolicy : String → Except LedgerError WalletPolicy) (registration : Registration)
    (choice : Nat := 0) (index : UInt32) (expected : String) : Program String := do
  let policy ← Program.ofExcept (policy makePolicy registration)
  let shown ← Client.address policy registration.hmac (choice == 1) index true
  unless shown == expected do throw (LedgerError.mismatch "the Ledger shows a different address")
  return shown

/-- The body of `sign(_:account:registration:client:)` after the device answered: every signature
must verify for the leaf it names, on its input; otherwise the PSBT is left untouched (the caller
keeps its own). Returns the signed PSBT and the number of signatures added. -/
def applySignatures (psbt : PSBT) (signatures : Array Signature) : Except SignError (PSBT × Nat) := do
  let mut signed := psbt
  let mut added := 0
  for s in signatures do
    let some leafHash := s.leafHash
      | throw (.ledger (.protocolViolation "a signature this account cannot use"))
    unless s.publicKey.size == 32 && s.inputIndex < signed.inputs.size do
      throw (.ledger (.protocolViolation "a signature this account cannot use"))
    let input := signed.inputs[s.inputIndex]!
    let existing := input.tapScriptSignatures
    let isNew := (existing.find? fun (id, _) => id.publicKey == s.publicKey && id.leafHash == leafHash).isNone
    if isNew then added := added + 1
    let updated := match existing.findIdx? fun (id, _) => id.publicKey == s.publicKey && id.leafHash == leafHash with
      | some j => existing.set! j ({ publicKey := s.publicKey, leafHash }, s.signature)
      | none => existing.push ({ publicKey := s.publicKey, leafHash }, s.signature)
    signed := signed.modifyInput s.inputIndex (·.setTapScriptSignatures updated)
  let tx ← signed.unsignedTransaction.mapError .psbt
  let spent ← signed.spentOutputs.mapError .psbt
  for s in signatures do
    -- Checked on its own leaf: the same key may already hold a valid signature elsewhere, which must
    -- not vouch for this one.
    let verified ← (signed.verifiedScriptPathSigners s.inputIndex (s.leafHash.getD .empty) tx spent).mapError SignError.ofRole
    unless verified.contains s.publicKey do throw (.ledger (.mismatch "a Ledger signature does not verify"))
  unless added > 0 do throw (.ledger (.mismatch "the Ledger added no signature"))
  return (signed, added)

/-- `sign` with the account given by its policy (`makePolicy`, checked against the registration). -/
def signWith (psbt : PSBT) (makePolicy : String → Except LedgerError WalletPolicy) (registration : Registration) :
    Program (Except SignError (PSBT × Nat)) := do
  let policy ← Program.ofExcept (policy makePolicy registration)
  let signatures ← Client.signPSBT psbt policy registration.hmac
  return applySignatures psbt signatures

/-! ## Over the account (what the app calls) -/

/-- An address the account derives, as the Ledger functions compare it. Swift throws the account's
own error here; an account that `MultisigAccount.make` accepted derives every address, so this is a
`mismatch` in the Ledger's error type. -/
def accountAddress (account : MultisigAccount) (index : UInt32) (choice : Nat) : Except LedgerError String :=
  (account.address index choice).mapError fun _ => .mismatch "this phone cannot derive the account's address"

/-- `ledgerSigner(of:fingerprint:path:)`: the key, on any leaf, whose origin is the Ledger's. -/
def accountLedgerSigner (account : MultisigAccount) (fingerprint : UInt32) (path : Array UInt32) :
    Option Descriptor.SingleKey :=
  ledgerSigner account.allKeys fingerprint path

/-- `hasLedgerSigner(_:fingerprint:)`: whether a Ledger with `fingerprint` holds a key of the account, so a
phone joining it can register it on that Ledger. -/
def hasLedgerSigner (account : MultisigAccount) (fingerprint : UInt32) : Bool :=
  (accountLedgerSigner account fingerprint (keyPath account.network)).isSome

/-- `namesALedgerKey(_:)`: whether any key of the account sits at a Ledger's key path, whoever holds it. -/
def namesALedgerKey (account : MultisigAccount) : Bool :=
  let path := keyPath account.network
  account.allKeys.any fun k => (k.origin.map (·.path)) == some path

/-- `register(_:name:fingerprint:client:)`: registers the account on the Ledger after the user approves
it there, then checks that the Ledger derives the same first receive address. -/
def register (account : MultisigAccount) (name : String) (fingerprint : UInt32) : Program Registration := do
  let path := keyPath account.network
  if (accountLedgerSigner account fingerprint path).isNone then
    throw (LedgerError.mismatch "this account has no signer for this Ledger")
  let policy ← Program.ofExcept (WalletPolicy.ofAccount name account)
  let (id, hmac) ← Client.register policy
  let registration : Registration :=
    { policyName := name, policyID := id, hmac, masterFingerprint := fingerprint, keyPath := path }
  let first ← Client.address policy hmac false 0 false
  unless first == (← Program.ofExcept (accountAddress account 0 0)) do
    throw (LedgerError.mismatch "the Ledger derives a different first address")
  return registration

/-- `policy(_:_:)`: the account's policy under the stored name, which must be the registered one. -/
def accountPolicy (account : MultisigAccount) (registration : Registration) : Except LedgerError WalletPolicy :=
  policy (WalletPolicy.ofAccount · account) registration

/-- `displayAddress(_:registration:choice:index:client:)`: shows the address at (choice, index) on the
Ledger for the user to compare with the phone's; it must equal the phone's own derivation. -/
def displayAddress (account : MultisigAccount) (registration : Registration) (choice : Nat := 0) (index : UInt32) :
    Program String := do
  let policy ← Program.ofExcept (accountPolicy account registration)
  let shown ← Client.address policy registration.hmac (choice == 1) index true
  unless shown == (← Program.ofExcept (accountAddress account index choice)) do
    throw (LedgerError.mismatch "the Ledger shows a different address")
  return shown

/-- `sign(_:account:registration:client:)`: asks the Ledger to sign `psbt`, which the caller has
reviewed. Every signature it returns must verify for the leaf it names, on its input; otherwise the
PSBT is left untouched (the caller keeps its own). The outer `Program` fails with the device's errors;
the inner `Except` is the check of what it returned: the signed PSBT and the number of signatures
added. -/
def sign (psbt : PSBT) (account : MultisigAccount) (registration : Registration) :
    Program (Except SignError (PSBT × Nat)) :=
  signWith psbt (WalletPolicy.ofAccount · account) registration

end Multisig
end Winnow.Ledger

namespace Winnow.MultisigAccountRecord

/-- `checkLedgerRegistration(for:)`: a stored Ledger registration must be this account's own policy
and name one of its signers. -/
def checkLedgerRegistration (r : MultisigAccountRecord) (account : MultisigAccount) : MAM Unit := do
  let some ledger := r.ledger | return
  let belongs := ledger.policyID.size == 32 && ledger.hmac.size == 32
    && (Ledger.Multisig.accountLedgerSigner account ledger.masterFingerprint ledger.keyPath).isSome
    && ((Ledger.WalletPolicy.ofAccount ledger.policyName account).toOption.map (·.id)) == some ledger.policyID
  unless belongs do
    MultisigAccount.invalid "the stored Ledger registration does not belong to this account"

end Winnow.MultisigAccountRecord
