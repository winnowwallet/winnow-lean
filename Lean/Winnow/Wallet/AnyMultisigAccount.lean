import Winnow.Wallet.MultisigAccount
import Winnow.Wallet.SegwitMultisigAccount

/-! # A multisig account of either kind

The wallet keeps two kinds of multisig account: the Taproot one, `tr(NUMS, sortedmulti_a(k, …))` with its
recovery leaves and nested members (`MultisigAccount`), and the SegWit v0 one, `wsh(sortedmulti(k, KEY, …))`
(`SegwitMultisigAccount`). A stored record names its account by the descriptor's text alone
(`MultisigAccountRecord`), so whoever holds a record reads it here and gets whichever kind it is, with the
questions both kinds answer asked one way: the addresses, the review of a spend, signing, counting signatures
and finalizing.

What only the Taproot account has (building a spend, recovery paths, nested members, a Ledger among the
signers) is asked of it directly, through `taproot?`; the answers given here for the SegWit v0 account are the
ones an account without those has: no recovery, not nested, one way to spend. -/

namespace Winnow
open Keys
open Tx (BitcoinNetwork)

inductive AnyMultisigAccount where
  | taproot (account : MultisigAccount)
  | segwit (account : SegwitMultisigAccount)
  deriving Inhabited

/-- A Taproot account where an account of either kind is wanted. -/
instance : Coe MultisigAccount AnyMultisigAccount := ⟨.taproot⟩

namespace AnyMultisigAccount
open MultisigAccount (OutputCoordinate SpendPath SpendReview Recovery Members)

/-- Reads a descriptor as the kind its opening says it is (`wsh(` or anything else, read as Taproot). -/
def parse (text : String) (network : BitcoinNetwork) : MAM AnyMultisigAccount :=
  if SegwitMultisigAccount.isDescriptor text then .segwit <$> SegwitMultisigAccount.parse text network
  else .taproot <$> MultisigAccount.parse text network

/-- The Taproot account, when it is one: for what only that kind has. -/
def taproot? : AnyMultisigAccount → Option MultisigAccount
  | .taproot a => some a
  | .segwit _ => none

def isSegwit : AnyMultisigAccount → Bool
  | .taproot _ => false
  | .segwit _ => true

def network : AnyMultisigAccount → BitcoinNetwork
  | .taproot a => a.network
  | .segwit a => a.network

/-- The descriptor in canonical form, checksum included: what a record stores. -/
def serialized : AnyMultisigAccount → String
  | .taproot a => a.descriptor.serialized
  | .segwit a => a.serialized

/-- The account's stable identifier: the descriptor's BIP380 checksum. -/
def id : AnyMultisigAccount → String
  | .taproot a => a.id
  | .segwit a => a.id

def policySummary : AnyMultisigAccount → String
  | .taproot a => a.policySummary
  | .segwit a => a.policySummary

/-- Signatures a spend needs (on the first signers' leaf of a Taproot account). -/
def threshold : AnyMultisigAccount → Int
  | .taproot a => a.threshold
  | .segwit a => a.threshold

/-- The account's signer keys: the distinct keys of a Taproot account's signers' leaves, every key of a
SegWit v0 account (its fixed keys among them). -/
def signers : AnyMultisigAccount → Array Descriptor.SingleKey
  | .taproot a => a.signers
  | .segwit a => a.keys

/-- Whether one key of the account is this account public key, whatever origin label it carries. -/
def includes : AnyMultisigAccount → HDKey → Bool
  | .taproot a, key => a.includes key
  | .segwit a, key => a.includes key

/-- Whether this account public key is among the signers, not on a recovery leaf alone. -/
def signs : AnyMultisigAccount → HDKey → Bool
  | .taproot a, key => a.signs key
  | .segwit a, key => a.includes key

/-- The output at `index` for each choice, receive then change: what a record's watched scripts are made of.
`none` for a choice where a SegWit v0 account has no address at `index` (`SegwitMultisigAccount.usable`). -/
def derivedOutputs : AnyMultisigAccount → UInt32 → MAM (Array (Option Descriptor.DerivedOutput))
  | .taproot a, index => (·.map some) <$> MultisigAccount.lift (·.name) (a.descriptor.derived index a.network)
  | .segwit a, index => return #[← a.derivedOutput? index 0, ← a.derivedOutput? index 1]

/-- The first index at or after `index` where the account has an address on `choice`: `index` itself for a
Taproot account, and for a SegWit v0 account wherever it has an address there. -/
def usableIndex : AnyMultisigAccount → (choice : Nat) → UInt32 → MAM UInt32
  | .taproot _, _, index => pure index
  | .segwit a, choice, index => a.usableIndex choice index

/-- scriptPubKey at (multipath choice, index): choice 0 receive, 1 change. -/
def scriptPubKey : AnyMultisigAccount → UInt32 → (choice : Nat := 0) → MAM ByteArray
  | .taproot a, index, choice => a.scriptPubKey index choice
  | .segwit a, index, choice => a.scriptPubKey index choice

def address : AnyMultisigAccount → UInt32 → (choice : Nat := 0) → MAM String
  | .taproot a, index, choice => a.address index choice
  | .segwit a, index, choice => a.address index choice

/-! ## What only a Taproot account has more than one of -/

def isNested : AnyMultisigAccount → Bool
  | .taproot a => a.isNested
  | .segwit _ => false

def recovery : AnyMultisigAccount → Option Recovery
  | .taproot a => a.recovery
  | .segwit _ => none

/-- The ways to spend at once: a Taproot account's signers' leaves, a SegWit v0 account's one script. -/
def signersPaths : AnyMultisigAccount → Array SpendPath
  | .taproot a => a.signersPaths
  | .segwit _ => #[.signers]

def recoveryPaths : AnyMultisigAccount → Array SpendPath
  | .taproot a => a.recoveryPaths
  | .segwit _ => #[]

/-- The keys of `path`, in descriptor order; none for a path the account does not have. -/
def keysOn : AnyMultisigAccount → SpendPath → Array Descriptor.SingleKey
  | .taproot a, path => a.keysOn path
  | .segwit a, path => if path == .signers then a.keys else #[]

/-- How many of `path`'s keys must sign. -/
def thresholdOn : AnyMultisigAccount → SpendPath → Int
  | .taproot a, path => a.thresholdOn path
  | .segwit a, path => if path == .signers then a.threshold else 0

/-! ## A spend -/

/-- Validates a PSBT before it is shown, signed, finalized or broadcast. -/
def reviewSpend : AnyMultisigAccount → PSBT → Array WalletUTXO → Array OutputCoordinate → UInt32 → MAM SpendReview
  | .taproot a, psbt, coins, owned, tip => a.reviewSpend psbt coins owned tip
  | .segwit a, psbt, coins, owned, tip => a.reviewSpend psbt coins owned tip

/-- Reviews the spend, then adds this key's signature to every input: BIP340 on every leaf the key is in, or
ECDSA for a SegWit v0 account. -/
def sign : AnyMultisigAccount → PSBT → HDKey → Array WalletUTXO → Array OutputCoordinate → UInt32 → ByteArray → MAM PSBT
  | .taproot a, psbt, key, coins, owned, tip, aux => a.sign psbt key coins owned tip aux
  | .segwit a, psbt, key, coins, owned, tip, aux => a.sign psbt key coins owned tip aux

/-- Which keys of `path` (by position among them) have a verified signature on every input. -/
def approvals : AnyMultisigAccount → PSBT → Array WalletUTXO → (path : SpendPath := .signers) → MAM (Array Nat)
  | .taproot a, psbt, coins, path => a.approvals psbt coins path
  | .segwit a, psbt, coins, path => if path == .signers then a.approvals psbt coins else return #[]

/-- Finalizes a PSBT with enough verified signatures on every input and extracts the transaction. -/
def finalizeSpend : AnyMultisigAccount → PSBT → Array WalletUTXO → Array OutputCoordinate → UInt32 → MAM (PSBT × Transaction)
  | .taproot a, psbt, coins, owned, tip => a.finalizeSpend psbt coins owned tip
  | .segwit a, psbt, coins, owned, tip => a.finalizeSpend psbt coins owned tip

end AnyMultisigAccount
end Winnow
