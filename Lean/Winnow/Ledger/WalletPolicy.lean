import Winnow.Ledger.APDU
import Winnow.Ledger.Merkle
import Winnow.Wallet.MultisigAccount

/-! # BIP388 wallet policies as Ledger's Bitcoin app registers them

Port of `Sources/WalletCore/Ledger/LedgerWalletPolicy.swift` (upstream d2ca878): a name, a descriptor
template over key placeholders, and the keys. The device keeps nothing; registration returns an HMAC
the phone stores and sends with every later request for this account.

`init(name:account:)` is `ofAccount` (and `ofDescriptor` for the descriptor alone): the account's
`tr(K,TREE)` with its `sortedmulti_a`/`multi_a` signers' leaves and timelocked recovery leaves, the tree
in the descriptor's shape. The Bitcoin app takes a template of at most 512 characters and 15 keys. -/

namespace Winnow.Ledger
open Keys

/-- `MultisigAccount.signerSuffix` (`/<0;1>/*`). -/
abbrev signerSuffix : Array Descriptor.Element := MultisigAccount.signerSuffix

/-- A BIP388 wallet policy (`LedgerWalletPolicy`). -/
structure WalletPolicy where
  name : String
  /-- For example `tr(@0/**,sortedmulti_a(2,@1/**,@2/**))`. -/
  template : String
  /-- Key information in placeholder order: `[fingerprint/path]xpub`, or a bare xpub for a key with
  no origin. -/
  keys : Array String
  deriving Inhabited, BEq, Repr

namespace WalletPolicy

/-- The longest descriptor template the Bitcoin app registers: `MAX_DESCRIPTOR_TEMPLATE_LENGTH_V2` in its
`src/common/wallet.h`, checked in `read_wallet_policy_header` (app-bitcoin-new, 2.2.x). -/
def maximumTemplateLength : Nat := 512
/-- The most keys in a policy, `MAX_N_KEYS_IN_WALLET_POLICY`, the internal key included. -/
def maximumKeys : Nat := 15

/-- Names are shown on the Ledger: 1 to 64 printable ASCII characters, with no space at either end. -/
def isValidName (name : String) : Bool :=
  let bytes := name.toUTF8
  1 ≤ bytes.size && bytes.size ≤ 64 && bytes.data.all (fun b => 0x20 ≤ b && b ≤ 0x7E)
    && bytes[0]! != 0x20 && bytes[bytes.size - 1]! != 0x20

/-- `init(name:template:keys:)`. -/
def make (name template : String) (keys : Array String) : Except LedgerError WalletPolicy := do
  unless isValidName name do
    throw (.mismatch "an account name must be 1 to 64 plain characters with no space at either end")
  unless !keys.isEmpty && keys.size ≤ maximumKeys do
    throw (.mismatch s!"a Ledger policy holds at most {maximumKeys - 1} signer keys")
  unless template.utf8ByteSize ≤ maximumTemplateLength do
    throw (.mismatch s!"this account's policy is {template.utf8ByteSize} characters and a Ledger takes at most {maximumTemplateLength}; fewer members, or members needing fewer of their keys, make it smaller")
  return { name, template, keys }

/-- `keyInformation(_:)`: `[fingerprint/86'/1'/0']tpub…` with the derivation suffix removed. -/
def keyInformation (key : Descriptor.SingleKey) : Except LedgerError String := do
  let .extended xpub network := key.base
    | throw (.mismatch "every policy key must be an extended public key under /<2n;2n+1>/*")
  unless xpub.privateKey.isNone && (MultisigAccount.appearance? key.derivation.elements).isSome do
    throw (.mismatch "every policy key must be an extended public key under /<2n;2n+1>/*")
  let mut text := ""
  if let some origin := key.origin then
    text := text ++ "[" ++ Descriptor.hex8 origin.fingerprint
    for step in origin.path do
      text := text ++ s!"/{(step &&& ~~~HDKey.hardenedOffset).toNat}" ++ (if step ≥ HDKey.hardenedOffset then "'" else "")
    text := text ++ "]"
  return text ++ xpub.serialized network

/-- The placeholder of `key`, numbering a new key after the ones seen so far. -/
def placeholder (keys : Array String) (key : Descriptor.SingleKey) : Except LedgerError (Array String × String) := do
  let information ← keyInformation key
  let (keys, index) := match keys.findIdx? (· == information) with
    | some i => (keys, i)
    | none => (keys.push information, keys.size)
  let some appearance := MultisigAccount.appearance? key.derivation.elements
    | throw (.mismatch "every policy key must be an extended public key under /<2n;2n+1>/*")
  let text := if appearance == 0 then s!"@{index}/**" else s!"@{index}{MultisigAccount.pairSuffixText appearance}"
  return (keys, text)

def placeholders (keys : Array String) (leafKeys : Array Descriptor.SingleKey) :
    Except LedgerError (Array String × String) := do
  let mut keys := keys
  let mut texts : Array String := #[]
  for k in leafKeys do
    let (ks, t) ← placeholder keys k
    keys := ks
    texts := texts.push t
  return (keys, ",".intercalate texts.toList)

def leafTemplate (keys : Array String) : Descriptor.Leaf → Except LedgerError (Array String × String)
  | .sortedMultiA t ks => do let (keys, p) ← placeholders keys ks; return (keys, s!"sortedmulti_a({t},{p})")
  | .multiA t ks => do let (keys, p) ← placeholders keys ks; return (keys, s!"multi_a({t},{p})")
  | .timelocked (.pk k) blocks => do
    let (keys, p) ← placeholder keys k
    return (keys, s!"and_v(v:pk({p}),older({blocks}))")
  | .timelocked (.multiA t ks) blocks => do
    let (keys, p) ← placeholders keys ks
    return (keys, s!"and_v(v:multi_a({t},{p}),older({blocks}))")
  | .pk _ => throw (.mismatch "a plain pk() leaf is not an account leaf")

/-- The tree's template, keeping the descriptor's shape; keys are numbered left to right. -/
def nodeTemplate (keys : Array String) : Descriptor.ScriptTree → Except LedgerError (Array String × String)
  | .leaf l => leafTemplate keys l
  | .branch left right => do
    let (keys, l) ← nodeTemplate keys left
    let (keys, r) ← nodeTemplate keys right
    return (keys, "{" ++ l ++ "," ++ r ++ "}")

/-- `init(name:account:)` over the account's internal key and tree: the internal key is `@0`, each
distinct key after it gets the next placeholder in descriptor order, `/<0;1>/*` becomes `/**` and a
reused signer's `/<2;3>/*`, `/<4;5>/*`… stays as it is. The tree keeps the descriptor's shape. The
template therefore derives exactly the account's addresses. -/
def ofTree (name : String) (internalKey : Descriptor.SingleKey) (tree : Descriptor.ScriptTree) :
    Except LedgerError WalletPolicy := do
  let .extended .. := internalKey.base
    | throw (.mismatch "only accounts whose internal key is an extended key can be registered")
  let keys := #[← keyInformation internalKey]
  let (keys, body) ← nodeTemplate keys tree
  make name s!"tr(@0/**,{body})" keys

/-- `init(name:account:)` from the account's descriptor. -/
def ofDescriptor (name : String) (d : Descriptor) : Except LedgerError WalletPolicy := do
  let .trTree internalKey tree := d.expression
    | throw (.mismatch "only accounts whose internal key is an extended key can be registered")
  ofTree name internalKey tree

/-- `LedgerWalletPolicy(name:account:)`. -/
def ofAccount (name : String) (account : MultisigAccount) : Except LedgerError WalletPolicy :=
  ofDescriptor name account.descriptor

/-- Version 2: 0x02 ‖ name length ‖ name ‖ compactSize(template length) ‖ SHA-256(template) ‖
compactSize(key count) ‖ Merkle root of the keys. -/
def serialized (p : WalletPolicy) : ByteArray :=
  let name := p.name.toUTF8
  let template := p.template.toUTF8
  ByteArray.mk #[0x02, name.size.toUInt8] ++ name ++ compactSize template.size.toUInt64 ++ sha256 template
    ++ compactSize p.keys.size.toUInt64 ++ Merkle.root (p.keys.map (Merkle.elementHash ·.toUTF8))

/-- The policy id the device returns on registration: SHA-256 of `serialized`. -/
def id (p : WalletPolicy) : ByteArray := sha256 p.serialized

end WalletPolicy
end Winnow.Ledger
