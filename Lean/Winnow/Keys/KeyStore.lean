import Std.Data.HashMap
import Winnow.Keys.Unicode

/-! # Wallet secret storage (port of `Keys/KeyStore.swift`)

`KeyStore` is a structure of functions over a monad, the Lean form of the Swift protocol. The device
implementation (`KeychainStore.swift`, Security framework) is not ported here: it becomes an iOS capability.
`InMemoryKeyStore` is the store of `Tests/Support/InMemoryKeyStore.swift`. -/

namespace Winnow.Keys

inductive KeyStoreError where
  | notFound (walletID : String)
  | alreadyExists (walletID : String)
  | malformedSecret
  /-- A recognizable account-secret format that this version cannot read (its bounded label). -/
  | unsupportedSecretVersion (label : String)
  /-- An `OSStatus` from the keychain. -/
  | keychain (status : Int32)
  deriving Repr, DecidableEq

def KeyStoreError.name : KeyStoreError → String
  | .notFound _ => "notFound" | .alreadyExists _ => "alreadyExists"
  | .malformedSecret => "malformedSecret" | .unsupportedSecretVersion _ => "unsupportedSecretVersion"
  | .keychain _ => "keychain"

def errSecUserCanceled : Int32 := -128
def errSecAuthFailed : Int32 := -25293
def errSecInteractionNotAllowed : Int32 := -25308

/-- `errorDescription`. A keychain status other than the three named ones is described by the Security
framework (`SecCopyErrorMessageString`), which belongs to the keychain capability: `none` here. -/
def KeyStoreError.errorDescription : KeyStoreError → Option String
  | .notFound w => some s!"The protected key for wallet {w} is missing from this device."
  | .alreadyExists w => some s!"This device already contains a protected key for wallet {w}."
  | .malformedSecret => some "The protected wallet key is damaged or has an unsupported format."
  | .unsupportedSecretVersion _ =>
    some "This wallet key uses an unsupported format version. Keep the key and open it with compatible wallet software."
  | .keychain s =>
    if s == errSecUserCanceled then some "Unlocking the wallet key was cancelled."
    else if s == errSecAuthFailed then some "The device did not confirm it was you, so the wallet key stays locked."
    else if s == errSecInteractionNotAllowed then
      some "The wallet key can only be unlocked while Winnow is on screen and the device is unlocked."
    else none

/-- The signing secret of a wallet, as held by a `KeyStore`. -/
inductive WalletSecret where
  /-- BIP39 mnemonic sentence (single spaces, checksummed). -/
  | mnemonic (words : String)
  /-- BIP32 master extended private key, Base58Check (xprv/tprv). -/
  | masterKey (xprv : String)
  /-- An account extended private key at the descriptor's origin, with the master fingerprint supplied
  separately (a child key records its parent's fingerprint, not the master's). -/
  | accountKey (xprv : String) (masterFingerprint : UInt32)
  deriving Repr, DecidableEq, Inhabited

namespace WalletSecret

def accountPrefix : String := "account/"
def accountHeader : String := "account/1"

def hex8 (n : UInt32) : String :=
  let h := String.ofList (Nat.toDigits 16 n.toNat)
  String.ofList (List.replicate (8 - h.length) '0') ++ h

/-- Tagged text: the legacy `mnemonic` / `xprv` header and payload, or `account/1`, an eight-digit
lowercase master fingerprint, and an xprv. -/
def serialized : WalletSecret → ByteArray
  | .mnemonic w => ("mnemonic\n" ++ w).toUTF8
  | .masterKey x => ("xprv\n" ++ x).toUTF8
  | .accountKey x fp => (accountHeader ++ "\n" ++ hex8 fp ++ "\n" ++ x).toUTF8

def decodeAccount (lines : List String) : Except KeyStoreError WalletSecret := do
  let [_, fp, xprv] := lines | throw .malformedSecret
  let bytes := fp.toUTF8.toList
  unless bytes.length == 8 && bytes.all (fun b => (48 ≤ b && b ≤ 57) || (97 ≤ b && b ≤ 102)) do throw .malformedSecret
  let value := bytes.foldl (fun acc b => acc * 16 + (if b ≤ 57 then b.toNat - 48 else b.toNat - 87)) 0
  return .accountKey xprv value.toUInt32

/-- `WalletSecret(serialized:)`: lossy UTF-8, lines split as Swift `Character`s (so `"\r\n"` does not
end a line). A header `account/<digits>` other than this build's `account/1` is an unsupported version,
reported by its bounded label (at most eight digits) alone; any other `account/…` header is damage. -/
def parse (b : ByteArray) : Except KeyStoreError WalletSecret := do
  let lines := Unicode.splitCharacters (Unicode.decodeUTF8Lossy b) '\n'
  let some first := lines.head? | throw .malformedSecret
  if first == "mnemonic" && lines.length == 2 then return .mnemonic lines[1]!
  if first == "xprv" && lines.length == 2 then return .masterKey lines[1]!
  if first == accountHeader then return ← decodeAccount lines
  if first.startsWith accountPrefix then
    let version := String.ofList (((first.toList.drop accountPrefix.length).takeWhile fun c => '0' ≤ c && c ≤ '9').take 8)
    if version.isEmpty || accountPrefix ++ version == accountHeader then throw .malformedSecret
    throw (.unsupportedSecretVersion (accountPrefix ++ version))
  throw .malformedSecret

end WalletSecret

/-- Secret storage for wallets, keyed by wallet ID; secrets stay on the device. -/
structure KeyStore (m : Type → Type) [Monad m] where
  /-- Stores `secret` under `walletID`; `alreadyExists` if occupied. -/
  store : WalletSecret → String → ExceptT KeyStoreError m Unit
  /-- Loads the secret for `walletID`; `notFound` if absent. -/
  load : String → ExceptT KeyStoreError m WalletSecret
  /-- Deletes the secret for `walletID`; deleting an absent ID is a no-op. -/
  delete : String → ExceptT KeyStoreError m Unit
  /-- Brings a secret stored by an earlier version up to the store's current protection; whether
  anything changed. Stores with one notion of protection have nothing to do. -/
  upgradeProtection : String → ExceptT KeyStoreError m Bool := fun _ => pure false
  /-- The item under `id` as stored, whatever wrote it (the Swift app kept raw bytes where this one keeps
  text); none if absent. Stores that hold only secrets have none to show. -/
  loadBytes : String → ExceptT KeyStoreError m (Option ByteArray) := fun _ => pure none
  /-- Keeps `bytes` under `id` as they are; `alreadyExists` if occupied. -/
  storeBytes : ByteArray → String → ExceptT KeyStoreError m Unit := fun _ id => throw (.alreadyExists id)

/-- The contents of an in-memory store. Swift dictionary keys compare by canonical equivalence, so IDs
are kept in NFD. -/
abbrev InMemorySecrets := Std.HashMap String WalletSecret

/-- An in-memory `KeyStore` over a state of secrets (not persisted). -/
def InMemoryKeyStore {m : Type → Type} [Monad m] [MonadStateOf InMemorySecrets m] : KeyStore m where
  store secret id := do
    let k := Unicode.nfd id
    if (← (get : m InMemorySecrets)).contains k then throw (.alreadyExists id)
    modify (m := m) (σ := InMemorySecrets) (·.insert k secret)
  load id := do
    match (← (get : m InMemorySecrets))[Unicode.nfd id]? with
    | some s => pure s
    | none => throw (.notFound id)
  delete id := modify (m := m) (σ := InMemorySecrets) (·.erase (Unicode.nfd id))

end Winnow.Keys
