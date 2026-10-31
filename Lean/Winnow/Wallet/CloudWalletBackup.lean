import Winnow.Wallet.Wallet
import Winnow.Crypto.AESGCM
import Std.Time

/-! # The encrypted iCloud recovery copy (`Sources/WinnowApp/CloudWalletBackup.swift`, upstream d2ca878)

A cloud backup is the import bundle split in two AES-256-GCM boxes under a random wrapping key (which
travels through iCloud Keychain; the file holds only authenticated ciphertext): the recovery words, and
the bundle without them plus any app-owned data. Automatic updates re-seal the wallet box and keep the
phrase box as it was, so they never read the signing key again.

Byte layout, as Swift's `JSONEncoder()` writes it (Lean writes sorted keys, Swift its own order; both read
either): `{"id": UUID, "network", "savedAt": seconds since 2001 as a double, "sealedPhrase": base64,
"sealedWallet": base64, "version": 1|2}`. Each box is CryptoKit's `combined` (nonce ‖ ciphertext ‖ tag),
authenticated with `Winnow cloud backup v1|<UUID, upper case>|<network>|<purpose>` where the purpose is
`phrase`, or `wallet-` and Swift's `description` of `savedAt` as seconds since 1970. Version 2 seals
`{"appState": base64?, "bundle": {…}}`; version 1 sealed the bundle's `serialized()` text alone.

Bounds: the file 32 MiB, the app data 10 MiB, the phrase box 1 KiB. Every restore runs the ordinary
importer over the result with key storage that keeps nothing (`ValidationKeys`), so a bad descriptor,
coin or key fails here, before the caller touches the real key store or wallet files.

`CloudBackupContents` (`CloudAppState.swift`) and its `digest` (`CloudBackupController.digest`): the
bundle without its words and the app data, sorted-key JSON, SHA-256 — what decides whether an automatic
update has anything new to upload. -/

namespace Winnow
open SwiftJSON Keys

namespace UUIDText

private def hexOf (c : Char) : Option Nat :=
  if '0' ≤ c && c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c && c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else none

/-- `UUID(uuidString:)` then `.uuidString`: the 8-4-4-4-12 hex form in either case, rendered upper case. -/
def canonical? (s : String) : Option String := do
  let cs := s.toList
  unless cs.length == 36 do none
  for (c, i) in cs.zipIdx do
    if i == 8 || i == 13 || i == 18 || i == 23 then
      unless c == '-' do none
    else
      discard <| hexOf c
  return String.ofList (cs.map Char.toUpper)

/-- A random (version 4) UUID, as `UUID().uuidString`. -/
def random : IO String := do
  let b ← IO.getRandomBytes 16
  let b := (b.set! 6 ((b[6]! &&& 0x0f) ||| 0x40)).set! 8 ((b[8]! &&& 0x3f) ||| 0x80)
  let h := (hex b).toUpper
  return s!"{h.take 8}-{(h.drop 8).take 4}-{(h.drop 12).take 4}-{(h.drop 16).take 4}-{h.drop 20}"

end UUIDText

/-- `Date()` as seconds since 2001-01-01 (Foundation's reference date). -/
def referenceDateNow : IO Float := do
  let ns := (← Std.Time.Timestamp.now).toNanosecondsSinceUnixEpoch.val
  return Float.ofInt ns / 1e9 - 978_307_200

/-- `CloudBackupContents`: what an iCloud backup carries. -/
structure CloudBackupContents where
  bundle : ImportBundle
  appState : Option ByteArray := none
  deriving Inhabited, BEq

namespace CloudBackupContents

def toJV (c : CloudBackupContents) : JV := obj [("bundle", some c.bundle.toJV), ("appState", c.appState.map ofData)]

/-- `CloudBackupController.digest`: SHA-256 of the sorted-key JSON of the contents without the words. -/
def digest (c : CloudBackupContents) : ByteArray :=
  sha256 (write ({ c with bundle := { c.bundle with mnemonic := none } }).toJV).toUTF8

end CloudBackupContents

structure CloudWalletBackup where
  version : Int
  /-- Upper-case UUID text. -/
  id : String
  network : String
  /-- Seconds since 2001-01-01 (`Date`'s encoding). -/
  savedAt : Float
  sealedPhrase : ByteArray
  sealedWallet : ByteArray
  deriving Inhabited

namespace CloudWalletBackup

def maximumBytes : Nat := 32 * 1024 * 1024
def maximumAppStateBytes : Nat := 10 * 1024 * 1024
def maximumSealedPhraseBytes : Nat := 1024

/-- `ValidationKeys`: the normal importer as a validation pass, keeping no key. -/
def validationKeys : KeyStore IO where
  store _ _ := pure ()
  load id := throw (.notFound id)
  delete _ := pure ()

def invalid {α} (reason : String) : WM α := throw (.wallet (.invalidBundle reason))

/-- The additional data every box is authenticated with. -/
def context (id network purpose : String) : ByteArray :=
  s!"Winnow cloud backup v1|{id}|{network}|{purpose}".toUTF8

/-- The wallet box's purpose: `wallet-` and `savedAt.timeIntervalSince1970` as Swift prints it. -/
def walletPurpose (savedAt : Float) : String := "wallet-" ++ SwiftDouble.description (savedAt + 978_307_200)

def aes {α} (r : Except AESGCM.Error α) : WM α :=
  match r with | .ok a => pure a | .error e => throw (.named e.name)

def sealed (key plaintext aad : ByteArray) : WM ByteArray := do
  let box ← aes (← AESGCM.sealRandom key plaintext aad)
  let some combined := box.combined | throw (.named "incorrectParameterSize")
  return combined

/-- The sealed `State`: `{"appState"?, "bundle"}`. -/
def stateJV (bundle : ImportBundle) (appState : Option ByteArray) : JV :=
  obj [("bundle", some bundle.toJV), ("appState", appState.map ofData)]

def bundleFailure (e : ImportBundle.Failure) : WalletFailure :=
  match e with | .wallet w => .wallet w | .decoding n => .named n

private def make (bundle : ImportBundle) (appState : Option ByteArray) (id : String) (key : ByteArray)
    (savedAt : Float) (phrase : ByteArray) : WM CloudWalletBackup := do
  let publicBundle := { bundle with mnemonic := none }
  match ImportBundle.decode publicBundle.serialized with
  | .ok _ => pure ()
  | .error e => throw (bundleFailure e)
  unless (appState.map (·.size)).getD 0 ≤ maximumAppStateBytes do invalid "cloud app data is too large"
  let state := (write (stateJV publicBundle appState)).toUTF8
  let wallet ← sealed key state (context id bundle.network (walletPurpose savedAt))
  return { version := 2, id, network := bundle.network, savedAt, sealedPhrase := phrase, sealedWallet := wallet }

/-- `create(bundle:appState:id:key:savedAt:)`: the bundle must carry its words, and import. -/
def create (bundle : ImportBundle) (key : ByteArray) (appState : Option ByteArray := none) (id : Option String := none)
    (savedAt : Option Float := none) : WM CloudWalletBackup := do
  let some words := bundle.mnemonic | throw (.wallet .mnemonicUnavailable)
  WM.liftE (·.name) (BIP39.validate words)
  discard <| Wallet.importing bundle validationKeys
  let id ← match id with | some i => pure i | none => WM.io UUIDText.random
  let savedAt ← match savedAt with | some d => pure d | none => WM.io referenceDateNow
  let phrase ← sealed key words.toUTF8 (context id bundle.network "phrase")
  make bundle appState id key savedAt phrase

/-- The opened wallet box (`state(key:)`). -/
def state (b : CloudWalletBackup) (key : ByteArray) : WM (ImportBundle × Option ByteArray) := do
  unless b.version == 1 || b.version == 2 do invalid "unsupported cloud backup"
  let data ← aes (AESGCM.openCombined key b.sealedWallet (context b.id b.network (walletPurpose b.savedAt)))
  let (bundle, appState) ← if b.version == 1 then
      match ImportBundle.decodeData data with
      | .ok bundle => pure (bundle, none)
      | .error e => throw (bundleFailure e)
    else do
      let some text := String.fromUTF8? data | throw (.named "dataCorrupted")
      let decoded : D (ImportBundle × Option ByteArray) := decodeText text fun v => do
        let kvs ← asObject v
        return (← SwiftJSON.key kvs "bundle" ImportBundle.ofJV, ← keyIfPresent kvs "appState" asData)
      let (bundle, appState) ← match decoded with
        | .ok r => pure r
        | .error e => throw (.named e)
      match ImportBundle.decode bundle.serialized with
      | .ok _ => pure ()
      | .error e => throw (bundleFailure e)
      pure (bundle, appState)
  unless bundle.network == b.network && bundle.mnemonic.isNone &&
      (appState.map (·.size)).getD 0 ≤ maximumAppStateBytes do
    invalid "cloud backup identity does not match"
  return (bundle, appState)

/-- `updating(bundle:appState:key:savedAt:)`: the same wallet (network and descriptor), the phrase box
kept as it is, the app data kept unless replaced. -/
def updating (b : CloudWalletBackup) (bundle : ImportBundle) (key : ByteArray) (appState : Option ByteArray := none)
    (savedAt : Option Float := none) : WM CloudWalletBackup := do
  let (previous, previousAppState) ← b.state key
  unless bundle.network == b.network && bundle.descriptor == previous.descriptor do throw (.wallet .descriptorMismatch)
  let savedAt ← match savedAt with | some d => pure d | none => WM.io referenceDateNow
  make bundle (appState <|> previousAppState) b.id key savedAt b.sealedPhrase

/-- `restoredBundle(key:)`: the bundle with its words back, validated by a full import. -/
def restoredBundle (b : CloudWalletBackup) (key : ByteArray) : WM ImportBundle := do
  let (bundle, _) ← b.state key
  let words ← aes (AESGCM.openCombined key b.sealedPhrase (context b.id b.network "phrase"))
  let some mnemonic := String.fromUTF8? words | invalid "invalid cloud recovery words"
  WM.liftE (·.name) (BIP39.validate mnemonic)
  let bundle := { bundle with mnemonic := some mnemonic }
  discard <| Wallet.importing bundle validationKeys
  return bundle

/-- `restoredAppState(key:)`: inside the authenticated wallet box, so it cannot be stripped; older copies
have none. -/
def restoredAppState (b : CloudWalletBackup) (key : ByteArray) : WM (Option ByteArray) := do
  return (← b.state key).2

def toJV (b : CloudWalletBackup) : JV :=
  .obj #[("version", ofInt b.version), ("id", .str b.id), ("network", .str b.network), ("savedAt", ofDouble b.savedAt),
         ("sealedPhrase", ofData b.sealedPhrase), ("sealedWallet", ofData b.sealedWallet)]

/-- `encoded()`. -/
def encoded (b : CloudWalletBackup) : WM ByteArray := do
  let data := (write b.toJV).toUTF8
  unless data.size ≤ maximumBytes do invalid "cloud backup is too large"
  return data

/-- `decode(_:)`: the size first, then the fields (every one required, `id` a UUID), then the version,
network and phrase-box bounds. -/
def decode (data : ByteArray) : WM CloudWalletBackup := do
  unless data.size ≤ maximumBytes do invalid "cloud backup is too large"
  let some text := String.fromUTF8? data | throw (.named "dataCorrupted")
  let decoded := decodeText text fun v => do
    let kvs ← asObject v
    let version ← key kvs "version" asInt
    let id ← key kvs "id" fun v => do
      match UUIDText.canonical? (← asString v) with | some u => pure u | none => dataCorrupted
    let network ← key kvs "network" asString
    let savedAt ← key kvs "savedAt" asDouble
    let sealedPhrase ← key kvs "sealedPhrase" asData
    let sealedWallet ← key kvs "sealedWallet" asData
    return ({ version, id, network, savedAt, sealedPhrase, sealedWallet } : CloudWalletBackup)
  let b ← match decoded with | .ok b => pure b | .error e => throw (.named e)
  unless (b.version == 1 || b.version == 2) && (Tx.BitcoinNetwork.ofString? b.network).isSome &&
      b.sealedPhrase.size ≤ maximumSealedPhraseBytes do
    invalid "unsupported cloud backup"
  return b

end CloudWalletBackup
end Winnow
