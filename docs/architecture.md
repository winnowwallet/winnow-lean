# Wallet architecture

Winnow is written in Lean 4 (`leanprover/lean4:v4.35.0`) as two Lake packages.
[`Lean/`](../Lean/lakefile.toml) is the wallet: the curve, keys, transactions,
networking and wallet state. [`LeanApp/`](../LeanApp/lakefile.toml) is the app:
its model, update, views and backend, and the UI journeys. Lean's compiler turns
both into C, which is linked with Lean's runtime, libuv, GMP and LeanNative's
shell. The tree holds no Swift. [PORT.md](../PORT.md) records how each part was
ported and checked.

## Source ownership

| Component | Holds | Depends on |
| --- | --- | --- |
| [`Secp`](../Lean/Secp.lean) | The curve as specified ([`Secp/Curve/Spec.lean`](../Lean/Secp/Curve/Spec.lean)), signing as BIP340 and ECDSA give it ([`Secp/Signing.lean`](../Lean/Secp/Signing.lean)), bytes, SHA-256 and DER. Its bytes, SHA-256 and DER code also runs in the app; its curve and signing are what `SecpCt` is proved against. | Lean only |
| [`SecpCt`](../Lean/SecpCt.lean) | secp256k1 as it runs, the only implementation: field, scalars, points, keys, tweaks, BIP340 and ECDSA on machine words, each proved against `Secp` ([`SecpCt/Gate.lean`](../Lean/SecpCt/Gate.lean)) | `Secp` |
| [`WinnowCore`](../Lean/WinnowCore.lean) | What transaction review needs: hashes, BIP32, transactions, PSBTs, sighashes, descriptors, spend review, the header chain. No seed phrases, coin selection or I/O. [`scripts/check-core`](../scripts/check-core) holds its imports to a list. | `SecpCt`'s code and `Secp`'s bytes and SHA-256, none of the proofs |
| [`Winnow`](../Lean/Winnow.lean) | The wallet: [`Crypto`](../Lean/Winnow/Crypto.lean), [`Keys`](../Lean/Winnow/Keys.lean), [`Tx`](../Lean/Winnow/Tx.lean), [`Net`](../Lean/Winnow/Net.lean) (protocol decisions without a socket), [`IO`](../Lean/Winnow/IO.lean) (peers over Lean's libuv TCP), [`Wallet`](../Lean/Winnow/Wallet.lean) and [`Ledger`](../Lean/Winnow/Ledger.lean) | `WinnowCore` |
| [`TestKit`](../Lean/TestKit.lean) | What the test executables share: the tally, test keys, a regtest bitcoind, a fake peer, the fuzz harness | `Winnow`; tests only |
| [`WinnowApp`](../LeanApp/WinnowApp/Main.lean) | The app: [Model](../LeanApp/WinnowApp/Model.lean), [Update](../LeanApp/WinnowApp/Update.lean), [View](../LeanApp/WinnowApp/View.lean) and a module per screen area; the [`Backend`](../LeanApp/WinnowApp/Backend.lean) interface and its implementation in [`Real/`](../LeanApp/WinnowApp/Real.lean) | `Winnow`, LeanNative |
| [`Journeys`](../LeanApp/Journeys.lean) | The UI journeys, as steps over [`Journeys/Screens.lean`](../LeanApp/Journeys/Screens.lean) and [`Journeys/Host.lean`](../LeanApp/Journeys/Host.lean) | `WinnowApp`, `TestKit` |

`Winnow` does not depend on the app. There is no MuSig2: a backup that carries
an account of any kind other than the two under "Accounts, people and cards" is
refused rather than restored without those funds
([`ImportBundle.lean`](../Lean/Winnow/Wallet/ImportBundle.lean)).

## The app and the shell

The app is LeanNative's native mode: `update` changes the model, `view` returns
a tree of nodes, and `perform` in [`Main.lean`](../LeanApp/WinnowApp/Main.lean)
runs commands against the backend. LeanNative is pinned by commit in
[`LeanApp/lakefile.toml`](../LeanApp/lakefile.toml); `ci.yml` and `release.yml`
name the same commit. Its shell is Objective-C on UIKit, printed from Lean at
build time into `LeanApp/ios/build/native-shell/` and never checked in.
`LeanApp/ios/` keeps only the asset catalog: the icon and the accent colour.

What only iOS can do reaches the app as a capability the manifest declares
([`Project.lean`](../LeanApp/WinnowApp/Project.lean)): device authentication,
the Keychain, the clipboard, paths, HTTPS (`http.get`), Bluetooth LE (`ble.*`),
background tasks (`bgtask.*`) and CloudKit (`cloudkit.*`). Generating the Xcode
project refuses a capability that lacks its usage text or entitlement. Test
mode ([`E2E.lean`](../LeanApp/WinnowApp/E2E.lean)) and the sample data are
inert unless the shell reports a Debug build.

## Keys

The wallet's secret is a Keychain item under the service
`org.btc-swift.wallet`, readable only on this device while it is unlocked
([`Real/Shell.lean`](../LeanApp/WinnowApp/Real/Shell.lean)). The item is
behind an access control that requires the person (Face ID, Touch ID or the
passcode), so the Keychain itself gives the secret only under an
authentication. The app asks for one (`authenticated` in `Main.lean`) before it
creates a wallet, imports or exports a recovery phrase, shows the phrase,
sends, bumps a fee, signs for a multisig account or makes a person's card. The
shell keeps that authentication for the reads of the one action and ends it
with the action; a read with none is refused, never a prompt. An item stored
by a build before this is given the access control in place when the wallet
opens. The sealed stores' keys are separate items without it, because sync
passes read them with nobody present. So is the scan private key a restored
wallet keeps while it searches for its cards
(`Wallet.cardSearchKeyID`); it finds payments and signs for nothing, and is
removed when the search ends. That iOS enforces the access control is device
evidence: a simulator's Keychain does not. Every curve operation goes through
[`Keys/Secp256k1.lean`](../Lean/Winnow/Keys/Secp256k1.lean) to `SecpCt`.
[SECURITY.md](../SECURITY.md) says what is proved, and what is and is not
claimed about timing.

## Receiving and synchronization

This is a compact-filter wallet. [`IO/Pool.lean`](../Lean/Winnow/IO/Pool.lean)
keeps a small pool of outbound peers (three by default) drawn from manual
endpoints, saved good peers, the census list and DNS seeds. The census list is
fetched at build time: [`scripts/import-census`](../scripts/import-census)
verifies its signature and writes `build/census/peers.json`, the manifest
bundles it, and the app downloads none
([`IO/Census.lean`](../Lean/Winnow/IO/Census.lean)). Headers are validated in
[`Net/HeaderChain.lean`](../Lean/Winnow/Net/HeaderChain.lean), from a checkpoint
compiled into [`Net/Params.lean`](../Lean/Winnow/Net/Params.lean) or from
genesis. [`Net/FilterSync.lean`](../Lean/Winnow/Net/FilterSync.lean) compares
filter headers across peers, verifies each filter, and checks a fetched block's
merkle root. Mempool windows ([`IO/Mempool.lean`](../Lean/Winnow/IO/Mempool.lean))
and the broadcaster ([`IO/Broadcast.lean`](../Lean/Winnow/IO/Broadcast.lean))
use the same pool.

Bitcoin P2P is plain TCP in Lean. Lean has no TLS, so every HTTPS request (DNS
seeds over DoH, explorer lookups) is the shell's `http.get` under the policy in
[`IO/Http.lean`](../Lean/Winnow/IO/Http.lean). Tor and I2P are reached only
through the user's own SOCKS gateways
([`IO/Gateways.lean`](../Lean/Winnow/IO/Gateways.lean);
[peer gateways](peer-gateways.md)). iOS may start a background check, which is
one bounded scan
([`Real/BackgroundSync.lean`](../LeanApp/WinnowApp/Real/BackgroundSync.lean)).
These checks do not establish the same view as validating every block from
genesis; the bundled [read-side guide](read-side.html) states the limits.

## Accounts, people and cards

The everyday wallet is BIP86 Taproot ([`Keys/BIP86.lean`](../Lean/Winnow/Keys/BIP86.lean),
[`Wallet/Wallet.lean`](../Lean/Winnow/Wallet/Wallet.lean)). It keeps two kinds
of multisig account ([`AnyMultisigAccount.lean`](../Lean/Winnow/Wallet/AnyMultisigAccount.lean)):

- Taproot script-path, `tr(NUMS, sortedmulti_a(k, …))`, with optional recovery
  leaves and nested members
  ([`MultisigAccount.lean`](../Lean/Winnow/Wallet/MultisigAccount.lean)). The app
  builds, signs and finalizes its spends, and a Ledger can be a signer over
  Bluetooth ([`Ledger/`](../Lean/Winnow/Ledger.lean),
  [`Real/LedgerTransport.lean`](../LeanApp/WinnowApp/Real/LedgerTransport.lean)).
- SegWit v0, `wsh(sortedmulti(k, KEY, …))`, joined from its descriptor
  ([`SegwitMultisigAccount.lean`](../Lean/Winnow/Wallet/SegwitMultisigAccount.lean)).
  The app reviews, signs with ECDSA and finalizes a PSBT someone else built. It
  does not build this account's payments, and no Ledger signs for it.

An account is more watched scripts in the same filter scan
([`Real/MultisigStore.lean`](../LeanApp/WinnowApp/Real/MultisigStore.lean)).
Saved people and receive labels are the records side of the backend
([`Real/Records.lean`](../LeanApp/WinnowApp/Real/Records.lean)); the people
file is sealed, authenticated under a key kept in the Keychain
([`Real/RecordsSeal.lean`](../LeanApp/WinnowApp/Real/RecordsSeal.lean)). A card
for one person is derived in
[`Keys/SilentPaymentPairing.lean`](../Lean/Winnow/Keys/SilentPaymentPairing.lean)
and its payments are found by the same scan; the
[proposal](out-of-band-payments.md) has the construction. Silent payments are
sent ([`Keys/SilentPayments.lean`](../Lean/Winnow/Keys/SilentPayments.lean)),
not received.

## Backup

A backup file is the import bundle
([`ImportBundle.lean`](../Lean/Winnow/Wallet/ImportBundle.lean)), with the
multisig accounts and signer list the app adds
([`Real/Wallet.lean`](../LeanApp/WinnowApp/Real/Wallet.lean)). The iCloud copy
is that bundle in two AES-256-GCM boxes under a random wrapping key
([`CloudWalletBackup.lean`](../Lean/Winnow/Wallet/CloudWalletBackup.lean)).
[`Real/CloudBackup.lean`](../LeanApp/WinnowApp/Real/CloudBackup.lean) writes it
to CloudKit's private database and keeps the wrapping key in a synchronizable
iCloud Keychain service, separate from the wallet's device-only key.
[`Real/CloudApp.lean`](../LeanApp/WinnowApp/Real/CloudApp.lean) adds saved
people, receive labels and the display name. The [backup guide](import.html)
covers the formats and their limits, and [CloudKit setup](../CloudKit/README.md)
the schema.

## Build and checks

[`scripts/build-ios`](../scripts/build-ios) builds the app from a clean
checkout, and the [script index](../scripts/README.md) lists the other entry
points. The [testing guide](testing.md) says what
[`ci.yml`](../.github/workflows/ci.yml) runs and what it does not show.
Security reports and dated evidence are under [security](security/README.md);
they apply to the revisions they identify.

The app bundles four HTML guides and their stylesheet from this directory
(`Project.lean`), so a change to one is an app change. The public website has
its own [repository](https://github.com/winnowwallet/website). The Swift app's
architecture is in [winnowwallet/winnow](https://github.com/winnowwallet/winnow).
