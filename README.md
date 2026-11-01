# Winnow

Winnow is a Bitcoin wallet for iPhone and iPad, also available on Apple silicon
Mac as an iPad app. It receives and sends bitcoin and saves recipients. This
build signs with this phone's key, alone or as one signer of a k-of-n multisig
account. It is written in Lean 4: the wallet, the networking and the app's
model, update and view, compiled to C and rendered by LeanNative's generic native
shell; the curve arithmetic behind every signature is the proven secp256k1 in
`Lean/Secp`.

[App Store](https://apps.apple.com/app/id6801502501) ·
[TestFlight](https://testflight.apple.com/join/83djpNE7) ·
[User guides](https://winnowwallet.com) ·
[Report a bug](https://github.com/winnowwallet/winnow/issues)

> **Port status.** This branch brings the Lean port up to upstream 0.8.13 and the
> Ledger signer (winnowwallet/winnow#255). The sections below describe that
> version; [PORT.md](PORT.md) lists what the Lean code has reached so far and how
> each part is verified.


## Using the wallet

Winnow starts on mainnet in Simple mode. One screen holds your balance,
Receive, Send, activity and backup status. Open a payment to
save its recipient; choose saved recipients from the Send form.

Advanced mode adds Wallet, Send and Settings tabs, with signet, manual peers,
fee controls and recovery words. Switching modes keeps your wallet and
settings. Use signet and test funds when trying a development build.

Advanced mode adds raw k-of-n multisig accounts: a
`tr(NUMS, sortedmulti_a(k, …))` descriptor in, addresses and PSBTs out, signed
by any k signers in any order with no rounds between them. "New multisig
account" builds one from this phone, other Winnows' keys and a Ledger, for
example a 2-of-3 of two phones and a Ledger, with an optional recovery path: a
coin that has not moved for a chosen number of blocks can then be spent by
fewer of the same signers, or by a separate recovery key. A Ledger (Bitcoin
app 2.1.2 or later; 2.2.1 for a recovery path) can be a signer: Winnow pairs with it
over Bluetooth, registers the account on it, and asks it to sign after it shows
the payment on its own screen ([Ledger signer](Lean/Winnow/Ledger)).
There are no MuSig2 accounts, cosigner cards or shared-savings screens. A backup carrying a MuSig2
account from the shared-account Winnow is refused rather than restored without
those funds.

## Connections and privacy

Winnow connects to Bitcoin peers and matches compact block filters on your
device. It does not send your address watch list to a wallet-history server.
Direct peers can still observe your IP address, requests and relay traffic.
The app syncs while open and during short background checks scheduled by iOS;
new payments may appear at the next sync.

You can use your own filter-serving node or route peer connections through Tor
and I2P SOCKS gateways on your Tailscale network. Winnow bundles no Tor or I2P
client. See [peer gateway setup](docs/peer-gateways.md). Explorer links open an
external website after a privacy warning; they do not supply wallet balances.

## Backups

Keep a current manual backup file and your recovery words. The default file
excludes the words and restores a watch-only wallet. To restore signing through
the file-import screen, the file must include the recovery phrase; that screen
has no separate word entry. Winnow scans forward from a backup's recorded
height, so words alone do not reconstruct its past transaction history.

Automatic iCloud backup is enabled by default when available. It saves an
encrypted copy containing this phone's signing secret and wallet state. A
successful save date confirms an upload. Keep the manual file and words as
well. The
[backup guide](docs/import.html) explains the formats and their limits.

## Layout

- `Lean/`: the wallet in Lean 4 (`Winnow/`): keys, transactions, PSBTs, descriptors, k-of-n
  multisig accounts, silent payments, the Ledger signer, the wallet, compact-filter sync, peers, mempool windows and the broadcaster, over libuv TCP.
  `Secp/` is the proven secp256k1. `IOTest.lean` (`io-test`) runs the network layer against a disposable
  regtest bitcoind.
- `LeanApp/`: the app: `WinnowApp/` holds the model, update, views and commands (Elm-style, LeanNative),
  `WinnowApp/Real/` the backend, `WinnowApp/E2E.lean` the Debug-only test mode, `WinnowApp/Project.lean`
  the app's manifest: LeanNative generates the Xcode project from it (`lake exe ios-project` writes the XcodeGen
  spec) and refuses a capability the app uses without its usage text or entitlement. `ios/` keeps only the
  icon and the UI tests. The project links the Lean-generated C with LeanNative's native shell (renderer, C shim, capabilities:
  Keychain, device authentication, clipboard, HTTPS, paths). The shell is Objective-C printed from Lean
  at build time into `ios/build/native-shell/`, never checked in; the app compiles no Swift at all.
- `docs/`: the website and the papers the app bundles.
- [PORT.md](PORT.md): how the port was done and verified, and what differs from the Swift original
  (removed from this tree; it remains in the history before this port).

## Build & test

```sh
cd LeanApp
lake build backend-test records-test        # Lean toolchain leanprover/lean4:v4.35.0 (elan)
./.lake/build/bin/backend-test               # end to end against a fresh regtest bitcoind
./.lake/build/bin/records-test
cd ..
scripts/build-ios Debug                      # the app for the simulator, from a clean checkout
scripts/ui-journeys                          # the UI journeys (Lean) against a regtest fixture
```

LeanApp pins the LeanNative framework by git (`LeanApp/lakefile.toml`); `lake` fetches it into
`LeanApp/.lake/packages/leannative` (its Lake package keeps the name it had as LeanNative).
`scripts/build-ios <Debug|Release> [iossim|ios]` runs LeanNative's
`framework/native/ci/build-ios` with Winnow's names: it builds WinnowApp, gathers the generated C, prints the
Objective-C shell, writes the Xcode project from the manifest (XcodeGen 2.46.0) and builds it. Simulator builds are ad-hoc signed (an unsigned app has no
Keychain entitlement). `backend-test --fixture <dir>` leaves a funded regtest node running for manual
simulator runs. Tests find Bitcoin Core through `WINNOW_BITCOIND` / `WINNOW_BITCOIN_CLI`, Homebrew or the
PATH; CI sets the first two to the pinned release `scripts/install-bitcoin` downloads.

### UI tests

The UI journeys are Lean (`LeanApp/Journeys.lean`, the `journeys` executable), run on the Mac: each step is
one command to LeanNative's journey driver (`LNDriver`, the one XCUITest in the app's UI test target), each
check is Lean against the node. Each launches the app in test mode on the regtest node of
`backend-test --fixture`, finds controls by the ids the views give them (`Html.identified`, the shell's
`accessibilityIdentifier`) and checks the app against the node:

- `createReceiveSendConfirm`: create a wallet, receive from the node, review and send a payment the
  node accepts, see it confirm;
- `multisigTwoOfThreeWithRecovery`: a 2-of-3 with two Bitcoin Core wallets, built in the app; the
  first address is Core's, the phone and both Cores sign, Core accepts a witness with exactly two
  signatures; after the one-day delay the phone alone spends on the recovery path;
- `ledgerPairVerifySpend`: pair test mode's simulated Ledger, have it verify the receive address,
  and spend with the phone's and the Ledger's signatures;
- `shippedCensus`: the census peer list the build ships shows in Settings on mainnet;
- `silentPaymentSend`: pay a BIP352 code; the node's transaction pays the one output backend-test's
  receiver (written from the BIP's receiving side) finds, and the receipt shows its address.

They run two ways. `scripts/wire-journeys` runs them against the app itself, headless: the journeys executable
runs the app as a child of itself with a fake shell (LeanNative's `LEANNATIVE_DRIVER=wire`: a Keychain in a file,
paths under the evidence directory, no network, no Bluetooth) and finds each element in the app's view tree, so
the five take under a minute against the fixture's node, with no simulator; CI runs this in the `lean` job. What
it does not test is the renderer and real touches, which the simulator run does.
`scripts/ui-journeys` runs them as CI does in the `app` job: LeanNative's `ui-tests` on a throwaway simulator (or `UI_SIMULATOR`)
with the journeys as `UI_JOURNEY`, and `scripts/ui-fixture` starting the node before and collecting the app's
test-mode journals after; it keeps the result bundle, a screen recording, the screenshots, `journeys.json`
(each journey's result and time) and the journals. `UI_JOURNEYS="silentPaymentSend" scripts/ui-journeys` runs
only the journeys named.

### CI and TestFlight

`.github/workflows/ci.yml` calls LeanNative's reusable `ios-app` workflow on every pull request that is ready for
review and changes more than the docs, on a push to main that does, nightly on main when its commit has not passed
yet, and by hand, in two jobs on GitHub's own macOS runners (free for a public repository; a fork's pull request
gets them too) that start at once and each build the Lean from the cache; every long step prints its progress as it
goes. Every run is the same, full run:

| job | what |
|---|---|
| `lean` | builds `Lean/` and `LeanApp/` (every proof) and the test executables, imports the census list, then runs at the same time: census-check on that list, the scripts' tests, multisig-test, ledger-test, silent-payment-test, crypto-test, records-test, multisig-app-test, ledger-transport-test, and `scripts/ci-regtest`'s three suites as three lines, each against its own disposable regtest bitcoind: io-test, backend-test and multisig-differential (6 random cases) |
| `app` | the same build and census import; Debug and Release for the simulator and Release for devices, each checked for Swift, and `verify-release-no-test-mode`; all five UI journeys (`scripts/ui-fixture` as the hooks); the website's media (`scripts/journey-media`) |

`.github/workflows/release.yml`: a `vMAJOR.MINOR.PATCH` tag finds a successful full CI run (main's push, nightly
or by hand: not a pull request's) on the same tree, then archives the app as
`com.btcswift.app` (team 2858MX5336, the identity of the Swift app it replaces), checks the archive and
the exported IPA (`verify-signed-archive`, `verify-exported-ipa`, `check-no-swift`), uploads it and adds
it to TestFlight's internal group (`scripts/testflight.sh`, whose App Store Connect token comes from
`scripts/asc-jwt`). It uses the repository's secrets `ASC_KEY_ID`, `ASC_ISSUER_ID`, `ASC_PRIVATE_KEY`,
`DEV_CERT_P12` and `DEV_CERT_P12_PASSWORD`. Dispatched by hand it runs the gates only.

The public website is maintained in
[winnowwallet/website](https://github.com/winnowwallet/website). This repository
contains the app's offline guides and engineering records. The
[roadmap](https://winnowwallet.com/roadmap) tracks proposed work separately from current behavior.

## License

Winnow is available under the [MIT License](LICENSE).
