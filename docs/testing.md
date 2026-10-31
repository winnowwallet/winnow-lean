# Testing the Lean app

Winnow 0.9.x is written in Lean 4. This guide describes how this repository's
app is tested and what its journey media show. The Swift app's suites
(WalletCoreTests, AppTests, the single signet journey) ended with 0.8.13; their
history stays in [winnowwallet/winnow](https://github.com/winnowwallet/winnow).
[PORT.md](../PORT.md) lists how each ported part is verified, and the
[script index](../scripts/README.md) describes the helpers named below.

## CI

Every pull request runs LeanNative's reusable `ios-app` workflow
([`.github/workflows/ci.yml`](../.github/workflows/ci.yml)) on WarpBuild runners,
and so does main, nightly and by hand. A push to main does not: main only gets a
tree a pull request already passed, and `release.yml` looks for that run. Two
jobs start at once, and each builds the Lean from the cache.

| Job | What it runs |
| --- | --- |
| `lean` | Builds `Lean/` and `LeanApp/`, which checks every proof, and the test executables; imports the census peer list (`scripts/import-census`). Then, all at the same time: `census-check` on that list, the scripts' unit tests (`scripts/tests`), `multisig-test`, `ledger-test`, `silent-payment-test`, `crypto-test`, `records-test`, `multisig-app-test`, `ledger-transport-test`, and `scripts/ci-regtest` (`io-test`, `backend-test` and `multisig-differential` against a disposable regtest Bitcoin Core, the pinned release `scripts/install-bitcoin` downloads). |
| `app` | The same build and import; Debug and Release simulator builds and a Release device build, each checked for Swift; `verify-release-no-test-mode`; the UI journeys; then the `journey-media` artifact. |

`verify-release-no-test-mode` launches both simulator builds with test mode's
environment: Debug must start the test run, Release must ignore it.

## The five journeys

The UI journeys are Objective-C XCUITests (`LeanApp/ios/UITests`, target
`WinnowLeanUITests`). Each launches the app in test mode on an iPhone Duo
simulator against a regtest node, finds controls by the identifiers the views
give them, and checks the app's results against the node.

- `testCreateReceiveSendConfirm`: create a wallet, receive from the node,
  review and send a payment the node accepts, see it confirm.
- `testLedgerPairVerifySpend`: pair test mode's simulated Ledger, have it
  verify the receive address, and spend with the phone's and the Ledger's
  signatures.
- `testMultisigTwoOfThreeWithRecovery`: a 2-of-3 with two Bitcoin Core
  wallets, built in the app. The first address is Core's; the phone and both
  Cores sign, and Core accepts a witness with exactly two signatures. After the
  one-day delay the phone alone spends on the recovery path.
- `testShippedCensus`: the census peer list the build ships shows in Settings
  on mainnet.
- `testSilentPaymentSend`: pay a BIP352 code. The node's transaction pays the
  one output that backend-test's receiver, written from the BIP's receiving
  side, finds, and the receipt shows its address.

What the journeys do not cover: a physical Ledger (CI's is simulated; the
owner's Nano X co-signed a mainnet 2-of-2 on 26 October 2026 with the Swift
app), receiving silent payments (Winnow does not), live Tor and I2P gateways,
iCloud, background tasks scheduled by iOS, and iPad layouts.

## Run them locally

From the repository root, with the Lean toolchain `leanprover/lean4:v4.35.0`
(elan):

```sh
cd LeanApp
lake build backend-test records-test
./.lake/build/bin/backend-test               # end to end against a fresh regtest bitcoind
./.lake/build/bin/records-test
cd ..
scripts/build-ios Debug                      # the app for the simulator, from a clean checkout
scripts/ui-journeys                          # the UI journeys against a regtest fixture
```

`scripts/ui-journeys` runs the journeys as CI does, on a throwaway simulator
unless `UI_SIMULATOR` names one, and keeps the result bundle, a screen
recording, the screenshots and the app's test-mode journals in
`LeanApp/ios/build/ui-journey`. Pass `xcodebuild` arguments to run one, for
example
`-only-testing:WinnowLeanUITests/WinnowLeanUITests/testCreateReceiveSendConfirm`.
Tests find Bitcoin Core through `WINNOW_BITCOIND` and `WINNOW_BITCOIN_CLI`,
Homebrew or the PATH; `scripts/ci-regtest` uses the pinned release that
`scripts/install-bitcoin` downloads.

## The journey media

After the journeys, `scripts/journey-media` turns the run into the
`journey-media` artifact: the screenshots, a browser copy of the recording and
`journey-provenance.json` (the run, source commit, device, each test's result
and seconds, and each file's SHA-256).

The website ([winnowwallet/website](https://github.com/winnowwallet/website))
downloads that artifact from the newest successful `ci.yml` run on this
repository's main, checks every file against the provenance file, and builds
its homepage gallery and [recording page](https://winnowwallet.com/recording)
from it. When the fetch fails, the site publishes its committed reference media
from the Swift app instead.

The result bundle and logs are what establish a pass. The recording and
screenshots show the run; they do not replace its assertions, and they are
evidence only for the commit and device their provenance names.
