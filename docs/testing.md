# Testing the Lean app

Winnow 0.9.x is written in Lean 4. This guide describes how this repository's
app is tested and what its journey media show. The Swift app's suites
(WalletCoreTests, AppTests, the single signet journey) ended with 0.8.13; their
history stays in [winnowwallet/winnow](https://github.com/winnowwallet/winnow).
[PORT.md](../PORT.md) lists how each ported part is verified, and the
[script index](../scripts/README.md) describes the helpers named below.

## CI

Every pull request that is ready for review and changes more than the docs (`*.md`,
`docs/`) runs LeanNative's reusable `ios-app` workflow
([`.github/workflows/ci.yml`](../.github/workflows/ci.yml)) on GitHub's hosted macOS runners,
and so does main: on every push, and by hand (after a push whose run failed, or
a force-push, which starts no run, before tagging). Every run is the same full run, and
`release.yml` looks for one on the tag's tree that is not a pull request's.
Three jobs start at once, and each builds the Lean from the cache.

| Job | What it runs |
| --- | --- |
| `lean` | Builds `Lean/` and `LeanApp/`, which checks every proof, and the test executables; imports the census peer list (`scripts/import-census`). Then, all at the same time: `census-check` on that list, the scripts' unit tests (`scripts/tests`), `multisig-test`, `ledger-test`, `silent-payment-test`, `crypto-test`, `records-test`, `multisig-app-test`, `ledger-transport-test`, `cloud-backup-test`, and `scripts/ci-regtest`'s three suites as three lines, each against its own disposable regtest Bitcoin Core (the pinned release `scripts/install-bitcoin` downloads): `io-test`, `backend-test` and `multisig-differential` (`MULTISIG_CASES`, 6); and the six journeys headless against the app itself (LeanNative's `wire-journey`). |
| `app` (two at once) | The same build and import; the Debug simulator build, checked for Swift; the UI journeys split in two (`ui-journey-shards`: create-receive-send and the 2-of-3 on one runner; Ledger, census and silent payments on the other). |
| `media` | Once both parts pass: their evidence joined into the `journey-media` artifact (one video, the journeys in order). |
| `release` | The same build and import; the Debug and Release simulator builds and the Release device build, each checked for Swift; the test-mode check. |

The test-mode check (LeanNative's `test-mode-check`, set by `ci.yml`'s
`test-mode-env`) launches both simulator builds with test mode's environment:
Debug must start the test run and journal it, Release must ignore it and boot
into its ordinary storage.

## The six journeys

The UI journeys are Lean (`LeanApp/Journeys.lean`), run on the Mac. Each step
is one command to LeanNative's journey driver, the one XCUITest in the app's UI
test target; each check is Lean, against the node. Each journey launches the
app in test mode on an iPhone Duo simulator against a regtest node, finds
controls by the identifiers the views give them, and checks the app's results
against the node.

- `createReceiveSendConfirm`: create a wallet, receive from the node,
  review and send a payment the node accepts, see it confirm.
- `ledgerPairVerifySpend`: pair test mode's simulated Ledger, have it
  verify the receive address, and spend with the phone's and the Ledger's
  signatures.
- `multisigTwoOfThreeWithRecovery`: a 2-of-3 with two Bitcoin Core
  wallets, built in the app. The first address is Core's; the phone and both
  Cores sign, and Core accepts a witness with exactly two signatures. After the
  one-day delay the phone alone spends on the recovery path.
- `shippedCensus`: the census peer list the build ships shows in Settings
  on mainnet.
- `silentPaymentSend`: pay a BIP352 code. The node's transaction pays the
  one output that backend-test's receiver, written from the BIP's receiving
  side, finds, and the receipt shows its address.
- `feeBumpReplaceConfirm`: send at a low rate (an override under the node's
  relay floor resolves to the floor first), then bump the fee from the
  unconfirmed payment's screen. Core checks the replacement: the same coins,
  the same payment, a higher fee, the original gone from the mempool, and
  the replacement is the one that confirms. The Transactions list shows it
  confirmed with its fee and the original's row marked replaced.
- `spentElsewhere`: the same recovery phrase, in a Core wallet, spends the
  phone's coins. A review whose coin has gone fails when signed, on the Send
  screen, which works again. Then the phone pays with a coin the node has
  already seen spent at a higher fee: the node requests the transaction and
  refuses it. Peers never say so, so the phone reports it as sent, and it
  finds out from the block: Send and the Transactions row say replaced, the
  balance drops and the fee bump goes.

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
scripts/journeys                             # the UI journeys against a regtest fixture
```

`scripts/journeys` runs the journeys as CI does, on a throwaway simulator
unless `UI_SIMULATOR` names one, and keeps the result bundle, a screen
recording, the screenshots, `journeys.json` (each journey's result and time)
and the app's test-mode journals in `LeanApp/ios/build/ui-journey`. Name
journeys to run only those, for example
`scripts/journeys createReceiveSendConfirm`; `scripts/journeys --wire` runs
them headless against the app itself, in under a minute, into
`LeanApp/build/wire-journeys`.
Tests find Bitcoin Core through `WINNOW_BITCOIND` and `WINNOW_BITCOIN_CLI`,
Homebrew or the PATH; `scripts/ci-regtest` uses the pinned release that
`scripts/install-bitcoin` downloads.

## The journey media

After the journeys, LeanNative's `journey-media` (`ci.yml`'s `journey-media`
input, with the website's names as its options) turns the run into the
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
