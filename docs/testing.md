# Testing the wallet

Use checks that exercise the changed behavior and retain the source revision,
command, environment and result. This guide maps the existing suites and CI;
it does not turn a test count, screenshot or old audit into a release guarantee.
The [architecture guide](architecture.md) explains source ownership, and the
[CI and release runbook](../.github/internal/ci-release.md) covers operations.

## Test coverage

| Suite | Exercises | Boundaries |
| --- | --- | --- |
| [BitcoinCoreTests](../Tests/BitcoinCoreTests/README.md) | Cryptographic and encoding vectors, silent payment vectors, descriptors, scripts and parser bounds | Vectors and parser checks do not demonstrate a user workflow |
| [WalletCoreTests](../Tests/WalletCoreTests/README.md) | Coin selection, fees, imports, people and contact cards, reorgs, peer behavior and synchronization | Controlled peers and fixtures cover their asserted cases |
| [AppTests](../AppTests/README.md) | Review, authorization, persistence, startup, recipients, backup state and iOS integration | Most cloud cases use in-memory stores; a simulator cannot prove device-lock enforcement |
| [UITests](../UITests/README.md) | A recorded iPhone payment journey and peer-setting persistence | No automated iPad journey or hardware-wallet matrix |
| [ToolsTests](../Tests/ToolsTests/README.md) and [fuzzing](../Tools/Fuzz/README.md) | Debugging commands, generators, parser regressions and hostile inputs | A bounded corpus or fuzz run establishes only its own executed coverage |
| [Script regressions](../scripts/tests/README.md) | CI evidence, media validation and release helpers | These check tooling rather than wallet payments |

The encrypted envelope tests are in
[AppTests/CloudWalletBackupTests.swift](../AppTests/CloudWalletBackupTests.swift).
They moved with CloudWalletBackup into the app; `swift test` does not run them.
App tests also cover backup defaults, retries, opt-out, account changes and
cancellation using injected stores.

Keep signing-policy and hostile-input regressions close to the code they test.
Descriptor changes, forged PSBT metadata, signature validation, amount bounds and storage integrity need focused assertions. A UI journey
cannot substitute for those checks.

## Run locally

Run from the repository root on macOS with Xcode and the Swift toolchain:

```sh
swift test
```

This runs the SwiftPM targets, including ToolsTests. For iOS
app tests, generate the project after importing the census:

```sh
scripts/import-census
scripts/install-xcodegen
"${RUNNER_TEMP:-${TMPDIR:-/tmp}}/winnow-xcodegen-2.46.0/xcodegen/bin/xcodegen"
WINNOW_APP_RESULTS=$(mktemp -d /tmp/winnow-app-tests-XXXXXX)
scripts/ci-app-tests "$WINNOW_APP_RESULTS"
```

The app-test script selects an installed iPhone simulator and writes its log and
`AppTests.xcresult` into that new directory. These results are separate from
SwiftPM's output. Use [the UI test setup](../UITests/README.md#run-locally) for
the signet fixture, continuous recording and journey. Local simulator runs
should be serial because they share fixture ports and an environment file.

Repository Python tooling requires Python 3.11 or later; CI uses 3.12. The macOS
system Python may be older. See [script regressions](../scripts/tests/README.md)
for their command.

Use [the script index](../scripts/README.md) for dependency checks, warning
gates, debugging smoke and evidence validation. `ci-lane` and `ci-tailnet` are
runner orchestration scripts for disposable CI machines; use the documented
local entry points on a development Mac.

## The payment journey

`WinnowAppUITests.test01CreateReceiveSendConfirm` creates a wallet, receives,
reviews, sends and confirms an ordinary payment, then a BIP352 silent payment
to a code whose receiver the test plays (Core cannot), then the multisig
account journey. A disposable private signet fixture funds the app's address,
accepts the transactions and mines confirmations. The test checks both the
app's outcomes and the node's accepted payments.

The host records one continuous video and retains checkpoint screenshots with
the test log and Xcode result bundle. Those assertions establish the result;
media helps review the interaction. This journey supplies evidence for that
flow on an iPhone simulator. Other signing orders, hardware, recovery paths
and network environments need their own checks.

## CI and reused evidence

[CI](../.github/workflows/ci.yml) selects parallel validation for same-repository
runs and a hosted fallback for fork PRs or the manual `hosted` option. Parallel
validation has five lanes: package, build, units, journey and tailnet. The build
lane publishes one Debug build; units and journey verify and use those products
on separate runners and simulators. The hosted fallback combines package, build
and app checks in one job. Fork PRs omit the signet journey and deployment
credentials. The [workflow index](../.github/workflows/README.md) lists the
lanes and retained artifacts.

The tailnet lane creates disposable Headscale clients and gateway services.
It checks discovery and routing in that controlled setup. Live Tor/I2P gateway
checks are separate manual operations; passing the simulation does not establish
public-network reachability.

[scripts/ci-validation](../scripts/ci-validation) can reuse a complete,
successful same-repository evidence bundle for matching build/test inputs,
workflow identity and validation policy, up to seven days old. It verifies the
record, file hashes, shared Debug build and media provenance. An unbundled docs
edit can match; HTML/CSS bundled in the app participates in the fingerprint.
Changed inputs, missing artifacts, invalid records or lookup errors run fresh
validation. Manual and nightly runs force fresh checks. Tag releases can reuse
eligible evidence under the same policy.

Reused evidence keeps its original tested source, run, inventory and recording;
a green reuse run does not mean the tests executed again. Inspect job
conclusions and the validation record before reporting a run as fresh. Wallet
CI retains evidence without building or deploying the separate website.

## Checks that need devices or external evidence

Simulator and in-memory tests do not establish locked-device Keychain behavior,
actual iCloud transport or iCloud Keychain synchronization. A CloudKit save date
confirms an upload, without establishing an end-to-end recovery result. Keep
manual backup and recovery-word guidance in place while physical-device
validation is outstanding.

Battery life, background scheduling in daily use, peer independence and
hardware-wallet compatibility also need measurements or explicit integration
tests. Record the devices, configuration, revision and actual result when doing
that work. Dated [security reports](security/README.md) and published recordings
retain their original scope; proposed work belongs on the
[roadmap](https://winnowwallet.com/roadmap).
