# CI and release operations

Winnow has one source tree and version train for the wallet app, SwiftPM library
products and development tools. The root `Package.swift` pins one package,
swift-secp256k1, and `Package.resolved` records its commit. The [architecture guide](../../docs/architecture.md)
explains the products; [testing](../../docs/testing.md) describes coverage and
its limits.

## Validation

[ci.yml](../workflows/ci.yml) calls ElmLean's reusable `ios-app` workflow (posix4e/elmlean,
`.github/workflows/ios-app.yml`): `build` (the Lean, once, cached), then `tests`, `extra` and `app` in
parallel, on WarpBuild Apple silicon runners. A fork's pull request gets no CI; push it to a branch here.

The rest of this file describes the Swift app's CI and is kept for its history.

Parallel build prepares Debug app/test products once and also checks an ARM64
Release build. Units and journey download the hash-checked Debug artifact and
run on separate runners and simulators. Package runs SwiftPM tests, lint,
dependency and production-warning checks, debugging smoke and provenance
generation. Journey uses a fresh disposable signet fixture. Tailnet builds a
controlled Headscale/gateway environment for routing tests; it does not verify
live public Tor or I2P access.

[Fuzz](../workflows/fuzz.yml) is a separate check with its own artifacts. Its
`smoke` job runs the fixed-seed campaign (14,000 deterministic cases) on every
pull request and main push; its `sustained-fuzz` job runs the weekly and manual
sanitizer matrix with a seed rotated from the run id, replayable through the
`replay_seed` input. See [deterministic fuzzing](../../Tools/Fuzz/README.md).
Validation evidence never includes fuzz results.

The parallel scripts currently require Xcode 26.6 build 17F113 and select iOS
26.5. Runner, runtime, architecture and test inventory are recorded in lane
evidence. Check the source and run logs when those pins change.

## Evidence and reuse

[scripts/ci-validation](../../scripts/ci-validation) verifies complete reusable
evidence for matching source inputs, workflow identity and policy. Eligible
bundles come from successful same-repository CI runs and expire after seven
days. File hashes, shared Debug product identity and normalized journey media
are checked before reuse. Unbundled docs may leave the fingerprint unchanged;
app-bundled HTML/CSS changes affect it. A lookup error or incomplete bundle
falls back to fresh validation.

Manual and nightly runs force fresh checks. Tag releases can reuse verified
evidence. Reuse preserves the original source SHA, run, test inventory and
media provenance. A successful validation job therefore establishes either
fresh checks or accepted matching evidence; inspect the record and lane
conclusions to distinguish them.

Parallel runs retain `lane-package-<run>-<attempt>`, `lane-build-…`,
`lane-units-…` and `lane-journey-…` artifacts, plus the transferred `lane-debug-…`
products. The complete record is published as `validation-<fingerprint>`.
A reuse run retains `reused-validation-<run>-<attempt>`. Hosted runs retain
`app-tests-<run>-<attempt>`, including Debug/Release logs, `units/` and,
when run, `journey/` results and recordings. Failed runs may contain only
partial evidence; inspect the original logs and xcresult conclusions.

The journey retains `NodeUI.xcresult`, test/fixture logs, `journey.mp4`, video
logs and checkpoint screenshots. Normalized media preserves the tested source
and run. Wallet CI does not build or deploy the public website.

## Release

A new stable `vMAJOR.MINOR.PATCH` tag triggers
[Release](../workflows/release.yml). The tag chooses the app marketing version;
the workflow run number chooses the build number. Existing tags stay fixed.
The app and WalletCore share those tags; no separate internal version
bump is needed.

1. Choose the intended commit and update
   [TestFlight notes](../../docs/testflight-what-to-test.txt) with the behavior
   and checks testers should exercise. Review current device-test limitations.
2. Run **Release** manually on that revision's branch and wait for success.
   Manual dispatch runs fresh validation without signing, uploading, assigning
   groups or publishing a GitHub release.
3. Create a new, unused stable tag on the reviewed commit and push that tag.
   This starts publishing after the reused CI workflow succeeds, using either
   fresh checks or eligible evidence under the policy above.
4. Inspect the Release run's selected version/build, archive checks, upload,
   processing result and TestFlight status. Keep the run URL with release notes.

The publishing job imports the newest public census before generating the
Xcode project (`scripts/import-census`: the signature is verified under the
pinned key, inconsistent clearnet peers are dropped by the census's health
record, and the app's decoder accepts the result). Its log, the
`release-census` artifact (`peers-source.txt`) and a `Peers:` line appended to
What to Test record the census commit included in the build. It uses
pinned XcodeGen 2.46.0, existing repository signing credentials and App Store
Connect configuration. Signing material stays in temporary runner storage and
is cleaned up by the workflow.

Before upload, the job checks the archive and exported IPA for the intended
identity, version, iCloud configuration and exclusion of E2E controls. It records
resolved dependencies and supply-chain metadata. After upload it waits for
processing, sets notes and assigns the internal group. It never requests
external beta distribution: a review request cannot be withdrawn, so that is a
person's decision once the internal group has used the build, made with
`scripts/testflight.sh external` and the exact version and build number, or by
dispatching TestFlight recovery with `external_review` ticked. External
**WAITING_FOR_REVIEW** or **IN_REVIEW** means Apple review is pending; a green
Release run never means external testers can install.
The final job publishes a GitHub release with SPDX and provenance artifacts.

Checkpoint maintenance is separate: `scripts/refresh-checkpoint` requires a
genesis-validated header file and a reviewed vector update. See the
[checkpoint runbook](../../Tools/Generate/README.md).

## Resume an existing upload

Use [TestFlight recovery](../workflows/testflight-recover.yml) with the exact
marketing version and build number from the original run, when processing
outlasts the release or App Store Connect fails mid-run. It waits for
processing, sets notes and assigns the internal group for that upload. It does
not rearchive or reupload the same build number, and it requests external
review only when `external_review` is ticked. Check the status it prints.

Prefer these workflows over calling `scripts/testflight.sh` without an explicit
operation: the helper defaults to `all`, which performs setup and upload.
The [script index](../../scripts/README.md#release-helpers) lists its operations.

## App Store and feedback

[App Store submission](../workflows/appstore-submit.yml) is a separate manual
operation. Attaching a build and setting notes changes App Store Connect even
when submission is disabled; use its status-only option for a read. Submission
is distinct from TestFlight distribution and Apple approval.

[TestFlight feedback](../workflows/testflight-feedback.yml) takes an `age` public
key whose private key stays with the reader. Download its encrypted
`testflight-feedback-<run>` artifact within three days and decrypt locally.
The public run logs show counts; tester comments, emails, screenshots and crash
contents must remain encrypted in retained artifacts.

## Website and offline guides

Public site sources, generation and deployment live in
[winnowwallet/website](https://github.com/winnowwallet/website). The wallet app
bundles five offline HTML guides and `site.css` from `docs/`. Review those copies
when changing guidance for an app release. See the [documentation index](../../docs/README.md).
