# CI and release operations

Winnow has one source tree and one version train: the wallet library (`Lean/`)
and the app (`LeanApp/`), both Lean 4, built and released by LeanNative's
reusable workflows at the commit `LeanApp/lake-manifest.json` pins. The
[architecture guide](../../docs/architecture.md) explains the parts;
[testing](../../docs/testing.md) describes coverage and its limits.

Validation, Release and Resume below describe the Lean app's workflows as of
2026-11-17. The Swift app's CI is kept at the end, under "History (Swift app)".

## Validation

[ci.yml](../workflows/ci.yml) calls LeanNative's reusable `ios-app` workflow
([LeanNative/leannative](https://github.com/LeanNative/leannative), formerly posix4e/elmlean;
`.github/workflows/ios-app.yml`), pinned to the commit `LeanApp/lake-manifest.json` pins: `lean`, `app` and `release` at once,
on GitHub's hosted Apple silicon runners (`macos-26`), a fork's pull request included. While the repository
variable `MACOS_RUNNER` is set, this repository's own branches run on that label instead (a self-hosted Mac, when
GitHub's are backed up); a fork's pull request never does.

It runs on pull requests that are ready for review and change more than the
docs, on every push to `main`, and by hand. A push to any other branch starts
no run, so a release branch's commit has a run only when CI is run by hand on
it. `media` joins the two `app` parts' recordings once both pass. The
[testing guide](../../docs/testing.md) lists what each job runs.

Fuzzing is a line of the `lean` job, seeded from the commit; see
[Fuzzing](../../docs/testing.md#fuzzing).

Each job keeps its evidence as an artifact: `lean-<run>-<attempt>`,
`app-<run>-<attempt>-part-<index>` (the journeys' result bundle, recording,
screenshots and `journeys.json` under `journey/`) and
`release-<run>-<attempt>`. The website's media is the `journey-media`
artifact. Wallet CI does not build or deploy the public website.

## Release

A new stable `vMAJOR.MINOR.PATCH` tag triggers
[Release](../workflows/release.yml), which calls LeanNative's `ios-release.yml`
at the pinned commit. The tag chooses the app marketing version; the workflow
run number chooses the build number. Every step is LeanNative's
`leannative-release` (built by `lake build leannative/leannative-release` in
`LeanApp`), which LeanNative's README describes.

1. Choose the intended commit and update
   [TestFlight notes](../../docs/testflight-what-to-test.txt) with the behavior
   and checks testers should exercise. The release refuses notes over 4,000
   characters and a tag that is not a stable `vMAJOR.MINOR.PATCH`.
2. Make sure a CI run outside a pull request has passed on that commit's tree:
   `main`'s push run, or CI run by hand on the branch. The release does not
   test again. Its `tested` job looks for that run and fails without one; a
   pull request's run does not count.
3. Optionally run **Release** by hand on that branch first. A manual run looks
   for no CI run and tests nothing. It builds, archives as version 0.0.0,
   signs, exports and checks the archive and the IPA, makes one read-only App
   Store Connect call, and uploads and publishes nothing.
4. Create a new, unused stable tag on the reviewed commit and push that tag.
5. Inspect the Release run's selected version/build, archive checks, upload,
   processing result and TestFlight status. Keep the run URL with release notes.

The `testflight` job imports the newest public census before generating the
Xcode project (`scripts/import-census`: the signature is verified under the
pinned key, inconsistent clearnet peers are dropped by the census's health
record, and the app's decoder accepts the result). Its log, the
`release-<run>-<attempt>` artifact (`peers-source.txt`) and a `Peers:` line
appended to What to Test on the runner record the census commit included in
the build. It uses pinned XcodeGen 2.46.0 and the repository's secrets
`ASC_KEY_ID`, `ASC_ISSUER_ID`, `ASC_PRIVATE_KEY`, `DEV_CERT_P12` and
`DEV_CERT_P12_PASSWORD`. Signing material stays in temporary runner storage
and is removed by the workflow's last step.

Before upload, the job checks the archive and the exported IPA
(`leannative-release verify-app` and `verify-ipa`): the bundle identifier,
team, version and build number, the signature, the iCloud container with
production iCloud, arm64 only, and no Swift. It records the IPA's SHA-256 and
the upload step checks it first, so what is uploaded is what was verified.
That a Release build ignores test mode is checked earlier, in CI's `release`
job (LeanNative's `test-mode-check`), not here. After upload it waits for
processing, sets notes and assigns the internal group. It never requests
external beta distribution: a review request cannot be withdrawn, so that is a
person's decision once the internal group has used the build, made with
`leannative-release testflight external` and the exact version
and build number. External
**WAITING_FOR_REVIEW** or **IN_REVIEW** means Apple review is pending; a green
Release run never means external testers can install.

The final job, `github-release`, publishes a GitHub release with generated
notes. It is a pre-release when the tagged commit is not on the default
branch, so a tag on a release branch never becomes "latest".

## Resume an existing upload

When processing outlasts the release or App Store Connect fails mid-run, finish
that upload by hand with `leannative-release testflight wait-processing`, then
`notes` and `internal`, with `TESTFLIGHT_MARKETING_VERSION` and
`TESTFLIGHT_BUILD_NUMBER` set to the original run's version and build number.
Never rerun the release for the same build number: it would upload again. Do not
use `leannative-release testflight all`, which performs setup and upload.
LeanNative's README lists the steps.

## App Store

There is no App Store submission workflow in this repository.
`leannative-release testflight` has the steps for one App Store version
(`appstore-status`, `appstore-attach`, `appstore-notes`, `appstore-submit`),
run by hand. Submission is distinct from TestFlight distribution and Apple
approval.

## Website and offline guides

Public site sources, generation and deployment live in
[winnowwallet/website](https://github.com/winnowwallet/website). The wallet app
bundles four offline HTML guides and `site.css` from `docs/`
(`LeanApp/WinnowApp/Project.lean`). Review those copies
when changing guidance for an app release. See the [documentation index](../../docs/README.md).

## History (Swift app)

Kept for its history, as last written for the Swift app (before 2026-10-31).
None of the workflows, scripts, artifacts or paths named here exist in this
repository: `Package.swift`, `scripts/ci-validation`,
`scripts/refresh-checkpoint`, `Tools/Generate/README.md`, and the
`appstore-submit.yml` and `testflight-feedback.yml` workflows went with the
Swift tree.

Winnow had one source tree and version train for the wallet app, SwiftPM
library products and development tools. The root `Package.swift` pinned one
package, swift-secp256k1, and `Package.resolved` recorded its commit. The app
and WalletCore shared the release tags.

### Validation

Parallel build prepares Debug app/test products once and also checks an ARM64
Release build. Units and journey download the hash-checked Debug artifact and
run on separate runners and simulators. Package runs SwiftPM tests, lint,
dependency and production-warning checks, debugging smoke and provenance
generation. Journey uses a fresh disposable signet fixture. Tailnet builds a
controlled Headscale/gateway environment for routing tests; it does not verify
live public Tor or I2P access.

Validation evidence never includes fuzz results.

The parallel scripts currently require Xcode 26.6 build 17F113 and select iOS
26.5. Runner, runtime, architecture and test inventory are recorded in lane
evidence. Check the source and run logs when those pins change.

### Evidence and reuse

`scripts/ci-validation` verifies complete reusable
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
and run.

### Release

Manual dispatch of Release ran fresh validation without signing, uploading,
assigning groups or publishing a GitHub release. A pushed tag started
publishing after the reused CI workflow succeeded, using either fresh checks or
eligible evidence under the policy above. Before upload, the job checked the
archive and exported IPA for the exclusion of E2E controls, and recorded
resolved dependencies and supply-chain metadata. The final job published a
GitHub release with SPDX and provenance artifacts.

Checkpoint maintenance was separate: `scripts/refresh-checkpoint` required a
genesis-validated header file and a reviewed vector update, described in the
checkpoint runbook (`Tools/Generate/README.md`).

### App Store and feedback

App Store submission (`appstore-submit.yml`) was a separate manual
operation. Attaching a build and setting notes changes App Store Connect even
when submission is disabled; use its status-only option for a read.

TestFlight feedback (`testflight-feedback.yml`) took an `age` public
key whose private key stays with the reader. Download its encrypted
`testflight-feedback-<run>` artifact within three days and decrypt locally.
The public run logs show counts; tester comments, emails, screenshots and crash
contents must remain encrypted in retained artifacts.
