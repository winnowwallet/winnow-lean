[Back to main README](../README.md)

# Scripts

- [install-xcodegen](install-xcodegen) downloads and verifies XcodeGen 2.46.0, which generates the
  app's Xcode project (`LeanApp/ios/project.yml`).
- [build-ios](build-ios) builds the Lean app from a clean checkout: Lake, ElmLean's `ios_lean_sources.sh`,
  XcodeGen and xcodebuild (`build-ios <Debug|Release> [iossim|ios]`; `PREPARE_ONLY=1` stops before xcodebuild).
- [check-no-swift](check-no-swift) fails on any Swift source, Swift compile step or Swift library in the app.
- [verify-release-no-test-mode](verify-release-no-test-mode) launches the Release and Debug simulator builds
  with test mode's environment: Debug must start the test run, Release must ignore it.
- [ci-lane](ci-lane) runs one CI lane (`lean`, `regtest`, `ios`, `journey`); the workflows call it.
- [ci-ui-journey](ci-ui-journey) runs the Objective-C UI journeys against a regtest fixture and keeps the
  evidence.
- [prepare-journey-media](prepare-journey-media) turns a `ci-ui-journey` output into the website's media
  (`prepare-journey-media <journey-out> <media-out>`): the screenshots, a browser copy of the recording (ffmpeg,
  at most 25 MiB) and `journey-provenance.json` (version 2: the run, source, device, each test's result and
  seconds, each file's SHA-256). CI publishes it as the `journey-media` artifact, which winnowwallet.com fetches;
  its tests are in [tests](tests) (`python3 -m unittest discover -s scripts/tests`).
- [install-lean](install-lean) installs elan and the Lean toolchain on CI and release runners.
- [testflight.sh](testflight.sh) drives App Store Connect (processing, notes, the internal group);
  [asc-jwt](asc-jwt) mints its token, [ci-sign.sh](ci-sign.sh) writes the API key,
  [check-release-policy](check-release-policy) checks the tag, and
  [verify-signed-archive](verify-signed-archive) / [verify-exported-ipa](verify-exported-ipa) check what
  is uploaded.
- [ios-simulator](ios-simulator) prints one available iPhone (default) or iPad on the newest iOS runtime.
- [signet-fixture](signet-fixture) provisions a disposable custom-signet bitcoind (`up`, `down`, `status`,
  `snapshot DIR`, `destroy`). For a regtest node with a funded wallet, use `LeanApp`'s `backend-test --fixture <dir>`.
- [import-census](import-census) fetches the census's `census/peers.json` at a census commit (default: its
  `main`, the newest) into `build/census/`, the peer list the app ships (`project.yml` bundles it): it
  verifies the Ed25519 signature under the key pinned in [census-public-key.txt](census-public-key.txt)
  ([ed25519_verify.py](ed25519_verify.py)), drops clearnet peers the census's health record scores under 70,
  checks the result with Lean's `census-check` and records its provenance in `build/census/peers-source.txt`.
  `build-ios` runs it for CI and Release builds and when the list is missing; `IMPORT_CENSUS=1` forces it,
  `IMPORT_CENSUS=0` keeps an existing list.
- [tests/](tests) holds the scripts' unit tests: `python3 -m unittest discover -s scripts/tests`.

Run commands from the repository root unless their help specifies otherwise.
