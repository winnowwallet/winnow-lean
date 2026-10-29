[Back to main README](../README.md)

# Scripts

CI is ElmLean's reusable `ios-app` workflow (`.github/workflows/ci.yml` calls it); its generic scripts
(`build-ios`, `ui-tests`, `check-no-swift`, `install-xcodegen`, `progress`) are in
`LeanApp/.lake/packages/elmlean/framework/native/ci`. These are Winnow's own:

- [build-ios](build-ios) builds the Lean app from a clean checkout with ElmLean's `build-ios`, after the census
  list (`build-ios <Debug|Release> [iossim|ios]`; `PREPARE_ONLY=1` stops before xcodebuild).
- [verify-release-no-test-mode](verify-release-no-test-mode) launches the Release and Debug simulator builds
  with test mode's environment: Debug must start the test run, Release must ignore it (CI's `release-check`).
- [ci-regtest](ci-regtest) runs io-test, backend-test and multisig-differential against a disposable regtest
  bitcoind (CI's `extra` job).
- [install-bitcoin](install-bitcoin) downloads the pinned Bitcoin Core release (31.1) from bitcoincore.org, checks
  its SHA-256 and prints its bin directory; `ci-regtest` and `ui-fixture` run against it, never a bitcoind
  found on the PATH.
- [ui-fixture](ui-fixture) starts the UI journeys' regtest node and config, and afterwards collects the app's
  journals and stops the node (`ui-tests`' hooks); [ui-journeys](ui-journeys) runs the journeys locally as CI does.
- [journey-media](journey-media) makes the website's media from a journeys run with prepare-journey-media.
- [prepare-journey-media](prepare-journey-media) turns a UI-journeys output into the website's media
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
  CI runs it once per run (the `build` job's `prepare`); `build-ios` runs it for Release builds and when the
  list is missing; `IMPORT_CENSUS=1` forces it, `IMPORT_CENSUS=0` keeps an existing list.
- [tests/](tests) holds the scripts' unit tests: `python3 -m unittest discover -s scripts/tests`.

Run commands from the repository root unless their help specifies otherwise.
