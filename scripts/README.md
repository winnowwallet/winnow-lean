[Back to main README](../README.md)

# Scripts

CI is LeanNative's reusable `ios-app` workflow (`.github/workflows/ci.yml` calls it); its generic scripts
(`build-ios`, `ui-tests`, `check-no-swift`, `install-xcodegen`, `progress`) are in
`LeanApp/.lake/packages/leannative/framework/native/ci`. These are Winnow's own:

- [build-ios](build-ios) builds the Lean app from a clean checkout with LeanNative's `build-ios`, after the census
  list (`build-ios <Debug|Release> [iossim|ios]`; `PREPARE_ONLY=1` stops before xcodebuild).
- [check-core](check-core) holds the core library's import closure (`WinnowCore`, `Lean/WinnowCore.lean`:
  transaction review without seed phrases, Unicode tables, coin selection, wallet naming or I/O) to the list of
  modules it allows, so the core does not grow back; CI runs it. `--measure MOD...` prints a closure's module
  count and non-blank lines.
- [check-proofs](check-proofs) enforces zero proof leakage into runtime libraries (`WinnowCore`, `Winnow`,
  `WinnowApp`), zero theorems/axioms/`sorry` in runtime and spec modules, zero `sorry`/`native_decide`/`bv_decide`
  in proof modules, and zero panicking `!`-indexing in bounds-cleaned modules; CI runs it.
- [check-shell-names](check-shell-names) prepares the iOS project without Xcode (LeanNative's `build-ios` with
  `PREPARE_ONLY=1`) to run the check CI's Xcode jobs make before they compile: a string in the app's compiled C
  that equals the name of a shell capability the manifest does not list. A JSON key `"device"` stopped all
  three Xcode jobs once; this says so in the `lean` job in about fifteen seconds. CI runs it.
- [ci-regtest](ci-regtest) runs io-test, backend-test, multisig-differential, card-regtest and
  segwit-regtest against a disposable regtest bitcoind (CI's `lean` job).
- [install-bitcoin](install-bitcoin) downloads the pinned Bitcoin Core release (31.1) from bitcoincore.org, checks
  its SHA-256 and prints its bin directory; `ci-regtest` and `ui-fixture` run against it, never a bitcoind
  found on the PATH.
- [ui-fixture](ui-fixture) starts the UI journeys' regtest node and config, and afterwards collects the app's
  journals and stops the node: the hooks of LeanNative's `ui-tests` and `wire-journeys`.
- [journeys](journeys) runs the journeys locally as CI does: in the simulator, or `--wire` headless against the
  app itself (no simulator, no XCTest). Without names it runs all of them.
- [leancov](leancov) runs source-level Lean 4 coverage, McCabe CRAP, and Cognitive Complexity via `leancov`:
  stages out-of-tree instrumented copies of `Lean/Winnow` and `LeanApp/WinnowApp` under `build/leancov/`, builds
  and runs the selected suites in parallel (including regtest suites and headless wire journeys), and writes
  `build/leancov/coverage.json` and `build/leancov/lcov.info`. Supports `--fast` (the 13 non-regtest, non-journey
  suites), `--report [suite ...]` (re-report from existing `.cov` profiles), `--list`, and resolves `leancov` from
  `--leancov-dir`, `$LEANCOV_DIR`, `../leancov`, or `PATH`.
- [ios-simulator](ios-simulator) prints one available iPhone (default) or iPad on the newest iOS runtime.
- [signet-fixture](signet-fixture) provisions a disposable custom-signet bitcoind (`up`, `down`, `status`,
  `snapshot DIR`, `destroy`). For a regtest node with a funded wallet, use `LeanApp`'s `backend-test --fixture <dir>`.
- [import-census](import-census) fetches the census's `census/peers.json` at a census commit (default: its
  `main`, the newest) into `build/census/`, the peer list the app ships (the app's manifest, `LeanApp/WinnowApp/Project.lean`, bundles it): it
  verifies the Ed25519 signature under the key pinned in [census-public-key.txt](census-public-key.txt)
  ([ed25519_verify.py](ed25519_verify.py)), drops clearnet peers the census's health record scores under 70,
  checks the result with Lean's `census-check` and records its provenance in `build/census/peers-source.txt`.
  CI runs it in each job that builds (`prepare` in `ci.yml`: `lean`, `app` and `release`); `build-ios` runs it
  for CI (`CI=true`) and Release builds and when the list is missing; `IMPORT_CENSUS=1` forces it, `IMPORT_CENSUS=0` keeps an existing list.
- [foundation-vectors](foundation-vectors) regenerates `LeanApp/FoundationVectors.lean`: what Foundation's `URL`
  and the Swift app's rules answer for custom explorer URLs and manual peers, which records-test checks the
  Lean rules against (macOS, `xcrun swift`).
- [mainnet-retarget-vectors](mainnet-retarget-vectors) writes `Lean/Vectors/mainnet-retargets.json`, the
  headers either side of every mainnet retarget, from a public Esplora server. Each header must hash to its
  block and meet its own target, so the server is trusted for nothing. crypto-test checks `expectedBits`
  against them.
- [funding-sources-vectors](funding-sources-vectors) writes `Lean/Vectors/mainnet-funding-sources.json`: five
  mainnet spends whose inputs are not segwit (key hashes with both key encodings, a 2-of-3 script hash, wrapped
  segwit and a bare key), each input with the script it spent, from a public Esplora server. Each transaction, and
  each one an input spends from, must hash to its txid, so the server is trusted for nothing. crypto-test holds
  `FundingSources.revelation` to them.
- [bip32-vectors](bip32-vectors) writes `Lean/Vectors/bip32-test-vectors.json`: the test vectors of BIP32
  itself, read from the BIP's text (vectors 1 to 4 give a seed and each chain's extended keys, vector 5 extended
  keys that must be refused). crypto-test holds `HDKey` to them.
- [card-keys-vectors](card-keys-vectors) writes `Lean/Vectors/card-keys-vectors.json`: a wallet's silent payment
  keys, the tweak, label and code it makes for each person and the payments derived from them (issue #94),
  computed with the
  Python standard library alone (BIP32, secp256k1, tagged hashes, bech32m) and none of the wallet's code.
  `card-keys-test` holds `Winnow.Keys.SilentPaymentPairing` to them.
- [ecdsa-vectors](ecdsa-vectors) writes `Lean/Vectors/openssl-ecdsa-secp256k1.json`: 64 ECDSA signatures over
  secp256k1 that OpenSSL made and verified, with their keys, which segwit-test holds the verifier
  (`Lean/SecpCt/Ecdsa.lean`) and the DER reader (`Lean/Secp/Der.lean`) to. OpenSSL signs with its own randomness,
  so the file is one run, kept.
- [secp-vectors](secp-vectors) writes `Lean/Vectors/secp-known-answers.json`: what every curve operation the
  wallet uses must answer, and where it must refuse, computed on Python integers with none of the wallet's code.
  The wallet has one implementation of secp256k1 (`Lean/SecpCt`), so this is what its compiled code is compared
  with; secpct-test holds it to every record. The output is the same on every run, and `--check` (CI runs it)
  fails if the kept file is not it.
- [swift-utf8-vectors](swift-utf8-vectors) writes `Lean/Vectors/swift-utf8-decoding.json`, Swift's own
  `String(decoding:as: UTF8.self)` over well-formed and ill-formed UTF-8, which `crypto-test` holds
  `Winnow.Text.decodeUTF8Lossy` to. It needs Xcode's Swift and feeds the program to `xcrun swift` on stdin, so
  the tree keeps no `.swift` file.
- [tests/](tests) holds the scripts' unit tests: `python3 -m unittest discover -s scripts/tests`.

Run commands from the repository root unless their help specifies otherwise.
