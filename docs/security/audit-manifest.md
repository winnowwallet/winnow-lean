# Winnow security audit manifest

> Historical audit boundary, not a current source inventory or CI checklist.
> For today’s checks and release process use the [CI runbook](../../.github/internal/ci-release.md);
> [security notes](README.md) explain changes since these snapshots.

This file freezes the source and evidence boundary for the security work. A
checked box or passing test proves only the named property. It is not a
general wallet-safety claim, and the mainnet decision is the
[gate report](gate-report.md)'s, not this file's.

Two frozen targets are recorded. The August 2026 record is kept as written —
its evidence rows in the [findings register](findings.md) name that tree, and
references to Silent Payments, the tweak index, `BitcoinCore`, `BitcoinP2P`
and `EsploraClient` describe the implementation reviewed then, all since
removed or folded into `WalletCore`. The 2026-09-14 record re-freezes the
manifest at the tree the [independent review](independent-review-2026-09-14.md)
was fixed against (IR-007), so that a reader following the pointers below
finds the files they name.

Scope note (2026-09-15, 0.7.1): the embedded Tor client — `TorBridge/`
(Rust, Arti 0.46.0), `TorController.swift`, `NetworkRoute.swift`'s Tor route,
`OnionChecksum.swift` and the SOCKS5 path in `PeerConnection.swift` — was
removed after the 2026-09-14 review; its 400-crate dependency tree had never
been independently reviewed (#95, #144). The rows below that name those files
describe the reviewed tree, kept on the `archive/tor-0.7.0` branch. The
current egress inventory has no Tor rows: every connection is direct, and
`RoutedHTTPClient` now lives in `Network/Transport/RoutedHTTPClient.swift`.

Scope note (2026-09-29): "every connection is direct" no longer holds. #179
restored the SOCKS5 path in `PeerConnection.swift` for external gateways, and
#181 added gateway routing ([peer gateways](../peer-gateways.md)). The census
also downloads automatically on mainnet when the saved catalog is missing or
expired, not only on request. Egress added since the frozen table below:

| Egress | Transport | Carries | When |
|---|---|---|---|
| Gateway lookup | UDP DNS to Tailscale's resolver `100.100.100.100:53` (`Network/Transport/TailnetGatewayDiscovery.swift`) | A-record queries for `winnow-tor-gateway` and `winnow-i2p-gateway`; nothing about the wallet | Automatic routing, when networking starts in the foreground and on reconnect or retry |
| Gateway probe | TCP to each answering tailnet address (`TailnetGatewayDiscovery.probeSOCKS`) | A SOCKS5 greeting | Right after the lookup |
| Routed peers | `PeerConnection.swift` through the gateway's SOCKS5 port (`Network/Transport/PeerGateways.swift`) | The same peer traffic as a direct connection; the destination name goes to the gateway | Tor and I2P peers, and every peer when clearnet is off |
| Routed HTTP | `RoutedHTTPClient` through the Tor gateway | Census and explorer requests | When clearnet is off and Tor is on |
| Census I2P mirror | `RoutedHTTPClient` through the I2P gateway to `CensusCatalog.i2pMirror` | The same census GETs | I2P-only routing; public hosts and explorer lookups are refused |

Scope note (2026-10-13): the app no longer downloads the census. Each release
bundles the census list current when it was built (`scripts/import-census`), so the
census refresh egress in the frozen table below and the census I2P mirror row
above are gone, routed HTTP carries explorer requests only, and I2P-only
routing makes no HTTP request at all.

## Frozen target, 2026-09-14

| Item | Value |
|---|---|
| Source commit | `2a6a4a40c3a418998676ecd59070ec370e00a5b6` on the review branch (winnow#137); the merge commit that lands it supersedes this row |
| Commit date | 2026-09-14 15:17:39 -04:00 |
| Swift | Apple Swift 6.3.3 (`swiftlang-6.3.3.1.3`) |
| Xcode | 26.6 (`17F113`) |
| Installed iOS runtimes | 26.4.1, 26.5 |
| Minimum package platforms | iOS 17, macOS 14 |
| Baseline commands | `swift test`; `scripts/ci-app-tests` (`WinnowAppTests` on a simulator); `swiftlint lint` |
| Baseline result | The package suite and the app suite pass at this revision; the counts are the dated rows of 2026-09-14 in the findings register. Lint clean. |
| CI at this revision | Recorded on winnow#137: `package`, `package-tests-intel`, `differential`, `complexity`, `app-build`, and the four `ui-iPhone-<story>` jobs |

Suites gated by `WINNOW_DIFF` run on the node lane against a local Bitcoin
Core; the iPad journeys run on `main` and not on the pull-request path (a
2026-09-14 change). An iOS release configuration is exercised only by the
release workflow.

## Frozen target, August 2026 (historical)

| Item | Value |
|---|---|
| Source commit | `98d90563a2c20b7137c708cb121e72b9b34552a3` |
| Commit date | 2026-08-20 06:55:20 -04:00 |
| Swift | Apple Swift 6.3.3 (`swiftlang-6.3.3.1.3`) |
| Xcode | 26.6 (`17F113`) |
| Host target | `arm64-apple-macosx26.0` |
| Installed iOS runtimes | 26.4.1, 26.5 |
| Minimum package platforms | iOS 17, macOS 14 |
| Build configuration exercised | SwiftPM debug |
| Baseline command | `swift test` |
| Baseline result | 310 tests in 60 suites passed |
| Hardened branch result | 311 tests in 60 suites passed; targeted PSBT AddressSanitizer run passed; iOS simulator build passed |

The baseline run did **not** execute suites gated by `WINNOW_DIFF` or the
checkpoint-generation environment. (At the frozen commit two further suites
were gated by `WINNOW_SIGNET`, which no workflow set; their assertions now run
on the node lane under `WINNOW_DIFF=1` as `FilterSyncDiffTests`. Since this
baseline, checkpoint generation and the genesis-versus-checkpoint agreement
check left the test tree for the `winnow-debug generate` subcommand, and the 2,000 headers
past the checkpoint became a vector that `HeaderChainTests` connects on
every CI run.) App/UI tests and an iOS release configuration were also outside
this run.

## Size and dependency boundary

Counts use `cloc 2.08` over `Sources/` only (`--include-lang=Swift`), exclude
comments, blank lines, dependencies, generated projects, tests and
documentation, and are measured at the 2026-09-14 frozen commit.

| Production surface | Files | Logical lines |
|---|---:|---:|
| `WalletCore` (primitives, network, wallet and signing core) | 58 | 14,427 |
| — of which `Network/Protocol/FallbackPeersGenerated.swift` (generated peer list) | 1 | 2,986 |
| `WinnowApp` (iOS application/UI) | 23 | 5,730 |
| **Production total** | **81** | **20,157** |
| **Production total without the generated list** | **80** | **17,171** |

The August table (72 files, 11,961 lines across five surfaces) is superseded;
the growth is the network layer's peer-source classes, the census and its
signature, people and shared savings, the sealed stores and the review's
fixes.

The one external Swift package is `21-DOT-DEV/swift-secp256k1` (version
`0.23.2`, commit `e70a10e036a55fffea31568f0af92d69b6d449cd`, recorded in
`Package.resolved`): Bitcoin Core's libsecp256k1, behind the `P256K` module,
for every key, tweak, signature and the BIP352 derivation. The app additionally embeds Arti 0.46.0 built from locked Rust
source ([TorBridge](https://github.com/winnowwallet/winnow/tree/archive/tor-0.7.0/TorBridge), now on the archive branch); `WalletCore` and the census
do not link Rust.

## Severity rules

| Severity | Release meaning |
|---|---|
| Critical | Practical unauthorized fund loss or broad secret extraction. Stop release; track the finding in a public issue under SECURITY.md. |
| High | Authorization bypass, key/nonce compromise, unintended spend path, or trusted-state corruption under a credible attacker. Stop release. |
| Medium | Security control weakness needing meaningful preconditions, bounded privacy disclosure, recoverable corruption, or resource exhaustion. Fix or record owner, mitigation, and release decision. |
| Low | Defense-in-depth, diagnostic, or hardening gap without a credible direct loss path. Track normally. |

Availability becomes high only when a credible input can permanently strand
funds or destroy the only usable recovery state. Findings are scored by impact
and credible prerequisites, not by code location.

## Trust boundaries

1. **Device secret boundary:** recovery words and extended private keys enter
   `KeyStore`, iOS Keychain, derivation, signing, authenticated reveal, and
   explicitly seed-bearing export paths.
2. **Authorization boundary:** SwiftUI review state feeds wallet transaction
   construction, PSBT fields, sighash calculation, signing, finalization, and
   broadcast. Mutation after review must fail closed.
3. **Untrusted network boundary:** DNS, peers, the census list and, when the
   user opts in, the block explorer supply attacker-controlled bytes or JSON.
4. **Untrusted interchange boundary:** addresses, descriptors, people's keys,
   PSBTs, Winnow cards and import bundles are attacker-controlled text/files
   even when they arrive from a known person.
5. **Persistent-state boundary:** wallet JSON, the sealed people
   file, headers, filter progress, peer cache, the downloaded census, settings,
   export staging files, and E2E journals have different authority and
   confidentiality.
6. **Build/distribution boundary:** package revisions, GitHub Actions, Xcode,
   signing credentials, TestFlight, the census repository and its signing key,
   and published evidence determine whether reviewed source is the source
   users receive.

## External disclosure inventory

Every point at which bytes can leave the device, and what each one carries.
Re-derived on 2026-09-14 with
`grep -rn "URLSession\|NWConnection\|getaddrinfo\|openURL" Sources/`; the Arti
row comes from the Tor bridge, which the grep cannot see.

| Egress | Transport | Carries | When |
|---|---|---|---|
| Peer connections | `NWConnection` (`WalletCore/Network/Transport/PeerConnection.swift`), directly or through Arti's local SOCKS port | BIP157/158 filter and header requests, and transactions the user broadcasts | Always: this is how the wallet reads the chain |
| DNS seeds | DoH over `URLSession` (`RoutedHTTPClient`), falling back to `getaddrinfo` (`WalletCore/Network/Peers/SeedResolver.swift`) | Seed hostnames only; the answer is capped at 128 KiB | At startup when local candidates do not fill the pool |
| Census refresh | `RoutedHTTPClient` (`NetworkRoute.swift`), through Tor when Tor is on, to `census.winnowwallet.com` | A GET for `census/peers.json` and, once a publisher key is compiled in, `peers.json.sig`; nothing about the wallet. The answer is capped at 4 MiB, must verify, and must be no thinner than a real census | Only when the user taps refresh in Settings; mainnet only |
| Explorer sender lookup | `RoutedHTTPClient` to the configured explorer (`WinnowApp/SenderLookup.swift`) | A GET for `/tx/{txid}`: one transaction id, no query string, no body | Only after the user opts in, per lookup |
| Arti | The embedded Tor client's own connections (`TorBridge/`) | Directory and guard traffic of an ordinary Tor client | Whenever Tor is on |
| Block explorer link | Browser handoff via `openURL` (`WinnowApp/Components.swift`) | The selected address or transaction and the browser connection's IP address | Only after the user taps a link and confirms the privacy warning; responses are never used by wallet sync |

`RoutedHTTPClient` follows a redirect only within the host it was asked of
and never down from https; a custom explorer must be https (plain http only
on loopback, for the test stub). No silent-payment tweak-index client and no
`EsploraClient` exist in the tree; historical references to them describe the
August revision.

## Production source inventory

Every production file is listed below. "Owner" means the responsible module,
not a named person; a named human reviewer is still required, as the gate
report records.

### WalletCore — owner: primitives, network/chain and wallet-authorization review

Parsed input and trust boundary: keys, addresses, descriptors, scripts,
transaction-derived bytes, arbitrary peer and DNS bytes, the census list and
its signature, persisted wallet state, PSBTs, people's keys, Winnow cards and
import/export bundles. Secrets: BIP39/BIP32 keys, signing tweaks, BIP340
nonces, derived signing keys. Persistence: Keychain, wallet JSON, header
chain, filter frontier, peer cache, broadcaster state, downloaded census and
export staging files. Primary test owners: `BitcoinCoreTests`,
`WalletCoreTests`, `DifferentialTests` and the fuzz harness.

- `Crypto/Base58.swift`, `Crypto/Bech32.swift`, `Crypto/GCSFilter.swift`
- `Crypto/PBKDF2.swift`, `Crypto/RIPEMD160.swift`, `Crypto/SipHash.swift`, `Crypto/TaggedHash.swift`
- `Descriptors/Descriptor.swift`
- `Keys/BIP32.swift`, `Keys/BIP39.swift`, `Keys/BIP39Wordlist.swift`, `Keys/BIP86.swift`, `Keys/KeyStore.swift`, `Keys/KeychainStore.swift`
- `Network/Broadcast/TxBroadcaster.swift`, `Network/Filters/FilterSync.swift`
- `Network/Headers/HeaderChain.swift`, `Network/Headers/UInt256.swift`, `Network/Mempool/MempoolWindow.swift`
- `Network/Peers/CensusCatalog.swift`, `Network/Peers/CensusCatalogStore.swift`, `Network/Peers/CensusSignature.swift`, `Network/Peers/OnionChecksum.swift`
- `Network/Peers/PeerDiversity.swift`, `Network/Peers/PeerPool.swift`, `Network/Peers/SeedResolver.swift`
- `Network/Protocol/Block.swift`, `Network/Protocol/FallbackPeersGenerated.swift`, `Network/Protocol/Framing.swift`, `Network/Protocol/Inventory.swift`
- `Network/Protocol/Messages.swift`, `Network/Protocol/NetworkParams.swift`, `Network/Protocol/PeerAddress.swift`, `Network/Protocol/Transaction.swift`, `Network/Protocol/Wire.swift`
- `Network/Transport/NetworkRoute.swift`, `Network/Transport/PeerConnection.swift`
- `PSBT/PSBT.swift`, `PSBT/PSBTRoles.swift`
- `Script/Multisig.swift`, `Script/Script.swift`, `Script/Taproot.swift`
- `SilentPayments/Sending.swift`, `SilentPayments/SilentPaymentAddress.swift` (BIP352 sending, reinstated October 2026)
- `Transactions/AddressDecoder.swift`, `Transactions/FundingSources.swift`, `Transactions/SighashBIP341.swift`, `Transactions/SilentPayment.swift`, `Transactions/Signer.swift`, `Transactions/TransactionBuilder.swift`
- `Wallet/CoinSelection.swift`, `Wallet/ExportStagingFile.swift`, `Wallet/FeePolicy.swift`, `Wallet/ImportBundle.swift`, `Wallet/People.swift`
- `Wallet/Wallet.swift`

### WinnowApp — owner: iOS authorization/UI review

Parsed input and trust boundary: user text, clipboard, files, settings, the
people file, the explorer's answer, app lifecycle, device
authentication, and the E2E launch environment. Secrets: recovery
display/copy, wallet creation handoff, seed-bearing export. Persistence:
UserDefaults, the sealed people file (HMAC under a Keychain-held key), receive labels, the E2E journal. Primary test
owners: `AppTests` (`WinnowAppTests`), `UITests`, plus library tests for
logic that remains below the UI.

- `AppModel.swift`, `BackgroundSyncScheduler.swift`, `BackupSection.swift`, `BeginnerHomeView.swift`, `ChainCheckStatus.swift`
- `CloudAppState.swift`, `CloudBackupController.swift`, `CloudBackupView.swift`, `Components.swift`, `E2EMode.swift`
- `HomeView.swift`, `ICloudBackupStore.swift`, `OnboardingView.swift`, `PeerGatewaysSection.swift`, `PeerRoutingBanner.swift`
- `PeopleStore.swift`, `ReceiveAddressLabelEditor.swift`, `ReceiveAddressLabelStore.swift`, `ReceiveView.swift`, `RecipientsView.swift`
- `ScreenCaptureMonitor.swift`, `SendView.swift`, `SenderLookup.swift`, `SensitivePresentationEpoch.swift`, `SettingsView.swift`
- `StoreAuthentication.swift`, `WinnowApp.swift`
- `Assets.xcassets/AppIcon.appiconset/Contents.json`

The Tor bridge (`TorBridge/`, Rust, Arti 0.46.0) is inventoried by its own
README and lockfile; the census publisher (winnowwallet/census) consumes
`WalletCore` as a package dependency and is inventoried in its repository.

## Baseline evidence and gaps

- Present: BIP/vector suites; parser negatives and the fuzz harness's sixteen
  targets; wallet create/send/RBF/import;
  peer loopback, failover, filter-consensus and broadcaster tests; header
  rules with a generator-proven checkpoint; sealed-store and census-signature
  tests; story redaction/idempotency checks; Bitcoin Core differential tests
  and the iPhone journey on every pull request; Keychain attribute read-back
  (protection class, synchronizable flag, the user-presence access control
  and its in-place upgrade of an earlier version's item) and the privacy
  cover in the app suite.
- Not executed on the pull-request path: the iPad journeys (on `main`), the
  sustained fuzz matrix (weekly), soak runs, device authentication on real
  hardware, and release provenance (release workflow).
- Structural gap: the simulator has no data protection and no Secure Enclave,
  so a protection class and the user-presence access control (IR-023) are
  observed to be requested and recorded, never to be honoured — the
  simulator releases the secret to a read that forbids interaction; that is
  Apple's contract and needs real hardware.
- Census signing (IR-003): the September 18 activation configured the publisher
  key and required signatures. From October 13 releases ship the census list
  instead and verify no signature. Earlier frozen observations above describe
  the pre-activation tree.
  On 2026-09-18 the owner chose public GitHub issues for bug and vulnerability
  reports (IR-009); enabling private vulnerability reporting is not pending.
  IR-023 (an access-control class on the Keychain item) was fixed on
  2026-09-15.

## Change control

The frozen commit remains the comparison base. Each bounded security change
must name the invariant, tests, residual risk, and rollback. Unrelated
refactors in the inventoried modules should wait until the next review pass or
be reviewed as changes to the audit target. Report and track findings publicly
under [SECURITY.md](../../SECURITY.md).
