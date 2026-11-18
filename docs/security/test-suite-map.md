# Where the Swift suites named in these records are now

Note of 2026-11-17. This file replaces the September 2026 map of Swift
selectors, which is in this file's history. The records in this directory cite
the Swift app's test suites by name. None of those suites or commands can be
run in this repository: it has no `Tests/`, `AppTests/`, `UITests/` or `Tools/`,
and no `swift test`, `xcodebuild` or `winnow-debug`. Dated findings and
validation rows keep their original names, commands and counts; nothing here
rewrites them.

The Lean app's tests are executables (`Lean/lakefile.toml`,
`LeanApp/lakefile.toml`), each one file with sections, and the UI journeys in
`LeanApp/Journeys.lean`. [The testing guide](../testing.md) says what CI runs
and what the tests do not cover; that guide, not this file, describes current
checks.

Each row below was written by searching the Lean test files for the suite's
name, or for the control it covered. “No Lean counterpart found” means that
search found no test. It does not say whether the control itself was ported;
where it was, the row names it.

## Suites carried under their own names

These are section headings or comments in the Lean test files.

| Swift suite | Lean executable | Where |
| --- | --- | --- |
| `MultisigAccountTests`, `TimelockedMultisigTests`, `NestedMultisigTests` | `multisig-test` | `Lean/MultisigTest.lean`, sections of those names; the nested accounts' Ledger cases are in `ledger-test` |
| `SighashBIP341Tests`, script-path half (earlier `SighashBIP341ScriptPathTests`) | `multisig-test` | section “BIP341 script-path vectors”, over `Lean/Vectors/bip341-scriptpath-test-vectors.json` |
| `HistoryOutputTests`, `HistoryLedgerTests`, `WalletCursorTests` | `multisig-test` | sections of those names |
| `SilentPaymentSendTests` | `multisig-test` | section of that name |
| `SilentPaymentTests`, and the silent payment case of `PeopleTests` | `silent-payment-test` | `Lean/SilentPaymentTest.lean` |
| `KeyStoreTests.accountSerialization`, `AccountKeyCustodyTests` | `multisig-test` | one section |
| `FeeResolutionTests` (the pure parts) | `multisig-test` | section of that name |
| `ImportBundleTests.signers` (earlier `ImportBundleBoundsTests`) | `multisig-test` | section “ImportBundleTests.signers … and the new bundle bounds”. The entry-count limits are checked there; no test of the byte limit (`ImportBundle.maximumSerializedBytes`) was found |
| `LedgerTests` | `ledger-test` | `Lean/LedgerTest.lean` |
| `MultisigStoreTests`, `MultisigAccountFlowTests`, `LedgerPairingTests`, `LedgerBluetoothTests`, `SignerRosterTests`, `NestedMultisigFlowTests`, `HistoryDisplayTests`, `SendReviewBindingTests` | `multisig-app-test` | `LeanApp/MultisigAppTest.lean`, sections of those names. The test names `SEC-030` to `SEC-037` cite are unchanged there and in `multisig-test` |
| `PeerGatewayModelTests`, `BackgroundSyncTests` | `records-test` | `LeanApp/RecordsTest.lean`, sections “Peer gateways” and “Background checks” |
| `CloudWalletBackupTests`, `CloudBackupTests`, `CloudAppStateTests`, `AutomaticCloudBackupTests`, `WalletStartupTests` | `cloud-backup-test` | `LeanApp/CloudBackupTest.lean`, sections of those names |

## Suites not carried by name

The middle column is the name the Swift app's September consolidation gave
the suite, where the earlier map recorded one.

| Swift suite in the records | Renamed in the Swift app | In the Lean tree |
| --- | --- | --- |
| `LoopbackTests`, `FilterSyncPersistenceTests`, `FilterProgressRollbackTests`, `FilterMatchingTests` | `FilterSyncTests` | `io-test` (`Lean/IOTest.lean`) against a regtest Bitcoin Core: a compact-filter download with a match, pinned filter headers equal to the node's, the `filters.json` round trip and a rollback on a reorg |
| `CheckpointMajorityTests`, `PeerDisagreementTests`, `CrossSourceCheckTests`, `CheckpointHangupTests` | `FilterSyncAdversaryTests` | `io-test`: filter votes that split or that one source class carries, `disputedPinChecks`, `restedScanPeerChecks` |
| `PeerCooldownTests`, `StaleTipEvictionTests` | `PeerPoolTests` | `io-test`: the cooldown schedule, a peer far below our height evicted as stale before a vote, and discovery (a comment there names `PeerPoolTests`) |
| `PeerDiversityTests`, `SeedResolverTests` | `PeerPolicyTests` | `io-test`: `DiversityPolicy` and seed filtering |
| `MainnetCheckpointTests`, `CheckpointStartTests`, `HeaderStartPolicyTests`, `HeaderReplayTests`, `ReorgVisibilityTests` | `HeaderChainTests` | `crypto-test` (`Lean/CryptoTest.lean`): `headerBranches`, and retargeting against `Lean/Vectors/mainnet-retargets.json`. `io-test`: header sync, a reorg, an equal-work stale sibling, `headerTurnChecks` |
| `HeaderStorageAppendTests`, `HeaderStorageCorruptionTests`, `HeaderStorageBoundsTests` | `HeaderStorageTests` | `io-test` checks the `headers.bin` round trip. No Lean test of the corruption cases or of the file-size bound (`HeaderChain.maximumHeaderFileBytes`) was found |
| `TxBroadcasterBackoffTests`, `FeeFilterAnnouncementTests`, `TxBroadcasterReorgTests` | `TxBroadcasterTests`, `TxBroadcasterStoreTests` | `io-test`: a broadcast the node holds, a reorg under it, the `broadcast.json` round trip, the announcement timeout, a peer whose fee filter keeps it from being told, `broadcastRaceChecks`, `serveOnlyTheToldChecks` |
| `WireFormatTests`, `MessageTests`, `FramingTests` | `WireTests` | `fuzz` targets `messages`, `framing`, `transaction` and `block` (`Lean/Fuzz.lean`); `io-test` `framerOffsetChecks` |
| `SpentCoinTombstoneTests`, `ReorgRollbackTests` | `WalletReorgTests` | `multisig-test` `aLosingPendingSend` (a chained send and a reorg); `backend-test` `reorgFlow` (`LeanApp/BackendTest.lean`); `card-regtest`'s reorganised payment |
| `CoinSelectionPropertyTests`, `FeePolicyTests` | `CoinSelectionTests` | No suite of that name, and no seeded property run was found. Fee resolution is `multisig-test`'s `FeeResolutionTests`; refused sends (a dust payment, a rate past the maximum) are in `backend-test` |
| `AntiFeeSnipingTests` | `TransactionBuilderTests` | No Lean counterpart found by name |
| `PSBTTests` (`hostileLengths`), `DescriptorBoundsTests` | | `fuzz` targets `psbt` and `descriptor`. The descriptor target's seeds include a tree of 4,000 nested braces; no test at depth 128 and 129 was found. The bound is `Descriptor.maximumTreeDepth` (`Lean/Winnow/Wallet/Descriptor.lean`) |
| `TransactionTests.oversizedSerializedScript` | | No Lean counterpart found by name. The bound is `maxSerializedScript` (`Lean/Winnow/Tx/Transaction.lean`) |
| `SendPreviewAuthorizationTests`, `SpendExclusionTests` | | The gate and the exclusion are `SendReview.authorizes` and `exclusively` (`LeanApp/WinnowApp/Real/Send.lean`); a send, a fee bump and an account's broadcast run under `exclusively`. No Lean test that names either was found. `multisig-test`'s `SilentPaymentSendTests` checks the scripts handed to the gate |
| `JournalRedactionTests`, `ErrorSurfaceTests` | | `looksSecret` is `LeanApp/WinnowApp/E2E.lean`. No Lean test that names it was found |
| `E2EEntropyPinningTests` | | The rule (`missingPinnedEntropy`) is `LeanApp/WinnowApp/E2E.lean`. No Lean counterpart found by name |
| `KeychainAttributeTests`, `PrivacyShieldTests`, `ClipboardPolicyTests`, `ScreenCaptureTests`, `NetworkScopedSettingsTests` | | No Lean counterpart found. The Keychain item and the privacy cover over an inactive scene are the LeanNative shell's, which is not in this repository |
| `StoreAuthenticationTests` | | No Lean counterpart found by name. `multisig-app-test` has the account store's sealed persistence (`testTamperedUnsealedAndOversizedFilesAreRefusedAndKept`) |
| `VaultFlowTests`, `VaultThresholdTests`, `PSBTMultisigTests`, `VaultCosignerIdentityTests`, `VaultDraftIdentityTests`, `VaultSignerIndependenceTests`, `VaultAdmissionTests` | removed with shared accounts | Vaults are not in the Lean app. The admission rules of `SEC-009`, `SEC-019` and `SEC-020` are `Lean/Winnow/Wallet/SpendReview.lean`, checked by `multisig-test`'s `MultisigAccountTests` |
| `MuSig2SessionSafetyTests`, the MuSig2 cases of `VaultInteropDiffTests` | removed with MuSig2 | None: the Lean app signs no MuSig2, and a backup carrying a MuSig2 account is refused (`Lean/Winnow/Wallet/ImportBundle.lean`) |
| `DifferentialTests` (`TransactionDiffTests`, `VaultInteropDiffTests`, `PSBTConversionDiffTests`, `FullLoopDiffTests`, `FilterSyncDiffTests`) | retired | Against a regtest Bitcoin Core (`scripts/ci-regtest`): `multisig-differential`, `segwit-regtest`, `card-regtest`, `io-test` and `backend-test`. The seeded 40-transaction `decoderawtransaction` corpus was not found |
| `WinnowFuzz`, `FuzzRegressionTests` | in `ToolsTests` | `fuzz`: 30 targets, with the saved inputs under `Lean/Vectors/fuzz` replayed at the start of each run |
| `WinnowSoak` | `winnow-debug soak` | None: this tree has no soak tool |
| `PeerGatewayTests`, `TailnetGatewayDiscoveryTests`, `RoutingTests` | | `io-test`: the routing gate (comments there name `RoutingTests` and `PeerGatewayTests`), MagicDNS answers and SOCKS5 |
| `PeerGatewaySettingsUITests`, `LiveGatewayDeviceTests` | | Not ported ([PORT.md](../../PORT.md)) |
| The signet journey (`WinnowAppUITests`, `UITests/MultisigJourney.swift`) | | The eleven journeys of `LeanApp/Journeys.lean` on regtest: the 2-of-3 with two Bitcoin Core wallets and its recovery spend is `multisigTwoOfThreeWithRecovery`, the silent payment leg `silentPaymentSend`, the fee bump `feeBumpReplaceConfirm` |
| `StorefrontCaptureTests`, the demo and story tests, `ExternalDisclosureTests` | retired in the Swift app | None |

## What the Swift map recorded

For reading the dated rows: the Swift app's former `BitcoinP2P` target was
folded into `WalletCore`, and its protocol tests moved to
`Tests/WalletCoreTests/Network` with their suite names unchanged. The
store-persistence cases once in `TxBroadcasterTests` moved to
`TxBroadcasterStoreTests`. `WinnowSoak` runs used a standalone executable,
later `swift run winnow-debug soak`; checkpoint generation became
`swift run winnow-debug generate checkpoint`. Bundled-peer generation, its
crawler and `FallbackPeerListTests` were removed; Tor's `SocksProxyTests` were
removed with that transport and returned with the external SOCKS5 transport
(winnow#179). None of this changes the recorded dates, measurements or scope
of historical evidence.
