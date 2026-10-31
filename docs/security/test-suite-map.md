# Current selectors for historical test evidence

The September consolidation moved retained tests into focused suites; later
cleanup also deleted obsolete features and broad integration suites. Dated
findings keep their original commands. Use the mappings below for retained
coverage, not as a promise that every historical case still exists.
Check that a filtered run executes the intended tests; an empty selection is
not evidence. App tests run in the Xcode test host, not through SwiftPM.

| Historical SwiftPM suite | Current suite |
| --- | --- |
| `VaultFlowTests`, `VaultThresholdTests`, `PSBTMultisigTests` | removed with shared accounts (single-key build) |
| `VaultCosignerIdentityTests`, `VaultDraftIdentityTests`, `VaultSignerIndependenceTests` | removed with shared accounts (single-key build) |
| `SpentCoinTombstoneTests`, `ReorgRollbackTests` | `WalletReorgTests` |
| `CoinSelectionPropertyTests`, `FeePolicyTests` | `CoinSelectionTests` |
| `AntiFeeSnipingTests` | `TransactionBuilderTests` |
| `ImportBundleBoundsTests` | `ImportBundleTests` |
| `SighashBIP341ScriptPathTests` | removed with script-path signing (single-key build); the key-path pins stay in `SighashBIP341Tests` |
| `LoopbackTests`, `FilterSyncPersistenceTests`, `FilterProgressRollbackTests`, `FilterMatchingTests` | `FilterSyncTests` |
| `CheckpointMajorityTests`, `PeerDisagreementTests`, `CrossSourceCheckTests`, `CheckpointHangupTests` | `FilterSyncAdversaryTests` |
| `PeerCooldownTests`, `StaleTipEvictionTests` | `PeerPoolTests` |
| `PeerDiversityTests`, `SeedResolverTests` | `PeerPolicyTests` |
| `MainnetCheckpointTests`, `CheckpointStartTests`, `HeaderStartPolicyTests`, `HeaderReplayTests`, `ReorgVisibilityTests` | `HeaderChainTests` |
| `HeaderStorageAppendTests`, `HeaderStorageCorruptionTests`, `HeaderStorageBoundsTests` | `HeaderStorageTests` |
| `TxBroadcasterBackoffTests`, `FeeFilterAnnouncementTests` | `TxBroadcasterTests` |
| `TxBroadcasterReorgTests` | `TxBroadcasterStoreTests` |
| `WireFormatTests`, `MessageTests`, `FramingTests` | `WireTests` |

The store-persistence cases formerly in `TxBroadcasterTests` are now in
`TxBroadcasterStoreTests`; relay cases remain in `TxBroadcasterTests`.
`MuSig2SessionSafetyTests` was removed with MuSig2 in the single-key build.
`WinnowGenerateTests` and the fuzz suite retain their names in `ToolsTests`.
The demo/story tests were retired with that feature; the subprocess
output-drain regression is retained in `DebugSystemTests`. The unused `BlockchainBackend` module and its two
Esplora/disclosure suites were subsequently removed: their four tests covered
only the deleted client, not GUI explorer links or wallet networking.

Historical `WinnowSoak` runs used the standalone executable. The same driver
now runs as `swift run winnow-debug soak`; the retained checkpoint command now uses
`swift run winnow-debug generate checkpoint`. Bundled-peer generation and
its crawler were removed, along with `FallbackPeerListTests`; Tor’s
`SocksProxyTests` were removed with that transport and returned with the optional external SOCKS5 transport (#179). Neither command migration rewrites the
recorded dates, measurements, or scope of historical evidence.

Gateway routing (#181) added `PeerGatewayTests`, `TailnetGatewayDiscoveryTests`
and routing cases in `RoutingTests` under WalletCoreTests/Network,
`PeerGatewayModelTests` in AppTests, and `PeerGatewaySettingsUITests` plus the
opt-in `LiveGatewayDeviceTests` in UITests.

Background chain checks (0.7.12) added `BackgroundSyncTests` in AppTests. They
run the task lifecycle without iOS scheduling it; whether and when iOS starts a
check is observed only on a device.

## Wallet/network consolidation

The current WalletCore target contains the former BitcoinP2P target.
Its protocol tests now live in Tests/WalletCoreTests/Network and use the
WalletCoreTests target; their suite names and assertions remain. Shared vector
resources are in Tests/WalletCoreTests/Vectors. Historical audit records above
keep the module and path names of the revision they describe.

See the [testing policy](../testing.md) for current ownership. The obsolete
one-shot Wallet.send test, StorefrontCaptureTests, broad UI stories and all
`DifferentialTests` were retired. One [iPhone journey](../../UITests/README.md)
checks one ordinary payment against Core. It does not
repeat the old differential corpus or fee-replacement UI journey. Lower-level
wallet, authorization, RBF and parser regressions remain.
