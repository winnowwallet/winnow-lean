# Winnow app layer: survey for the ElmLean port (2026-10-26)

Source: `Sources/WinnowApp` (AppModel.swift = AM). Condensed from a read-only survey; file:line refs
point at the original.

## AppModel state
- Lifecycle: `stage` (loading | onboarding | ready | storageDamaged msg, AM:39,243); `networkGeneration`
  (AM:322: bumps on suspend/switch/rebuild; older async results are dropped); `httpClient` cancelled on suspend.
- Wallet/network: `wallet`, `stack {pool, chain, filters?, broadcaster}` (AM:122), `walletID`,
  `walletDescriptor`, `status {balance, utxoCount, history, feeBumpableTxids, observedFeeRates, peerCount,
  tipHeight, nextScanHeight, syncing, lastSyncError, relayStoreQuarantined, feeFloorSatPerVByte}` (AM:101),
  `syncPhase` (idle | connecting(c,t) | headers(s,est) | filters(s,tip) | synced | peerDiscoveryFailed, AM:131),
  `peersToAvoid`.
- Census: refreshingCatalog, catalogBytes, catalogNotice, catalogError.
- Settings (UserDefaults): network, manualPeers, esploraURLString, explorerProvider (blockstream|mempool|custom),
  verifyFromGenesis, advancedMode, ownDisplayName, torRemovedNotice.
- Vaults `[VaultRecord]` (didSet → recomputeSharedSavings, ownedVaultScripts); people `[PersonRecord]`
  (didSet → recomputeSharedSavings, recipientByScript); senderByTxid; sharedSavings; peopleStorageNotice.
- Receive labels `[script: note]` + notice; ownWatchScripts; operationsInFlight (exclusive spending, AM:1787).

## Methods (→ commands in the port)
boot (AM:470) · retryWalletOpen · scenePhaseChanged · retryPeerDiscovery · syncNow/syncOnce (AM:954) ·
refresh (AM:1033) · createWallet (AM:1115) · importWallet (AM:1148) · exportWalletBundle (AM:1215) ·
finishOnboarding · pendingBackupMnemonic · revealMnemonic · destroyWallet (AM:1393) ·
currentReceiveAddress / freshReceiveAddress (AM:1459) · setReceiveAddressLabel · previewSend (AM:1695/1722) ·
send (AM:1802) · prepareVaultApproval (AM:1752) · pendingFeeRate / previewFeeBump / bumpFee (AM:1852) ·
rawTransactionHex · setAdvancedMode · vault ops (ownKeyExpression, addVault, removeVault, createVaultSpend,
reviewVaultSpend, partialSignVaultSpend, finalizeAndBroadcastVaultSpend, broadcastVaultSpend,
advanceVaultReceiveIndex, withMasterKey AM:2435) · people ops (addPerson, attachDestination, updateRecipient,
labelReceivedSender, removeReceivedSenderLabel, loadPaymentDetails AM:2191, nextPaymentAddress, ownPersonCard,
setOwnDisplayName) · shared savings (create AM:2221, add card, card for) · settings (switchNetwork AM:2507,
add/remove manual peers, reconnect, refreshPeerCatalog AM:2612, resetPeers AM:2642, setVerifyFromGenesis,
setEsploraURL, setExplorerProvider, explorer URLs, sender lookup AM:2763, pasteboardText AM:463).
Auth gate: authenticateSensitiveAction (AM:2457), 60 s grant revoked after each operation.

## Background loops
syncTask every 45 s (AM:935) · phaseTask every 1 s (AM:604) · broadcaster events (AM:907) · mempool windows
owned by Receive and Send status. Scene phase: active → activate (build stack, start loops); background →
revoke auth, stop networking (stack = nil); inactive keeps syncing.

## Persistence
`ApplicationSupport/BTCSwift/<network>/` (excluded from backup; atomic writes,
completeUntilFirstUserAuthentication): wallet.json, headers.bin, filters.json, peers.json, broadcast.json
(+ broadcast.damaged.json), vaults.json and people.json sealed as `winnow-store-mac-v1 <HMAC-SHA256 hex>\n<json>`
(MAC over store name + network; keys in Keychain `store-key.<store>.<net>`), receive-labels.json,
rollback.height, mainnet/downloaded-census.json(+.sig). adopt deletes filters, broadcast, vaults,
receive-labels; destroyWallet also wallet.json. Export staging in tmp, swept at boot.
Keychain: wallet secret service `org.btc-swift.wallet`, account walletID, WhenUnlockedThisDeviceOnly +
userPresence. UserDefaults keys: network, manualPeers.<net>, esploraURL.<net>, explorerProvider.<net>,
verifyFromGenesis, advancedMode, ownDisplayName, backupPending.<walletID>; legacy migration (torEnabled →
torRemovedNotice).

## Screens
Root: loading → busy; onboarding → OnboardingView (create, restore/import sheet, resume backup, network
picker; MnemonicBackupView sheet: word grid hidden while captured, copy, written-down toggle, Done);
ready → advancedMode ? MainTabView (Wallet/Send/Settings) : BeginnerHomeView; storageDamaged →
StorageDamagedView (retry, switch network). Global alert: Tor removed.
BeginnerHomeView: balance, sync summary, Retry, Receive/Send sheets, activity (→ PaymentDetailView), shared
savings rows (→ AccountDetailView), Save with someone, Back up; toolbar Advanced (confirm alert).
HomeView: balance, savings + 4 sheet buttons, Sync section, transactions; toolbar Simple, Receive.
PaymentDetailView (recipients, receive labels, sender section, load details, advanced: txid, explorer, bump).
FeeBumpView. SendView (form → review with 4 warnings → status with relay log). SettingsView (network,
backup, advanced: census, peers, reset; manual peers; explorer; verify-from-genesis; about; papers; delete).
ExportBundleView, BackupSection, RevealPhraseView. ReceiveView (label editor first, QR, copy/share/new address,
explorer, unconfirmed rows; ShareMyCardView). SavedRecipientsView, AddPersonView (modes: recipient, co-owner,
sender label, attach destination), AccountDetailView, VaultCreateView, SharedSavingsCreate/Share/Add,
ApprovalView (VaultSpendSession), MuSig2SignView, DesignPapers (bundled HTML).

## Platform behaviour to keep
Privacy cover when not active (the native shell does this) · screen-capture hides phrase grids · sensitive
results accepted only with a current epoch token and not backgrounded; sensitive sheets clear on background ·
clipboard: recovery phrase local-only 120 s, interchange 300 s · ShareLink, openURL behind warnings, QR (M),
number pads, pull to refresh · no haptics · E2EMode is the UI-test harness (DEBUG only) · accessibility
identifiers are used by UITests (keep them as node ids if the UI tests are ever pointed at the Lean app).

## Port design
Sub-models: App, Settings, Sync, Onboarding, Backup, Receive, Send, FeeBump, PaymentDetail, People, Vaults,
SharedSavings, Approval, MuSig2 (secret nonces never in the Model), Papers. Rules: epoch-tagged sensitive
results; generation-tagged network results; `spendingInFlight` flag; pre-derived data in the Model
(recomputed when wallet/people/vaults change); port the already-pure helpers as-is (historyForDisplay,
labeledReceiveOutputs, paymentRecipients, senderCandidates, SendPreview.authorizes, FeeProportion,
explorerBaseURL, isLoopback, parsePeer, networkScopedSettings, migrateLegacyNetworkSettings, SyncPhase
summaries, shouldObscureWallet, SendReviewInputs, VaultThreshold.reconciled).
Commands: wallet (open, create, import, export, mnemonic, address, preview/send, fee bump, payment details,
snapshot), network (start/stop stack, retry, reset peers, sync once, ticks, broadcaster events, mempool
window, raw tx, census, sender lookup), vaults/people (all mutations), storage (defaults, staging), iOS
(auth, keychain, clipboard with policy, share, open URL, screen-captured, scene phase).
