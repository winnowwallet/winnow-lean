# Winnow in Lean: the port

Goal: all of Winnow written in Lean 4 (ElmLean for the app), with **no Swift**: since 2026-10-27 the
app compiles no Swift at all, not even generated.
This file is the plan and the status board; it is updated as each module lands.

## What "no direct Swift" means here

* Every line of `Sources/WalletCore` and `Sources/WinnowApp` is replaced by Lean: wallet logic,
  crypto, networking, storage, timers, and the app's `Model`/`Msg`/`update`/`view`.
* The Lean code is compiled by Lean's own compiler to C and linked into the iOS app together with
  Lean's runtime and standard library (`libleanrt`, `libInit`, `libStd`, `libuv`, `libgmp`), retargeted
  to iOS. Networking uses Lean's libuv TCP; there is no Swift networking.
* **No Swift.** The app compiles no Swift: not Winnow's, not the framework's. The only code besides the
  Lean-generated C is **generic ElmLean framework code**, the same for any app: a C shim (runtime
  start-up, callbacks) and the shell, an **Objective-C/UIKit** renderer of the view tree Lean produces,
  the store around the shim, and a capability host for what only iOS can do (Keychain, Face ID /
  passcode, clipboard, share sheet, bundled pages). Winnow names none of its types. The shell is
  **generated and never checked in**: the framework holds it as Lean data (`framework/lean/ElmShell`), and
  `ios_lean_sources.sh` has `lake exe elmshell` print it into `LeanApp/ios/build/native-shell/`
  (gitignored: `ElmLeanShell.h` and five `.m` files) on every build. Its grammar-dependent parts (node
  decoding, the render dispatch, enum values, events, the capability dispatch and its doc table) come from
  tables that the framework's build checks against `Wire.toJson` and `Event.fromJson?`.
* **How this was decided (2026-10-27).** The first step made the shell's Swift generated and uncommitted
  (the user: generated Swift is fine, provided it is not checked in). Asked whether that meets "no direct
  swift", the user answered **"No Swift at all"**, so the shell was rewritten as Objective-C on UIKit,
  still printed from Lean. The Xcode project has no Swift settings (`SWIFT_*`, bridging header) and a scene
  manifest naming `ELSceneDelegate`; a scene saved by an earlier SwiftUI build is adopted by the shell's
  delegate, so an update does not open on an empty window.
* This is ElmLean's **native mode** (full Lean, compiled to C, generic renderer). It brings back a
  generic in-process renderer, which was dropped earlier in favour of generated SwiftUI; the difference
  from the dropped served mode is that there is no server and no second process. ElmLean keeps its
  **generated mode** (elmgen, subset apps such as Todo, Counter, Send) alongside.

## Scope

* Ported: `Sources/WalletCore` (≈18,100 lines) and `Sources/WinnowApp` (≈9,900 lines).
* **Removed (2026-10-27, at the user's request):** the Swift original and everything that compiled
  against it — `Sources/`, the Swift tests (`Tests/`, `AppTests/`, `UITests/`), `Package.swift` and its
  lockfile, the Swift app's `project.yml`, the Swift tools (`Tools/Debug|Fixture|Fuzz|Generate`), the
  Swift-app CI/release/site scripts and `.github/workflows`. The tree holds no `.swift` file; the only
  Swift in the app is the generic ElmLean shell, generated at build time (above). The original remains in
  history at `9cca3fc`.
* **During the port** the Swift WalletCore was the **oracle**: for each module, a Swift driver exercised
  the original and a Lean CLI answered the same requests, compared step by step. The results below were
  recorded against it. The harness (Swift drivers, `gen/*.py`, `lockstep.py`, the Swift `Package.swift`
  with the oracle products) was moved out of the tree to `~/src/winnow-lean-swift-archive/LeanOracle`
  ("`LeanOracle/…`" in Lean comments means that harness); to rerun it, restore `Sources/` from `9cca3fc`
  next to it. The Lean-side oracle executables (`Lean/Oracle*.lean`, `LeanApp/Oracle*.lean`) are kept.
  `io-test --swift` likewise needs the archived `oracle-io`; without it `io-test` runs its 73 Lean checks.
* Platform APIs replaced: CryptoKit / CommonCrypto / P256K → Lean crypto; Network → Lean TCP;
  CoreImage QR → a QR encoder in Lean and a `qr` node; WKWebView (bundled design papers) → a generic
  bundled-page node; Security (Keychain), LocalAuthentication, UIKit pasteboard/share → capabilities.

## Known fragility

* The runtime libraries are macOS arm64 objects with their Mach-O `LC_BUILD_VERSION` rewritten to the
  iOS simulator (`retarget_ar.py`). Lean does not support this. Verified: the simulator runs Lean code
  with GMP, tasks and libuv TCP (2026-10-26). Device (platform 2): the app links and archives for
  `generic/platform=iOS` (2026-10-27, `scripts/build-ios Release ios`, unsigned); not run on a device. The
  first TestFlight build is the first time Apple's processing and a device see it.
* iOS suspends background apps and drops sockets: the peer layer needs reconnect-on-foreground.
* HTTPS (census catalog, DNS-over-HTTPS, explorer) cannot be Lean: Lean's runtime links OpenSSL but exposes
  no TLS API, and `Std.Http` is server-only. It is the generic shell capability `http.get` (URLSession,
  ephemeral, same-host redirects only, never https→http); `RoutedHTTPClient`'s policy is ported to Lean.
  Bitcoin P2P is plain TCP and stays Lean (libuv).

## Tracking upstream 0.8.13 and the Ledger signer

On 2026-10-27 the user asked for the port to follow the newer upstream: winnowwallet/winnow#255
(`ledger-on-main`, 1cf93fb, "Ledger Nano X as a signer of Taproot multisig accounts"), which is on
upstream `main` at 0.8.13 (#252: raw Taproot multisig accounts in Advanced mode replace vaults). That is 43
upstream commits after this port's base: upstream's f4bab06 has the same tree as 9cca3fc. The Swift
changes are Sources/WalletCore 60 files (+6,593/−4,217) and the app 35 files (+4,466/−3,545). No new
third-party dependency.

- Branch `lean-port-ledger`. Its merge commit 5acf15d has 1cf93fb as a parent and applies exactly
  `f4bab06..1cf93fb` minus the Swift sources, tests, tools and workflows, so a PR based on `ledger-on-main`
  shows only the Lean work.
- Oracle: the Swift at 1cf93fb, checked out at `~/src/winnow-ledger` (kept pristine). The lockstep harness in
  `~/src/winnow-lean-swift-archive/LeanOracle` builds its oracle products against that checkout's `Sources/`.

| Phase | Upstream Swift | Status | Verified by |
|---|---|---|---|
| A. Removals | Vault, VaultRecord, VaultSetup, MuSig/MuSig2 descriptors, CensusSignature, CensusCatalogStore, FallbackPeersGenerated; the app's vault, shared-savings and MuSig2 screens and stores; their parts of People, PSBTRoles, Descriptor, ImportBundle (a bundle with a MuSig2 account is refused) | **done** (91c6e91, dc439e3): a bundle with accounts is refused (`unsupportedWalletData`); the census is the list shipped with the build (`CensusCatalog.bundled`), but importing it into the iOS build (scripts/import-census plus a resource line in project.yml) is still to do | every Lean target builds; records-test 99/99, backend-test 76/76, io-test 71/71; the simulator app builds and launches |
| B. WalletCore: multisig | Descriptor and Script/Multisig changes (`tr(NUMS, sortedmulti_a(k, …))`, `tr(KEY,TREE)` as `trTree`, timelocked recovery leaves), MultisigAccount, PSBTRoles (multi-leaf, lock-aware signing and finalizing), HistoryOutputs, account-key secrets, FeePolicy's capped resolution | **done** (`Lean/Winnow/Wallet/MultisigAccount.lean`, `Tx/Multisig.lean`, …) | `multisig-test` 464/464: all of upstream's MultisigAccountTests, TimelockedMultisigTests, HistoryOutputTests, the BIP341 script-path vectors and Core's timelocked-multisig vectors, account secrets, fee resolution. `multisig-differential` (upstream's check-multisig-core in Lean): 1,036 agreements and 0 disagreements with Bitcoin Core v31.1.0 over 24 regtest cases (addresses, every k-of-n subset, finalizer bytes, mempool and mining, recovery locks a block early and on time). The Swift lockstep was not rerun: the archived drivers predate 1cf93fb |
| C. Ledger protocol | LedgerAPDU, LedgerBluetoothFraming, LedgerMerkle, LedgerWalletPolicy, LedgerClientCommands, LedgerBitcoinClient, LedgerMultisig, Tests/Support/LedgerSimulator | **done** (`Lean/Winnow/Ledger/`): the client is a pure resumable `Ledger.Program` over one APDU exchange; the simulator is in the library for tests and test mode | `ledger-test` 199/199: all of upstream's LedgerTests, Ledger's 15 policy ids and 6 Taproot addresses, and sessions recorded from the Swift at 1cf93fb (its client against its simulator, 2-of-2 and 2-of-3 with recovery) replayed byte-exact on both sides, the signed PSBTs included. The Swift recorder is kept outside the tree (`~/src/winnow-lean-swift-archive/LedgerRecorder/`) |
| D. App | MultisigStore, AppModel's multisig and Ledger operations, MultisigViews, MultisigBuildView, LedgerViews, LedgerBluetooth's transport | **done** (`LeanApp/WinnowApp/Multisig.lean`, `Real/Multisig.lean`, `Real/MultisigStore.lean`, `Real/LedgerTransport.lean`); the Ledger is `openLedger` over the shell's `ble.*`, or in Debug test mode (`WINNOW_E2E_LEDGER`, entropy hex) the simulated device | `multisig-app-test` 150/150 (MultisigStoreTests, MultisigAccountFlowTests, LedgerPairingTests, LedgerBluetoothTests); `ledger-transport-test` 13/13 (the transport against a fake peripheral backed by the simulator, frame sizes 23 and 153, each failure text); `backend-test` 126/126 against regtest: a 2-of-2 spent by the phone and a second key, and two Ledger accounts (2-of-2, and 2-of-3 with recovery) paired, verified on the device, funded, signed by the Ledger and the phone, broadcast and confirmed, exported and restored. Simulator (test mode, regtest): a simulated Ledger paired, an address verified, a spend signed by Ledger and phone, and the node's mempool held exactly that txid. No real Nano X has been used |
| E. Shell capability | Bluetooth LE (GATT) for the Ledger: generic `ble.state/connect/subscribe/write/read/close` rows in ElmLean's shell (`framework/lean/ElmShell/Capabilities.lean`, Objective-C/CoreBluetooth), not Winnow code | **done** (framework 015dc2d) | both apps build with no Swift; in the simulator (no Bluetooth) `ble.state` answers `unsupported` and the app shows Swift's text. Not run on a device with a radio |

Scope, as the user set it on 2026-10-27: the Ledger signer and the Taproot multisig ("ledger, and the fancy
multi, no need for musig2 right now"). The other upstream changes in this range were deferred then;
automatic iCloud backup, background checks, the app side of the Tor/I2P gateways and the onboarding
without a phrase checklist are ported since (see "The rest of the app" below). **Restore-only range scans (RangeScan, upstream #226) are done** (091b35e:
`Winnow/Net/RangeScan.lean`, `FilterSyncIO.scanRange` in `Winnow/IO/Filters.lean`). **The census shipped with the build is done** (2026-10-27): `project.yml`
bundles `build/census/peers.json` (fetched by `scripts/import-census`, which `scripts/build-ios` runs when
the list is missing), `CensusCatalog.bundled` reads it, and the UI test `testShippedCensus` requires
Settings on mainnet to show the list's date and count. **Silent-payment sending is done** (2026-10-27):
`Winnow/Keys/SilentPayments.lean` (the code and the BIP352 derivation; `silent-payment-test`, 263 checks,
every official sending vector), `Wallet.buildSend` derives the outputs after coin selection and the review
gate binds them (multisig-test's SilentPaymentSendTests), the Send screen takes a code, notes that the
address is derived and shows it on the receipt; backend-test and the UI test `testSilentPaymentSend` hold
the node's transaction to a receiver written from the BIP's receiving side, and Core's watch-only wallet
finds the coin. A person can be paid by a code (People's `.silentPayment` pay-to: pasted, on a card,
identified by its two keys; upstream's PeopleTests case in `silent-payment-test`). As upstream, the review
of a payment to such a person shows the reused-address warning (the code has no payment index), and
Activity does not name the person on a code's output (the Lean history rows carry no code).

The layer table below was written for the 0.7.3 port. Phase A removed its MuSig2 (layer 4), musig()
descriptors and MuSig2 rounds (layer 7), vaults and vault records (layer 8), fallback peers and the signed,
downloaded census (layer 9), and VaultStore, shared savings and approvals (layer 10). Phases B–E then added
Taproot multisig accounts and the Ledger. Test counts on this branch, all rerun on its final tree
(2026-10-27): multisig-test 464, ledger-test 199, io-test 71, records-test 99, multisig-app-test 150,
ledger-transport-test 13, backend-test 126 (regtest), and multisig-differential with 0 disagreements against
Bitcoin Core (24 cases, 1,036 agreements, in the Phase B run; 3 cases, 92 agreements, in the final rerun).
The iOS app builds with no Swift. In the simulator, test mode paired a simulated Ledger and verified an
address on it.

The simulator has no Bluetooth, so phases D and E are verified with a test-mode fake and the pure oracles.
A device run with a Ledger is not claimed until one happens.

## Tracking upstream "one wallet" (#259, with #256 nested multisig)

The next upstream step is winnowwallet/winnow#259 at d2ca878, which includes #256 (nested multisig).
Oracle: the Swift at d2ca878, checked out read-only at `~/src/winnow-onewallet`; the diff against the
previous oracle is `git -C ~/src/winnow-ledger diff 1cf93fb d2ca878 -- Sources/WalletCore Tests`. The merge
commit db4cb1d brings the docs and release scripts; the Swift is ported in the commits after it.

| Piece | Upstream Swift | Status | Verified by |
|---|---|---|---|
| #256 nested multisig, WalletCore | MultisigAccount (`Member`, `descriptor(members:…)`, `SpendPath` with leaf positions, `signersLeaves`/`recoveryLeaves`, `members`/`recoveryMembers`, `policySummary`, `signerKey`, `signerExpressions`, 32 leaves at most), LedgerMultisig (`hasLedgerSigner`, `namesALedgerKey`, the signer looked up over every key), LedgerWalletPolicy (any tree, 512-character template, 15 keys), the simulator's limits, SignerRecord, ImportBundle.signers | **done** (`Wallet/MultisigAccount.lean`, `Wallet/SignerRecord.lean`, `Ledger/`) | `multisig-test`: all of NestedMultisigTests without a Ledger, ImportBundleTests.signers; `ledger-test`: the three Ledger cases (one and two simulated Ledgers, the 335- and 368-character policies, 27 leaves refused); `multisig-differential` against Bitcoin Core v31.1.0 (default seed, 24 cases, five of them nested, among them 2-of-3 and 1-of-3 members and a 1-of-2 of pairs): 1,321 agreements, 0 disagreements |
| #259 one wallet, WalletCore | HistoryLedger (lifted out of Wallet, which calls it), MultisigSpendDraft and InFlightSpend, MultisigAccountRecord's `history`/`draft`/`inFlight` (each omitted when empty), ImportBundle's account bounds | **done** (`Wallet/HistoryLedger.lean`, `Wallet/MultisigSpendRecords.lean`) | `multisig-test`: HistoryLedgerTests, an old record encoding byte for byte, the spend records' coding and refusals, the bounds. Counts on this tree: multisig-test 664, ledger-test 230; records-test 99, multisig-app-test 150, ledger-transport-test 13 unchanged |
| #256 app | SignerStore (`Real/SignerStore.lean`: sealed `signers.json` per network, 100 signers, 1 MiB, kept when a wallet is deleted, in every backup, merged on import) and Settings → Signers (`Signers.lean`: this phone, Ledgers, saved keys, detail; Pair a Ledger files the Ledger's key and registers nothing); each Advanced tab its own navigation stack; the builder over members (This phone, Ledgers, saved keys, accounts on this phone, pasted keys, ⊕ a co-key, any k of N members, the preview line, the paired Ledger registering after Create with Register on Ledger on failure); Join's Ledger notice, member share and registration; the account screen's members and Ledger | **done** (`LeanApp/WinnowApp/Real/{SignerStore,Multisig}.lean`, `Signers.lean`, `Multisig.lean`). Deviations: the recovery delay defaults to 26,000 blocks (about six months; the user's choice), adjustable a day at a time; the signers' threshold stays at 2 while only this phone is a member (upstream's `onChange(of: members.count)` lowers it to 1 when the builder seeds this phone, so an account built without touching the stepper is any 1 of its members) | `multisig-app-test`: SignerRosterTests (4), NestedMultisigFlowTests (3), LedgerPairingTests as upstream changed them; `backend-test`: the builder and the Ledger flows on regtest |
| #259 app | MultisigStore's history (HistoryLedger), settle, recordSpend with the broadcast height, drafts, abandon, rollBack rewinding history, backups carrying pending payments; `Status.accountsBalance` and the one balance with its "of which…" line (Simple and Advanced); DisplayedPayment (`Payments.lean`) as the one Activity/Transactions list; the payment screen's Account section (Collect signatures, Rebroadcast, Give up); Send's From (Advanced), the account review through the wallet's gate (override band, relay floors, `authorizes` on the unsigned PSBT, account id in the review identity, silent payment codes refused), Sign and continue (one device authentication), one collection step from Send, Transactions and the account page (phone, Ledger, pasted copy, PSBT to share, finalize with the main path's relay watch and receipt, discard); the account page shrinks to the recovery path and a pasted PSBT, both filing the draft (since taken away: see Deliberate departures) | **done**. Simple mode gains nothing: accounts show only in the balance line and as rows without actions, a draft row saying its signatures are collected in Advanced mode | `multisig-app-test`: MultisigStoreTests as #259 changed them (the backup test inverted), the draft lifecycle, MultisigAccountFlowTests (Send tab across two phones, a transfer is one row, an in-flight spend survives a backup and can be rebroadcast or given up), HistoryDisplayTests' merge, SendReviewBinding's account identity, a Simple-mode render test and the tab stacks; `backend-test`: a Send-tab account spend on regtest and a wallet→account transfer as one row |

### Fixed upstream bugs

Bugs in upstream d2ca878 that the port fixes rather than copies (each with a test):

1. **The PSBT given to share must be BIP174 v0.** #259 writes `psbt.base64` (the v2 envelope) into the
   account's draft (`AppModel.signAndDraftMultisigSpend`, `updateMultisigDraft`, Sources/WinnowApp/AppModel.swift
   2522 and 2559) and shares the draft's text as "PSBT to share" (MultisigViews.swift 695); before #259 it
   shared `base64V0()`. Bitcoin Core and most other signers read only v0. Here `MultisigSpendDraft.ofPSBT`
   writes the v0 envelope (`PSBT.base64V0`), and every draft the app files goes through it
   (`Real/Multisig.lean` `draftOf`). **Fixed.** Tests: multisig-test (the draft's text is v0 and reads back as
   the same spend); multisig-app-test `testSendTabSpendsFromAnAccountAcrossTwoPhones` and
   `testDraftsFollowTheirCoins…` (the filed draft is v0); backend-test "the shared text is BIP174 v0".
2. **Draft signature counts are compared by number.** Upstream's `draftRow` (Sources/WinnowApp/DisplayedPayment.swift
   93–109) picks the "best leaf" text with `.max { lhs.count < rhs.count }` over strings like "2 of 3": the
   longest text wins, so an untouched twelve-key leaf ("0 of 12") is shown over a leaf that is two of
   three signed ("2 of 3"). Here `bestLeafSignatures` (`WinnowApp/Pure.lean`) takes each path's (approvals,
   threshold) and shows the path needing the fewest further signatures, ties broken by the most approvals,
   then by the first path. **Fixed.** Test: multisig-app-test `testTheDraftRowShowsTheLeafClosestToFinishing`.
3. **A person's address index advances when the account spend confirms, whoever broadcast it.** Upstream
   advances it only in `broadcastMultisigDraft` (AppModel.swift 2572–2576), i.e. when this phone
   broadcasts; when a co-signer broadcasts, `MultisigStore.pruneDraft` (MultisigStore.swift 488–500) drops
   the draft, with its `personID` and `paymentIndex`, once its inputs stop being live coins, and the index
   never moves, so the next payment reuses the address. Here `MultisigStore.applyPaying` reports the
   `(personID, paymentIndex)` of each draft whose own transaction the block confirms, and the app's
   `multisigApply` hook advances that person's index (and still advances it on this phone's own broadcast).
   **Fixed.** Tests: multisig-app-test `testADraftConfirmedByACoSignerPaysItsPerson` (store) and
   `testACoSignersBroadcastAdvancesThePaidPersonsIndex` (the hook).

Also found while porting (not one of the three above): upstream's builder lowers its threshold to 1 as it
seeds this phone as the first member (see the #256 row), so the default account is any 1 of N. The port
keeps 2 (`MultisigBuildForm.clamp`; multisig-app-test `testTheBuilderStartsAtAnyTwoMembers`); the UI
journey found it.

## Deliberate departures from upstream (user, 2026-10-28)

These screens differ from upstream d2ca878 on purpose: the user, testing on their iPhone, rejected
upstream's versions ("No reason to have a bunch of different send screens"; "You get simple by taking
away"). They are not to be restored or re-ported for fidelity.

1. **One Send; the account page has no payment form.** Upstream's MultisigPSBTView keeps its own "New
   payment" form (Spend with, address, amount, fee rate, Create PSBT) and an "Or paste a PSBT" text field, and
   MultisigAccountView prints the whole descriptor. Here every payment starts from Send: when From is an
   account with a recovery path, Send shows "Spend with: Signers now / Recovery path" (Advanced only, only
   then), with the caption "Only coins that have not moved for the recovery delay can be spent this way
   (after N blocks: …)." The path is part of the review's identity (`SendInputs.recovery`), the account's
   PSBT is built on it (`previewAccountSend` → `newSpendPSBT … recovery`, which still refuses coins whose
   delay has not passed), and the review says "Spend with: Recovery path". The account page keeps balance,
   policy (and its recovery line), members (without the long footer), the Ledger line or Register on Ledger,
   Receive (Verify on Ledger, New address), "Send from this account" (the Send tab with From preset), "Payment
   awaiting signatures" while a draft exists (the collection step), "Paste a PSBT from a co-signer" (the
   clipboard filed as the draft at once, then the collection step; errors inline), Coins, one "Share with
   co-signers" button ("Everyone who signs needs this to see the account.") instead of the Descriptor text,
   and Remove account. The account's collection page (`.multisigPSBT`) is only the collection step and its
   receipt. Removed with the form: `Cmd.createDraft`, `Cmd`/`Host.multisigFeeRate`, `CollectForm`'s address,
   amount, fee rate and path. `Backend.createDraft` stays for backend-test's Ledger-first leg. Tests:
   multisig-app-test `testOneSendForAccounts`; the UI journey's recovery leg runs on the Send tab.
2. **Plain wording for creating and joining.** Upstream's Multisig footer (60 words of k-of-n, descriptors,
   PSBTs and recovery), "New multisig account" / "Join with a descriptor", and Join's xpub, NUMS and
   `/<0;1>/*` text with its "Copy 2-of-2 template" button are replaced: the footer is "Accounts that need
   more than one signature to spend. Pair a Ledger or save other people's keys in Settings → Signers.";
   "Create an account" ("You choose who signs, then share the account with them.") and "Join an account"
   ("Paste the account someone shared with you."), ids unchanged; Join's key section says "Send this to
   whoever is creating the account." and its input is "Account" ("Paste the account (tr(…))", "Winnow finds
   coins sent to it from now on."); the builder's long footers are one sentence each (after Create: "Send
   this account to every other signer; each should see the same first address."). Test: multisig-app-test
   `testPlainCreateAndJoinWording`.
3. **Backup, clear and honest.** A build without the iCloud entitlement gets `missingEntitlement` from the
   shell; upstream's text for it is the sign-in one ("Sign in to iCloud and enable iCloud Drive…"), wrong for
   a signed-in user. Here it is its own `CloudBackupError.missingEntitlement`: "iCloud backup isn't available in
   this build of Winnow." (`shellCloudStore.account` reads the error before the status; `notAuthenticated`
   keeps the sign-in text). The reason is no longer prefixed "Not backed up: " under a "Not backed up" status.
   Settings' Backup section shows the iCloud state on its row ("Backed up 5 min ago", "Backing up", "Off",
   "Not available", "Not backed up"), "Back up wallet" is "Save a backup file", and the footer is "iCloud
   backup keeps this wallet automatically. A backup file is a copy you keep yourself." (Simple's Back up page:
   "A backup file is a copy of this wallet you keep yourself.", no iCloud control). The export sheet is
   "Backup file": "Saves a file you can keep in Files or send to yourself. Restore it from Restore from a
   file.", toggle footer "Without the recovery phrase the file restores your history but not the ability to
   spend.", the include-phrase confirmation unchanged; Simple's home says "Your wallet still works. Until
   iCloud backup works, keep a backup file yourself." with "Save a backup file". "Manual backup" is "backup
   file" throughout. The sheets keep their Close row: ElmLean's sheet renders its children in a page
   (`ELPageController`), and only a screen lifts a `toolbar` into the navigation bar. Tests: cloud-backup-test
   `shellAnswers` and the screen checks.

## The rest of the app: gateways, sync bookkeeping, background checks, iCloud backup, onboarding

Ported 2026-10-28 from d2ca878 (the app side of upstream a02727c, 2f983db, 66c6a48, 0eeae72 and 4228c6b), on
ElmLean fbce4c5 (the shell's SOCKS `http.get`, `bgtask.*`, `cloudkit.*`, synchronizable `keychain.*`).

| Piece | Upstream Swift | Lean | Verified by |
|---|---|---|---|
| Peer gateways | PeerGatewaysSection, PeerRoutingBanner, `preparePeerGateways`, `setPeerGatewaySettings`, the settings' `peerGatewaySettings` (an unreadable value is offline), `candidateCount(networks:)`, the peers' network labels, the Tor-removed notice, `WINNOW_E2E_LIVE_GATEWAYS`, `NSLocalNetworkUsageDescription` | `Real/Stack.lean` (`preparePeerGateways`: once per generation, one shared discovery, the pool's gateways and dial timeout, `RoutedHTTPClient.ofGateways`), `Settings.lean`, `Home.lean`, `Pure.lean` | records-test: PeerGatewayModelTests (all seven), the banner on the Simple screen; backend-test: Manual Tor-only never dials the regtest node, Direct only and Automatic reach it |
| Sync bookkeeping | `recordSyncFailure`, `simpleSyncError`, `lastCompleteCheck`, ChainCheckStatus | `Real/Stack.lean` (`syncOnce` returns completeness, counts transient failures), `Home.lean` | records-test: the Simple/Advanced screens, `relativeAgo`; backend-test: a background check records the time |
| Background checks | BackgroundSyncScheduler (identifiers, 15-minute requests, the 25/120 s budgets), BackgroundSyncRun, `runBackgroundSync`, `backgroundRoutingAllowed`, `UIBackgroundModes`, `BGTaskSchedulerPermittedIdentifiers` | `Real/BackgroundSync.lean`, the model's `bgtask` events and scene-driven networking | records-test: BackgroundSyncTests (all nine; the two sync-error ones were ported before); backend-test: a bounded background scan reaches the node's new tip and leaves nothing running, refused while active |
| iCloud backup | CloudBackupController, ICloudBackupStore, ICloudBackupKeys, CloudBackupView, CloudRestoreView, AppModel's iCloud extension, CloudAppState's signers, the entitlements | `Real/CloudBackup.lean`, `Real/CloudApp.lean`, `Backup.lean` | cloud-backup-test: CloudBackupTests (all twelve controller cases), AutomaticCloudBackupTests (all three), a restore from iCloud end to end, the screens |
| Onboarding | OnboardingView without the phrase checklist, BeginnerHomeView's backup line, BackupSection (iCloud and the words in Advanced) | `View.lean`, `Backup.lean`, `Real/Wallet.lean` (the legacy flag cleared at open) | cloud-backup-test: WalletStartupTests' creation, the onboarding and restore screens; backend-test: creation without a checklist and its journal |

Deviations, all forced by the Lean app's shape or the renderer:

* The routing banner has no tint (the renderer's text has no colour); its icon differs per state as upstream's.
* "Chain last checked … ago" is rendered by the backend to the minute ("under a minute", "5 min", "2 hr, 3 min")
  rather than SwiftUI's live relative text. `lastCompleteCheck` (per network) and `automaticUsedGateways`
  (global) are small files beside the wallet and the network directories, not UserDefaults keys.
* Apply routing returns at once (the settings are saved and networking is rebuilt in the background), so
  "Applying…" is never seen.
* Foreground networking now starts only when the shell reports the scene active (upstream's `isActive`):
  a cold background launch opens the wallet without the foreground loop.
* CloudKit failures show the shell's `detail` (not CKError's own localized text); `missingEntitlement` and
  `notAuthenticated` show `ICloudBackupError.unavailable`'s text. Dates are "M/d/yyyy, h:mm AM/PM" in the
  phone's time zone (Std.Time; UTC when the zone cannot be read), not locale-formatted.
* `cloud-backup.json` is written atomically in the backup-excluded directory without Swift's explicit
  `completeFileProtection` (it holds only ciphertext).
* Updates are scheduled on each `refresh` command and when the status watcher sees a changed snapshot
  (upstream schedules in every `refresh()`).
* The model now learns the wallet id after creation and import (before, only at boot).
* BackupSection's, the reveal sheet's and the export sheet's footers follow d2ca878 (upstream #184's
  wording, which the earlier port had missed).

Needs a real device and iCloud account: CloudKit save/list/load and the iCloud Keychain key (the simulator
build carries the entitlement and answers that iCloud is unavailable, which the onboarding shows), a
second device restoring, background task launches and expiry (the simulator refuses `bgtask.schedule`),
Background App Refresh's status, and Tailscale gateway discovery over a real tailnet (UDP to MagicDNS and the
SOCKS probe; upstream's `LiveGatewayDeviceTests`). Not ported: upstream's UI tests for these screens
(`PeerGatewaySettingsUITests`, `LiveGatewayDeviceTests`); the journey's creation step was updated for the
onboarding without a checklist.

## Tests, UI tests, CI and TestFlight

Upstream's Swift tests, UI tests and workflows went with the Swift code; their Lean replacements:

* **Lean tests**: multisig-test, ledger-test, records-test, multisig-app-test, ledger-transport-test, and
  against a regtest bitcoind io-test, backend-test and multisig-differential (Bitcoin Core as the oracle).
* **UI tests**: Objective-C XCUITest in `LeanApp/ios/UITests` (no Swift: the runner is Objective-C too),
  driving the app in test mode against `backend-test --fixture`. Controls are found by id: ElmLean's
  `Html.identified id child` (framework, with the erasure and Sat theorems extended to it) puts `"id"` on
  the node's wire object and the shell sets it as the control's `accessibilityIdentifier`; the views use
  upstream's identifier names where upstream had them. The journeys follow upstream's
  `test01CreateReceiveSendConfirm` (without silent payments) and `MultisigJourney` (the account built in
  the app's builder rather than pasted, so its recovery delay is a day, 144 blocks, not 3), plus a Ledger
  journey on test mode's simulated device. Since #256/#259 (2026-10-28) the multisig journey builds the
  account from members (the Core keys pasted through "Add a member"), pays from it on the Send tab (From:
  the account, Sign and continue, the Core co-signers' copies combined in the collection step) and checks the
  one Transactions row, then spends on the recovery path from the account page; the Ledger journey pairs the
  device under Settings → Signers, builds the account with it as a member (registered on it), funds it from
  the wallet (one "Moved to …" row) and pays from it on the Send tab with the Ledger signing in the
  collection step. Both passed on a throwaway iOS 27 simulator against `backend-test --fixture`. Differences from upstream's harness: the node is regtest, not a
  custom signet; Core co-signers are driven by bitcoin-cli from the runner (posix_spawn, as upstream).
* **CI** (since 2026-10-28): `ci.yml` calls ElmLean's reusable `ios-app` workflow, which builds the Lean once
  and caches it, then runs `tests`, `extra` (`scripts/ci-regtest`) and `app` (the iOS builds and the UI
  journeys) in parallel with live progress, on WarpBuild only (no hosted fallback). Before, `scripts/ci-lane
  lean|regtest|ios|journey` ran four lanes that each built the Lean. The release check replaces upstream's
  `strings`-based release check, which cannot work here (test mode is compiled into every build and
  switched on only when the shell answers Debug): `verify-release-no-test-mode` launches the Release and
  Debug builds with test mode's environment and requires Debug to start the run and Release to ignore it.
  `check-no-swift` fails on any Swift source, compile step or library. The `mac` lane builds the Mac
  Catalyst app and launches its arm64 slice against regtest (`scripts/mac-smoke`).
* **TestFlight**: `release.yml` as upstream's (tag → CI → archive → verify → upload → internal group), as
  `com.btcswift.app`. Not run yet: it needs a tag push. Whether an update from a Swift build keeps its
  wallet (the same Keychain service and storage names, read in place) has not been tried; it must be
  before a tag reaches testers. The tag must also be above the last version uploaded for the app, or App
  Store Connect refuses the build. `asc-jwt` replaces `asc-jwt.swift`;
  `verify-signed-archive` requires the iCloud container with CloudKit again (production iCloud for
  distribution), now that automatic iCloud backup is ported.

## Design, the Mac, and where the app ships (2026-10-28)

* **Design modernization.** The app's look comes from ElmLean's shell, not from Winnow: the Liquid Glass
  shell (ElmLean 92dfea8..6b3d432; pinned at a00d262: 62b27f0 sends only events the view accepts, so a
  row without an action is not selectable and sends nothing, and a00d262 builds the background-task
  completion form only under the iOS 27 SDK, so CI's Xcode 26 compiles the shell) renders lists as inset-grouped tables inside
  the page's scroll view (every row stays in the accessibility tree), gives screens real push and pop by
  their depth, presents sheets as grouped forms with toolbars, and takes `Html.decorated` hints (tone,
  monospaced literals, badges, centring, SF Symbols, chevrons) that change no wire arity. Winnow's views
  use it through small helpers (`formSheet`, `closeBar`, `navLink`, `literal`; f9a3036, 93dfde8). The
  shell stays generic: it names no Winnow type, and it is still printed from Lean and never checked in.
* **Mac Catalyst: deferred (user, 2026-10-28).** A Catalyst build was tried (universal, with Lean's x86_64
  libraries from its official release, Mac entitlements, a CI lane and a release job) and taken out again:
  on the Mac, creating a wallet in an ad-hoc Debug build hung waiting on a capability answer, test mode did
  not start through `open --env`, and the iPad idiom scaled to 77% looked wrong. Until that is worked through,
  the app reaches the Mac as upstream's does: the iPad app on Apple silicon Macs
  (`SUPPORTS_MAC_DESIGNED_FOR_IPHONE_IPAD: YES`). ElmLean keeps its Catalyst support (unused by Winnow).
  iPhone stays portrait-only and iPad keeps all four orientations (ae5bd30).
* **Where it ships.** The app will ship from a new repository, `winnowwallet/winnow-lean`, as one fresh
  commit of the final tree: the same app (`com.btcswift.app`, the same App Store Connect record). This
  branch and PR #260 stay as the history of the port and are not merged. The new repository needs the
  secrets `ASC_KEY_ID`, `ASC_ISSUER_ID`, `ASC_PRIVATE_KEY`, `DEV_CERT_P12` and `DEV_CERT_P12_PASSWORD`
  (set by the maintainer), and the website's `fetch-journey-media` must point at it.

## Census in builds

Every CI and Release build ships the newest census's peer list, verified (2026-10-28).
`scripts/import-census` takes winnowwallet/census at its `main` (or a given commit) and refuses to ship
unless `census/peers.json.sig` is an Ed25519 signature over `winnow-census-peers-v1\0` and the file's exact
bytes by the key pinned in `scripts/census-public-key.txt` (`scripts/ed25519_verify.py`, RFC 8032 in plain
Python; the pin was copied from what the census publishes and is still to be confirmed out of band). It
then drops the clearnet entries the census's 30-day health record (`census/health.json`, model
`observed-consistency-1`, and the nodes artifact whose SHA-256 its name carries) scores under 70 over at
least 3 attempted days, unless fewer than 200 would remain; entries the record does not score are kept. Tor
and I2P are kept as published, though health covers them too: on the 2026-10-27 census the rule would drop
705 of 2,919 onions and 18 of 2,671 I2P names, against 6 of 817 clearnet. When nothing is dropped the signed
bytes ship; otherwise a derived file, the census's own JSON style (checked to reproduce the signed bytes
before removing anything). Lean's `census-check` (`CensusCatalog.readFile`, what `bundled` reads at launch,
50 clearnet entries at least) must accept the result. `build/census/peers-source.txt` records the commit,
the signature and key, the health counts and both files' SHA-256; the CI lanes that import keep it as
evidence, and `release.yml` keeps it and appends its `Peers: census <commit> of <date>` line to What to
Test. `scripts/build-ios` imports for CI (`CI=true`) and Release builds, otherwise only when the list is
missing; `IMPORT_CENSUS=1` forces an import, `IMPORT_CENSUS=0` keeps an existing list. Tests:
`scripts/tests` (the verifier on RFC 8032's vectors; the importer on a signed synthetic census), run by the
`lean` lane with `census-check` on the shipped file.

## Layers and status

Each module is done when its lockstep run against the Swift original passes and its vectors pass.

| Layer | Modules | Status |
|---|---|---|
| 0. Native runtime | ElmLean native mode: C ABI, renderer, capabilities, iOS build | **done (simulator)**: examples/native-demo in ElmLean runs a Lean view, a Lean background task, Lean TCP and the `auth` capability; links for device, not run |
| 1. Bytes | hex, little/big-endian, CompactSize, readers/writers | **done** (`Lean/Winnow/Bytes.lean`) |
| 2. Hashes | SHA-256, SHA-512, HMAC, PBKDF2-HMAC-SHA512, RIPEMD-160, SipHash, tagged hash | **done**: lockstep `a_crypto` OK, seeds 1–5 (3,169 requests per seed at 300 cases) |
| 3. Encodings | Base58(check), Bech32/Bech32m, segwit addresses (GCS filters moved to Net) | **done**: same lockstep |
| 4. Curves | **done**: secp256k1 as WalletCore uses P256K (on the proven `Secp`), BIP340, MuSig2 (BIP327), Ed25519 (RFC 8032) + census signatures — lockstep `b_p256k b_musig b_ed25519` OK seeds 1–3 |
| 5. Keys | **done**: BIP32, BIP39 (+ Foundation-exact NFKD), BIP86, Taproot, KeyStore + in-memory store — lockstep `b_bip32 b_bip39 b_bip86 b_taproot b_keystore` OK seeds 1–3; Keychain store becomes the shell's keychain capability |
| 6. Script, Transactions | wire, transactions, scripts, multisig, addresses, sighash (BIP341), builder, funding sources | **done**: lockstep `c_wire c_transaction c_script c_address c_sighash c_builder c_funding` OK seeds 1–3; BIP341 vectors (23 sighashes) match |
| 7. Descriptors, PSBT | **done**: PSBT format (`c_psbt`), descriptors (`e_descriptor`), Signer + PSBT roles incl. MuSig2 rounds (`e_psbtroles`, whole flows compared step by step) — OK seeds 1–3 |
| 8. Wallet | **done**: fee policy, wallet data types + wallet.json (sorted-keys form), coin selection, export staging, the wallet itself (create/open/import, scan, receive, send, fee bump, reorgs), vaults (multi_a and MuSig2 spends), vault records and setup, people, import bundles — lockstep `e_feepolicy e_types e_coinselection e_descriptor e_psbtroles e_wallet e_vault e_people` OK seeds 1–3 (and 7). Random draws (aux rand, nonces, change position) are compared by shape. Untested: persist-failure paths, the 64 MB state limit; Swift traps on some UInt32 overflows where Lean wraps (inputs avoided). `SwiftJSON.parse?` skips one leading byte-order mark as `JSONDecoder` does (2026-10-27; tested through `f_records` raw-byte prefixes, since the oracle transport's `JSONSerialization` drops one leading U+FEFF from Swift-side string fields); `e_types e_people e_vault e_wallet` rerun OK seeds 1–3. Swift `Character`s (`Wallet/Characters.lean`): the full UAX #29 segmenter (GB9b Prepend, GB9c Indic conjuncts, GB11, SpacingMark incl. Thai/Lao SARA AM) over property tables measured from Swift 6.4 itself (`Tools/LeanOracle/Characters/tables.py` regenerates `CharactersData.lean`); fuzzed against Swift with ~1.35 million strings, 0 disagreements. The Keys area's `split(separator:)` (BIP39 words, key-store lines) now splits on those `Character`s too (lockstep `b_bip39` with joining-separator cases, `b_keystore` OK seeds 1–3) |
| 9. Network | data **done**: GCS filters, UInt256, headers + HeaderChain (retarget, reorg, storage), params, fallback peers, addresses, inventory, framing, blocks, messages, FilterSync/MempoolWindow pure logic — lockstep `d_gcs d_headers d_protocol d_filters` OK seeds 1–3 (BIP158 vectors, 2,000 mainnet headers); I/O **done** (`Lean/Winnow/IO`: transport over libuv TCP, peer pool, seeds, diversity, census, header/filter sync, mempool window, broadcaster, HTTP policy with injected fetch): `io-test` 83/83 against a fresh regtest bitcoind, and Winnow's Swift against the same node gives the same tip, matches, filter header and byte-identical headers.bin; gaps listed in `IO.lean` (live HTTPS, fsync, cancellation) |
| 10. App | AppModel and every view, as an ElmLean native app (`LeanApp/`, survey in `Lean/APP-SURVEY.md`) | **done** except the gaps below: every screen ported. `Backend.real` (`Real/Full.lean`) joins two halves through `Hooks`: the core (`Real/{Base,Stack,Wallet,Send,Peers,Shell,Assemble}.lean`: wallet, storage, network stack, 45 s sync loop, receive, send, fee bump, census, backup) and the records (`Real/Records*.lean`: VaultStore, PeopleStore, ReceiveAddressLabelStore as sealed files keyed from the Keychain; people, pastes, sender lookup, vaults, shared savings, the vault send path, approvals, MuSig2). `records-test` 192/192; lockstep `f_records` OK seeds 1–3 (sealing, store files under every wrap, people mutation scripts byte-exact, derived data, pastes, labels, explorer answers). `backend-test` 84/84 against a fresh regtest bitcoind (create, backup-pending, sync, receive, send, RBF bump, a 2-of-2 shared savings funded from the wallet and credited by the sync loop, the vault payment marked as owned, a vault spend previewed and prepared only as reviewed, export/import carrying the vault and its coins, stop leaves no loop, reopen, delete). Pure helpers (`Pure.lean`): lockstep `f_pure` OK seeds 1–4 (5,559 requests per seed: sync text, history rows, explorer URLs with Foundation's URL rules, peers, labels, fee warning, rate parsing with Swift's `Double(String)` grammar, the bump suggestion from the unrounded rate, thresholds, approvals, MuSig2 labels); it found and fixed six port bugs. Renderer parity (2026-10-27, framework changes with `make check` green): the steppers show "2 of 3" in one row as SwiftUI's `LabeledContent` does, both home screens pull to refresh (`syncNow`), the backup is staged as `winnow-export-<UUID>/winnow-<network>-<id>.json` (excluded from backup, `FileProtectionType.complete`, removed on reset/close/background and swept at boot) and shared as a file, fee-rate fields use the decimal pad. Gaps: the records keep store keys as `.masterKey <hex>` Keychain items where Swift keeps raw bytes (files are shared, Keychain items are not); on a phone upgraded from the Swift app, the people, signers and multisig stores it sealed are set aside, the file as `<store>.swift-era.json` and the raw key as `store-key.swift-era.<store>.<network>`, and start empty (`StoreSeal.setAsideSwiftEra`; the user's choice on 2026-10-28, after 0.9.0 (1) locked them: "Winnow could not safely read its signers"; multisig-app-test `testSwiftEraStoresAreSetAsideAndStartEmpty`, `testAnInterruptedSetAsideFinishes`, `testATamperedFileUnderThisAppsKeyIsStillDamage`); Test mode (E2EMode.swift → `WinnowApp/E2E.lean`, 2026-10-27): Debug builds only (the shell's `build` capability), `WINNOW_E2E=1` with pinned entropy (fails closed without), run-scoped storage and Keychain service with reset, manual peer, custom signet, peer count, sync interval, census URL/keys, forced network (picker locked), first tab, advanced mode, clipboard and control file, device authentication skipped unless asked, and the event journal with Swift's secret filters; lockstep `f_e2e` OK seeds 1–5. In it the simulator app created a wallet from pinned entropy (words checked against BIP39), received 1,000,000 sats from a regtest node and sent 300,000 back (fee 710 as reviewed; the node's mempool held exactly that transaction; confirmed at block 104, balance 699,290). The journal records every event AppModel journals, at the same points with the same field names and formats (backend-test checks 24 of them; 84/84). A second run journaled the create, sync and receive with Swift's field sets, and the app's own send: the journal's `raw` decoded to the txid in the node's mempool, and the file never contained the entropy or the words. Store MACs compare in constant time as CryptoKit's do; the records files get `completeUntilFirstUserAuthentication`, Swift's explicit write option, as iOS's default class (the app has no data-protection entitlement). |
| 11. Integration | the app on the iOS Simulator against a Bitcoin node | regtest **done**: the simulator app imports a watch-only backup and verifies it over Lean TCP, syncs headers and filters, shows an unconfirmed payment within seconds (mempool window), picks up the confirming block in the 45 s loop, and reopens from disk (`backend-test --fixture <dir>` starts the node). Independence (2026-10-27): a copy of `Lean/`, `LeanApp/` and `docs/` with no `.swift` file and no `Sources/` builds from a clean Lean build to the iOS app; with the Objective-C shell (2026-10-27) it compiles no Swift at all (0 `SwiftCompile`, and `otool -L` of the app binary lists no Swift library): the shell's six files are printed into `ios/build/native-shell` by `lake exe elmshell`. In test mode in the simulator the app built from that output created a wallet (Keychain), showed the backup sheet with live sync progress, took a typed label through the Receive sheet (the caret survives each round trip to Lean) and showed the address and its QR code, turned on Advanced mode through an alert, and showed the tab bar, Settings, the Send tab and a bundled design paper; the native demo exercised the remaining node kinds (picker, stepper, disclosure, sheet dismissal, share sheet). The generated files are byte-identical to the hand-written Objective-C prototype they were transcribed from, except for the render dispatch (one branch per grammar row) and the header's capability table. Text is not selectable as it was with SwiftUI; the app has Copy buttons. `Sources/` remains only as the lockstep oracle. Outside test mode, sending in the simulator stops at device authentication: even a freshly created iOS 26.4 simulator shows the system passcode prompt at the app's `auth` step, and no passcode is entered for it. `NormalModeSendUITests.swift` (archived with the oracle harness in `~/src/winnow-lean-swift-archive`; restore a seed-bearing fixture backup, then send; inputs via TEST_RUNNER_WINNOW_UI_*) reaches that prompt and runs where authentication can pass. Accepted 2026-10-27: sending is verified by test mode in the simulator (the node's mempool held exactly the reviewed transaction) and by `backend-test`, since no simulator passcode is available; in test mode (below), which skips it as Swift's does, create, receive and send all ran in the simulator app. Signet **done** (2026-10-27): from a clean install the simulator app finds real signet peers itself (seeds/DoH through the shell's `http.get`), imports a watch-only backup, syncs headers from the built-in checkpoint (258,000) to the tip (328,174) and verifies the backup by filter-scanning 327,674–328,174, in about 90 s. Records on signet (2026-10-27): a co-owner added from a pasted card, a 2-of-2 shared savings created and shown, its sealed `vaults.json` / `people.json` reopened after a restart. Simulator builds are ad-hoc signed: unsigned, the app has no Keychain entitlement and every Keychain write fails (-34018). |

## How to port a module (the pattern every area follows)

Layout during the port (the Swift parts are now in the archive, see Scope):

| What | Where |
|---|---|
| Lean code of area `A` (`Keys`, `Tx`, `Net`, `Wallet`) | `Lean/Winnow/A/*.lean`, each imported by the aggregator `Lean/Winnow/A.lean` |
| Lean oracle ops of area `A` | `Lean/Oracle/A.lean` (list `aOps`), executable `oracle-a` (`Lean/OracleA.lean`) |
| Swift oracle of area `A` (Winnow's original WalletCore) | `Tools/LeanOracle/A/main.swift` (`ops["name"] = { r in … }`), product `oracle-a` |
| Request generators | `Tools/LeanOracle/gen/<n>_<module>.py` with `AREA = "a"` and `cases(rng, n)` |
| Shared helpers | Lean: `Lean/Oracle/Base.lean`; Swift: `Tools/LeanOracle/Common/Oracle.swift`; Python: `gen/_util.py` |

Commands:

```
cd Lean && lake build Winnow.A oracle-a                                  # Lean side
swift build -c release -Xswiftc -enable-testing --product oracle-a       # Swift side (from the root)
python3 Tools/LeanOracle/lockstep.py 300 1 <generator file stem>         # compare
```

Rules:

* **Same behaviour, same errors.** The Lean function returns what the Swift one returns, and fails
  where it throws, with the same error case name (`{"error":"<caseName>"}`; the Swift side prints
  `kind(error)`, the enum case without its payload). Mirror the Swift types as Lean structures and
  inductives with the same field and case names.
* **Requests are data**: bytes as hex strings, 64-bit integers as decimal strings, small ints as JSON
  numbers. Replies must serialize identically on both sides (`{"ok":…}`).
* **Generators** cover random inputs, edge cases (lengths, boundaries, malformed encodings) and the
  published vectors Winnow's tests use (`Tests/**/Vectors`, BIP vectors). A module is done when its
  generator passes for several seeds with both successes and refusals exercised.
* **Lean style**: ordinary Lean 4 (v4.35, no Mathlib); `ByteArray` for bytes, `Except` for failures,
  `Winnow.Reader` for parsing. Reuse `Secp` (proven secp256k1: field, curve, BIP340, tweaks) instead of
  re-implementing curve arithmetic. Proofs are welcome but not required for a port.
* **Scope** (during the port): an area touched only its own files above, never `Package.swift` or `Sources/`.
