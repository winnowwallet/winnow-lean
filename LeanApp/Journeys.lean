import LeanNative.Journey
import LeanNative.Journey.Wire
import WinnowApp.Main
import Journeys.Screens

/-! # The UI journeys

Twelve journeys of the app in the simulator (or headless, against the app itself) against the regtest node
`backend-test --fixture` left running (scripts/ui-fixture). Each is a list of named steps of what a person
does on each screen (`Journeys/Screens.lean`) and what the node must then show (`Journeys/Host.lean`): a
step that cannot be done fails with its name, the driver's reason and what was on screen. Each journey
launches the app in test mode with a fresh random seed, so a reused node never shows an earlier run's coins.
scripts/journeys runs them in the simulator and `scripts/journeys --wire` headless; CI runs both. The
screenshots' names are the website's (ci.yml's journey-media). -/

namespace WinnowJourneys
open Lean LeanNative LeanNative.Journey WinnowApp.Ids

/-- Create a wallet, receive from the node, send to it and see the payment confirm. -/
def createReceiveSendConfirm : Journey := ⟨"createReceiveSendConfirm", do
  let r ← Run.new "journey"
  let h := r.host
  let destination ← h.bankAddress
  r.clipboard destination
  r.launch "journey"

  let address ← step "create the wallet and show a receive address" do
    createWallet
    let address ← Receive.address
    shot "03-receive"
    Receive.close
    pure address

  step "the node pays the wallet, which finds the payment" do
    let fundingTx ← h.fund address funding
    waitForBalance funding
    waitFor (historyPayment fundingTx) 20
    waitSynced
    shot "04-home-funded"

  let (txid, fee) ← step "pay the node back from the review" do
    tap openSendButton
    Send.fill r destination payment
    let fee ← Send.expectReview destination payment
    shot "05-send-review"
    let txid ← Send.send h
    h.expectPays txid destination payment
    pure (txid, fee)

  step "the payment confirms on both sides" do
    h.mine 1
    waitFor broadcastConfirmed 90
    expect (← h.confirmed txid) "the node's wallet has not confirmed the payment"
    shot "06-send-confirmed"
    tap closeSendButton
    waitUntil 60 "the balance after the payment" (every := 1) do
      return (← balance) == some (funding - payment - fee)
    waitFor (historyPayment txid) 20
    shot "07-home-after-send"⟩

/-- A 2-of-3 Taproot multisig account between the phone and two Bitcoin Core wallets, with a recovery path
letting any one of them spend a coin after a day, built in the app's own builder from members: its first
address must be Core's; the payment starts from Send with the account as its source, "Sign and continue" signs
it here, each Core wallet signs its copy with its own libsecp256k1, the phone combines both (three signatures
where two are needed), finalizes and broadcasts, and Core must accept a witness carrying exactly two; the
Transactions list shows the spend once, named with the account. Then, past the delay, the phone alone spends
the change on the recovery path (Send from this account, "Spend with" the recovery path), and Core accepts the
CSV-locked witness. -/
def multisigTwoOfThreeWithRecovery : Journey := ⟨"multisigTwoOfThreeWithRecovery", do
  let r ← Run.new "multisig"
  let h := r.host
  let run ← randomHex 4
  let core ← h.coreSigner s!"ui-core-{run}"
  let second ← h.coreSigner s!"ui-core-second-{run}"
  r.launch "multisig"
  createWallet

  let descriptor ← step "build a 2-of-3 of this phone and two Core keys, any 1 after a day" do
    openMultisigAccounts
    Builder.start
    Builder.name "Phone and two Cores"
    for signer in [core, second] do Builder.addPastedMember r signer.keyExpression
    waitFor (.beginning "Members · 3") 10
    here (.beginning "Any 2 of 3 members spend")
    waitFor (.beginning "2 of 3: any 2 of the 3 keys sign a spend.") 10
    let proposed ← Builder.turnOnRecovery
    expect (proposed.startsWith "After about 181 days (26,000 blocks)") s!"the default delay: {proposed}"
    Builder.setRecoveryDays 1
    shot "10-multisig-build"
    Builder.create
  let account := accountID descriptor
  h.importAccount core descriptor
  h.importAccount second descriptor

  let fundingTx ← step "the account's first address is Core's, and the node funds it" do
    Builder.openAccount
    let first ← h.deriveAddress descriptor 0
    expectEq "the account's first address (Core's)" (← Account.receiveAddress) first
    let fundingTx ← h.fund first funding
    waitForBalance funding multisigBalance
    shot "11-multisig-funded"
    pure fundingTx

  let destination ← h.bankAddress
  let (phoneSigned, fee) ← step "Send from the account: this phone signs, one signature is not enough" do
    Send.fromAccount r account destination payment "needs 2 of 3"
    Collect.countIs multisigSignatureCount "1 of 2"
    let fee := (← amount multisigFee).getD 0
    expect (fee > 0) "the collection step shows no fee"
    scrolled multisigBroadcastButton
    expect (!(← state multisigBroadcastButton).enabled) "one signer alone can send"
    let psbt ← Collect.psbt
    shot "12-multisig-one-signature"
    pure (psbt, fee)

  step "each Core wallet signs its own copy; the phone combines both" do
    for (signer, expected) in [(core, "2 of 2"), (second, "3 of 2")] do
      Collect.add r (← h.sign signer phoneSigned)
      Collect.countIs multisigSignatureCount expected 30

  let (txid, spentAt) ← step "the phone broadcasts; Core accepts a witness with exactly two signatures" do
    let txid ← Collect.broadcast h
    let input ← h.spendingInput txid
    expectEq "what the spend spends (the funding)" input.txid fundingTx
    expectEq "witness items (three key slots, the leaf script and the control block)" input.witness.length 5
    expectEq "the witness's signatures (exactly two of 64 bytes)" (witnessSizes input.witness 3) [0, 128, 128]
    expectEq "the control block's hex length" (input.witness.getLast!.length) 130
    h.expectPays txid destination payment
    shot "13-multisig-sent"
    h.mine 1
    let spentAt ← h.height
    waitFor broadcastConfirmed 90
    pure (txid, spentAt)

  step "one Activity row for the spend, named with the account" do
    backToWalletList
    waitFor (historyPayment txid) 30
    scrolled (historyPayment txid)
    here (paymentAccount txid)
    shot "13b-multisig-transactions"
    openAccountRow account
    waitForBalance (funding - payment - fee) multisigBalance

  step "past the delay, with the Core signers gone, the app syncs to the new tip in one go" do
    -- the app is in the background while the node mines
    h.unload [core, second]
    let height ← h.height
    if height < spentAt + recoveryBlocks - 1 then
      home
      h.mineElsewhere (spentAt + recoveryBlocks - 1 - height)
      activate

  step "the account page: no payment form of its own, Send from this account, Paste a PSBT, Share" do
    scrolled multisigPastePSBTButton
    expect (!(← exists? amountField)) "the account page still has a payment form"
    shot "13a-account-page"
    scrolled multisigShareButton
    shot "13a-account-page-share"

  let recoveryDestination ← h.bankAddress
  step "Send from this account on the recovery path, reviewed once the coin unlocks" do
    tap multisigSendButton
    waitFor sendSourceNote 10
    tap multisigPathPicker
    waitFor (.button "Recovery path") 10
    tap (.button "Recovery path")
    waitFor sendRecoveryNote 10
    shot "13c-send-recovery-path"
    r.paste recoveryDestination pasteDestinationButton
    type amountField (toString recoveryPayment)
    -- the phone may not have seen the last blocks yet: review until the coin unlocks
    waitUntil 120 "the recovery spend was not reviewed" (every := 1) do
      if ← exists? sendButton then return true
      let review ← state reviewButton
      if review.present && review.enabled && (← scrollTo reviewButton) then tap reviewButton
      exists? sendButton 0.5
    expectEq "the reviewed spend path" (← text reviewSpendPath) "Recovery path"
    scrolled sendButton
    expectEq "the review's button" (← text sendButton) "Sign and continue"
    tap sendButton
    -- Sign and continue signed every leaf this phone is on: the recovery leaf's one signature is in
    waitFor multisigRecoverySignatureCount 90
    Collect.countIs multisigRecoverySignatureCount "1 of 1" 30

  step "the phone alone broadcasts the CSV-locked recovery spend, and Core mines it" do
    let recovered ← Collect.broadcast h
    let input ← h.spendingInput recovered
    expectEq "what the recovery spend spends (the change)" input.txid txid
    expectEq "the recovery input's sequence" input.sequence recoveryBlocks
    expectEq "witness items (one signature, two empty slots, the leaf and its control block)" input.witness.length 5
    expectEq "the witness's signatures" (witnessSizes input.witness 3) [0, 0, 128]
    expectEq "the control block's hex length" (input.witness.getLast!.length) 130
    shot "14-multisig-recovered"
    h.mine 1
    expect ((← h.tipTransactions).contains recovered) "the recovery spend was not mined"⟩

/-- A 2-of-2 between the phone and a Ledger, with test mode's simulated Ledger (`WINNOW_E2E_LEDGER`, the Lean
device behind the app's real APDU program): pair it under Settings → Security → Hardware wallets and keys
(its key filed, nothing registered), build the account with it as a member (the Ledger registers it), have it derive the receive
address, which must also be Core's, fund the account from the wallet (one Transactions row, a transfer), pay
from it in Send (Sign and continue, then the Ledger in the collection step), and Core must accept a
witness carrying both signatures; the receipt sees it confirm and Activity shows it once, named with the
account. The nearby card the simulated Ledger brings is answered Not now: this journey pairs by hand. -/
def ledgerPairVerifySpend : Journey := ⟨"ledgerPairVerifySpend", do
  let r ← Run.new "ledger"
  let h := r.host
  r.launch "ledger" [("WINNOW_E2E_LEDGER", ← randomHex 16)]
  createWallet (bluetooth := true)
  step "Bluetooth, then Not now on the Ledger nearby" Ledger.notNow

  step "the node funds the wallet" do
    let walletAddress ← Receive.address
    Receive.close
    discard <| h.fund walletAddress (2 * funding)
    waitForBalance (2 * funding)

  step "Settings → Security → Hardware wallets and keys → Pair a Ledger" do
    Ledger.pair "Nano X"
    shot "19-signers-paired"

  let descriptor ← step "build a 2-of-2 of this phone and the Ledger, which registers it" do
    backToWalletList
    openMultisigAccounts
    Builder.start
    Builder.name "Ledger savings"
    Builder.addLedgerMember "Nano X"
    waitFor (.beginning "Members · 2") 10
    tap multisigBuildCreateButton
    waitFor multisigBuildLedgerRegistered 60
    scrolled multisigCreatedDescriptor
    text multisigCreatedDescriptor
  let account := accountID descriptor

  let address ← step "the Ledger derives the address the phone shows, and so does Core" do
    Builder.openAccount
    waitFor multisigPolicy 20
    expectEq "the account's policy" (← text multisigPolicy) "2 of 2"
    let address ← Account.receiveAddress
    let verified ← Ledger.verifyAddress
    expect (verified.startsWith "The Ledger derived this same address.") verified
    -- the page shares its descriptor rather than printing it; the builder showed the same one
    scrolled multisigShareButton
    expectEq "the account's first address (Core's)" (← h.deriveAddress descriptor 0) address
    shot "20-ledger-verified"
    pure address

  let fundingTx ← step "the wallet pays the account: one Activity row, a transfer" do
    backToWalletList
    tap openSendButton
    tap sendFromWallet
    Send.fill r address funding
    let fundingTx ← Send.send h
    h.mine 1
    waitFor broadcastConfirmed 90
    backToWalletList
    waitFor (historyPayment fundingTx) 30
    scrolled (historyPayment fundingTx)
    waitUntil 30 "the transfer's row (one row)" do
      return (← text (historyPayment fundingTx)) == "Moved to Ledger savings"
    shot "20b-ledger-transfer-row"
    openAccountRow account
    waitForBalance funding multisigBalance
    pure fundingTx

  let destination ← h.bankAddress
  step "Send from the account: this phone signs, then the Ledger" do
    Send.fromAccount r account destination payment "needs 2 of 2"
    Collect.countIs multisigSignatureCount "1 of 2"
    tap ledgerSignButton
    Collect.countIs multisigSignatureCount "2 of 2"
    shot "21-ledger-signed"

  let txid ← step "Core accepts a witness carrying both signatures" do
    let txid ← Collect.broadcast h
    let input ← h.spendingInput txid
    expectEq "what the spend spends (the transfer)" input.txid fundingTx
    expectEq "witness items (two signatures, the leaf script and the control block)" input.witness.length 4
    expectEq "the phone's and the Ledger's signatures" (witnessSizes input.witness 2) [128, 128]
    h.mine 1
    waitFor broadcastConfirmed 90
    expect ((← h.tipTransactions).contains txid) "the payment was not mined"
    shot "22-ledger-confirmed"
    pure txid

  step "one confirmed Activity row, named with the account" do
    backToWalletList
    waitFor (historyPayment txid) 60
    scrolled (historyPayment txid)
    here (paymentAccount txid)
    shot "23-ledger-transactions"⟩

/-- From the Ledger nearby card to a verified 2-of-2 (#97): onboarding ends with the Bluetooth card, and test
mode's simulated Ledger (`WINNOW_E2E_LEDGER`) advertising brings the card over the home. Set up pairs it,
creates the 2-of-2 of this phone and the Ledger, registers it on the Ledger and has the Ledger show the
account's first receive address, which the phone shows to compare; They match opens the account, whose receive
address it is: the node pays it and the account sees the coin. With a Ledger paired, no card comes again. -/
def ledgerCardTwoOfTwo : Journey := ⟨"ledgerCardTwoOfTwo", do
  let r ← Run.new "ledgercard"
  let h := r.host
  r.launch "ledgercard" [("WINNOW_E2E_LEDGER", ← randomHex 16)]
  createWallet (bluetooth := true)

  step "onboarding's Bluetooth card, then the Ledger in range: the card over the home" do
    shot "24-bluetooth-card"
    tap allowBluetoothButton
    waitFor ledgerNearbyCard 30
    here (.text "^Ledger Nano X nearby\\.$")
    here ledgerNotNowButton
    shot "25-ledger-nearby"

  let address ← step "Set up: paired, created, registered, and the first address on both screens" do
    tap ledgerSetUpButton
    waitFor ledgerSetupStartButton 10
    tap ledgerSetupStartButton
    waitFor ledgerSetupDone 90
    let address ← text ledgerSetupAddress
    expect (address.startsWith "bcrt1p") s!"not a regtest Taproot address: {address}"
    shot "26-ledger-compare"
    pure address

  step "They match: the account, 2 of 2, whose first address that is" do
    tap ledgerAddressesMatchButton
    waitFor multisigPolicy 20
    expectEq "the account's policy" (← text multisigPolicy) "2 of 2"
    expectEq "the account's receive address" (← Account.receiveAddress) address
    discard <| h.fund address funding
    waitForBalance funding multisigBalance
    shot "27-ledger-account"

  step "a Ledger paired: the home shows no card again" do
    backToWalletList
    pause 3
    expect (!(← exists? ledgerNearbyCard)) "the nearby card came back with a Ledger paired"⟩

/-- The census list the build ships (the app's manifest bundles build/census/peers.json): Settings → Network →
Peers and routing on mainnet shows its date and count, not the sentence for a build without one; About shows
the version on the build's own bundle (in a simulator; headless there is no bundle, and it says Unknown); then
the plain texts (PORT.md, deliberate departures): Settings' Backup section, the backup file sheet, the iCloud sheet,
Settings → Security → Multisig accounts and Join. -/
def shippedCensus : Journey := ⟨"shippedCensus", do
  let r ← Run.new "census"
  r.launch "census" [("WINNOW_E2E_NETWORK", "mainnet")]
  createWallet

  step "Peers and routing on mainnet show the shipped census list's date and count" do
    openSettings
    scrolled networkPeersButton
    tap networkPeersButton
    waitFor censusCatalogText 20
    scrolled censusCatalogText
    let line ← text censusCatalogText
    here (.text "^Observed \\d{4}-\\d{2}-\\d{2}: \\d+ candidates\\.$")
    let count := ((line.splitOn ": ")[1]?).bind digits
    expect (count.getD 0 > 100) s!"census line: {line}"
    shot "30-settings-census"
    tap .back

  step "About shows the version on this build's bundle" do
    scrolled appVersion
    let shown ← text appVersion
    -- headless, the app is the journeys' own executable, with no Info.plist beside it: nothing to read
    if (← IO.getEnv "LEANNATIVE_DRIVER") == some "wire" then expectEq "the version, with no bundle" shown "Unknown"
    else expect (shown != "Unknown" && (digits shown).isSome && shown.endsWith ")") s!"the version in a bundle: {shown}"

  step "the Backup section, the backup file sheet and the iCloud sheet" do
    waitFor exportBundleButton 10
    scrolled exportBundleButton
    expectEq "the backup file button" (← text exportBundleButton) "Save a backup file"
    here cloudBackupRowStatus
    shot "31-settings-backup"
    tap exportBundleButton
    waitFor exportExplanation 10
    here (.nav "Backup file")
    shot "32-backup-file-sheet"
    tap (.button "Close")
    waitFor exportBundleButton 10
    scrolled (.button "iCloud backup")
    tap (.button "iCloud backup")
    waitFor automaticCloudBackupToggle 10
    shot "33-icloud-sheet"
    tap (.button "Close")

  step "Settings → Security → Multisig accounts, and Join" do
    scrolled multisigAccountsButton
    tap multisigAccountsButton
    waitFor multisigAddButton 10
    scrolled multisigAddButton
    expectEq "the Join button" (← text multisigAddButton) "Join an account"
    expectEq "the Create button" (← text multisigBuildButton) "Create an account"
    shot "34-wallet-multisig"
    tap multisigAddButton
    waitFor (.nav "Join an account") 10
    shot "35-join"⟩

/-- Pays a BIP352 silent payment code. Core has no BIP352, so the receiver is backend-test's, written from the
BIP's receiving side: the transaction the node accepts must pay the one output that receiver finds, the review
must say the address is derived, and the receipt must show that output's address. -/
def silentPaymentSend : Journey := ⟨"silentPaymentSend", do
  let r ← Run.new "silent"
  let h := r.host
  let code ← h.silentPaymentCode
  expect (code.startsWith "tsp1") s!"not a test-network code: {code}"
  r.launch "silent"
  createWallet

  step "the node funds the wallet" do
    let address ← Receive.address
    Receive.close
    discard <| h.fund address funding
    waitForBalance funding

  let txid ← step "pay the code: the review says the address is derived" do
    tap openSendButton
    Send.fill r code silentPayment
    expectEq "the reviewed destination" (← text reviewDestination) code
    here silentPaymentNote
    expectEq "the reviewed amount" (← amount reviewAmount) (some silentPayment)
    shot "40-silent-review"
    Send.send h

  step "the transaction pays the one output the code's holder finds, and the receipt shows its address" do
    let expected ← h.silentPaymentExpectedScript txid
    let some paid := (outputs (← h.transaction txid)).find? (fun o => o.script == expected && o.sats == silentPayment)
      | failure s!"the transaction pays no output the code's holder would find ({expected})"
    waitFor derivedOutputAddress 20
    scrolled derivedOutputAddress
    expectEq "the receipt's derived address" (← text derivedOutputAddress) paid.address
    h.mine 1
    waitFor broadcastConfirmed 90
    shot "41-silent-confirmed"⟩

/-- A payment sent at a low rate, then replaced with a higher fee from its payment screen (Bump fee). Before it,
Send's folded Fee against the node: the Network floor is the node's BIP133 feefilter, and an override under it
resolves to the floor. Core checks the replacement: it spends exactly the original's coins, pays the same amount
to the same address with a higher fee, takes the original's place in the mempool, and is the one that confirms.
Activity then shows the replacement confirmed and the original replaced, and their payment screens the block,
each one's fee and what replaced the original. -/
def feeBumpReplaceConfirm : Journey := ⟨"feeBumpReplaceConfirm", do
  let r ← Run.new "feebump"
  let h := r.host
  -- headless, this run's wallet secret is behind the person's presence, as the app's is outside test mode, and
  -- its device check is on: creating, sending and bumping each read the secret under the authentication they ask
  -- for, and the fake shell refuses a read without one as a device does. Not in a simulator: there the device
  -- check is a system sheet that no driver answers, and the Keychain does not enforce an access control anyway
  let headless := (← IO.getEnv "LEANNATIVE_DRIVER") == some "wire"
  r.launch "feebump" (if headless then [("WINNOW_E2E_DEVICE_AUTH", "1"), ("WINNOW_E2E_KEYCHAIN_PROTECTION", "1")] else [])
  createWallet

  step "the node funds the wallet" do
    let address ← Receive.address
    Receive.close
    discard <| h.fund address funding
    waitForBalance funding

  let destination ← h.bankAddress
  let low ← step "Send's fee: the node's relay floor, and an override under it resolved to the floor" do
    tap openSendButton
    r.paste destination pasteDestinationButton
    type amountField (toString payment)
    let floor ← Send.floorMilli
    let shown ← text feeFloorText
    expectEq "an override under the floor, resolved" (← Send.override (Send.rateText (floor / 2))) shown
    -- a whole rate at or above the floor: the lowest Winnow would send at that the node relays
    let low := max 1 ((floor + 999) / 1000)
    expectEq "the low override, resolved" (← Send.override (toString low)) s!"{low} sat/vB"
    pure low

  let (txid, fee, coins) ← step "send at the low rate; the node has it at that fee" do
    scrolled reviewButton
    tap reviewButton
    waitFor sendButton 30
    let fee ← Send.expectReview destination payment
    let txid ← Send.send h
    h.expectPays txid destination payment
    expectEq "the fee the node computes" (← h.mempoolFee txid) fee
    let coins := spends (← h.transaction txid)
    expect (!coins.isEmpty) "the payment spends nothing"
    waitFor broadcastPending 30
    pure (txid, fee, coins)

  let (replacement, newFee) ← step "open the unconfirmed payment and replace it at a higher rate" do
    backToWalletList
    waitFor (historyPayment txid) 30
    scrolled (historyPayment txid)
    expectEq "the payment's row" (← text (historyStatus txid)) "Pending"
    tap (historyPayment txid)
    Bump.start
    let newFee ← Bump.review (toString (low + 4))
    expect (newFee > fee) s!"the replacement's fee {newFee} is not above the original's {fee}"
    shot "50-fee-bump-review"
    let replacement ← Bump.replace h
    pure (replacement, newFee)

  step "Core: the same coins, the same payment, a higher fee, and the original gone from the mempool" do
    expectEq "the coins the replacement spends" (spends (← h.transaction replacement)) coins
    h.expectPays replacement destination payment
    expectEq "the replacement's fee, as the node computes it" (← h.mempoolFee replacement) newFee
    expect (!(← h.mempool).contains txid) "the original is still in the node's mempool"

  step "the replacement confirms, not the original; Activity and the payment screens say so, with each fee" do
    tap (.button "Done")
    h.mine 1
    let tip ← h.tipTransactions
    expect (tip.contains replacement) "the block does not have the replacement"
    expect (!tip.contains txid) "the block has the original"
    let height ← h.height
    backToWalletList
    waitForBalance (funding - payment - newFee)
    scrolled (historyPayment replacement)
    waitUntil 60 "the replacement's row is not confirmed" do
      return (← text (historyStatus replacement)) == "Confirmed"
    expectEq "the original's row" (← text (historyStatus txid)) "Replaced"
    shot "51-fee-bump-confirmed"
    tap (historyPayment replacement)
    scrolled paymentBlock
    expectEq "the replacement's block" (← text paymentBlock) s!"{height}"
    expectEq "the replacement's fee" (← amount paymentFee) (some newFee)
    backToWalletList
    scrolled (historyPayment txid)
    tap (historyPayment txid)
    scrolled paymentReplacedBy
    expectEq "what replaced the original" (← text paymentReplacedBy) s!"{String.ofList (replacement.toList.take 8)}…"
    expectEq "the original's fee" (← amount paymentFee) (some fee)⟩

/-- The same recovery phrase on another device spends the phone's coins, twice. A review whose coin has gone
fails when the owner signs, on the Send screen, which can then be used again. A payment whose coin the node has
already seen spent goes out and the node refuses it, which it never tells a peer: the phone finds out from the
block that confirms the other spend. When that spend took only one of the payment's two coins, the other comes
back and can be spent. -/
def spentElsewhere : Journey := ⟨"spentElsewhere", do
  let r ← Run.new "elsewhere"
  let h := r.host
  let entropy ← randomHex 16
  let other := s!"elsewhere-{← randomHex 4}"
  let some seed := Winnow.Wire.dataOfHex? entropy | failure "the entropy is not hex"
  h.samePhrase other seed
  r.launch "elsewhere" [("WINNOW_E2E_ENTROPY", entropy)]
  createWallet

  let address ← step "the node funds the wallet" do
    let address ← Receive.address
    Receive.close
    discard <| h.fund address funding
    waitForBalance funding
    pure address

  let destination ← h.bankAddress
  step "the reviewed coin is spent elsewhere and confirmed: signing fails on the Send screen" do
    tap openSendButton
    r.paste destination pasteDestinationButton
    type amountField (toString payment)
    scrolled reviewButton
    tap reviewButton
    waitFor sendButton 30
    discard <| Send.expectReview destination payment
    -- a low rate: the phone's next fee comes from this block
    discard <| h.sweep other destination 2
    h.mine 1
    discard <| h.fund address (2 * funding)
    Send.waitForReviewBalance (2 * funding)
    scrolled sendButton
    tap sendButton
    waitFor (.text "^The available coins, fee, or change changed") 30

  let refused ← step "the coin is spent elsewhere again, unconfirmed: the node takes the payment and refuses it" do
    scrolled (.button "Edit payment")
    tap (.button "Edit payment")
    scrolled reviewButton
    tap reviewButton
    waitFor sendButton 30
    discard <| Send.expectReview destination payment
    -- well over the rate the phone reviewed: a lower one its payment would replace
    let winner ← h.sweep other destination 100
    scrolled sendButton
    tap sendButton
    waitFor broadcastPending 30
    scrolled (.text "^Transaction details")
    tap (.text "^Transaction details")
    let txid ← Send.relayedTxid
    let mempool ← h.mempool
    expect (!mempool.contains txid) "the node took the payment"
    expect (mempool.contains winner) "the node dropped the other spend"
    pure (txid, winner)

  step "the other spend confirms: the refused payment is marked replaced and the coins are gone" do
    let (txid, winner) := refused
    h.mine 1
    let tip ← h.tipTransactions
    expect (tip.contains winner) "the block does not have the other spend"
    expect (!tip.contains txid) "the block has the refused payment"
    waitFor broadcastReplaced 60
    expect (!(← exists? broadcastPending)) "Send still waits for a confirmation that cannot come"
    backToWalletList
    waitForBalance 0
    scrolled (historyPayment txid)
    waitUntil 60 "the payment's row is not marked replaced" do
      return (← text (historyStatus txid)) == "Replaced"
    tap (historyPayment txid)
    scrolled paymentReplacedBy
    expectEq "what replaced it" (← text paymentReplacedBy) s!"{String.ofList (winner.toList.take 8)}…"
    pause 1
    expect (!(← exists? bumpFeeButton)) "the payment still offers a fee bump"

  let (twoCoins, other3) ← step "a payment of two coins, one of them spent elsewhere: the node refuses it" do
    backToWalletList
    discard <| h.fund address smallCoin
    discard <| h.fund address smallCoin
    waitForBalance (2 * smallCoin)
    tap openSendButton
    r.paste destination pasteDestinationButton
    type amountField (toString (smallCoin + payment))
    scrolled reviewButton
    tap reviewButton
    waitFor sendButton 30
    discard <| Send.expectReview destination (smallCoin + payment)
    let winner ← h.sweepOneCoin other destination 1000
    scrolled sendButton
    tap sendButton
    waitFor broadcastPending 30
    scrolled (.text "^Transaction details")
    tap (.text "^Transaction details")
    let txid ← Send.relayedTxid
    expect (!(← h.mempool).contains txid) "the node took the payment"
    pure (txid, winner)

  step "the other spend confirms: the coin it left comes back, and the phone can spend it" do
    h.mine 1
    expect ((← h.tipTransactions).contains other3) "the block does not have the other spend"
    waitFor broadcastReplaced 60
    backToWalletList
    waitForBalance smallCoin
    scrolled (historyPayment twoCoins)
    waitUntil 60 "the payment's row is not marked replaced" do
      return (← text (historyStatus twoCoins)) == "Replaced"
    tap (historyPayment twoCoins)
    scrolled paymentReplacedBy
    expectEq "what replaced it" (← text paymentReplacedBy) s!"{String.ofList (other3.toList.take 8)}…"
    backToWalletList
    tap openSendButton
    r.paste destination pasteDestinationButton
    type amountField (toString payment)
    scrolled reviewButton
    tap reviewButton
    waitFor sendButton 30
    let fee ← Send.expectReview destination payment
    scrolled sendButton
    let txid ← Send.send h
    h.expectPays txid destination payment
    h.mine 1
    backToWalletList
    waitForBalance (smallCoin - payment - fee)
    discard <| h.cli #["unloadwallet", other]⟩

/-- The phone cannot reach the Bitcoin network. The fixture's node goes off the network (`setnetworkactive
false`) while Winnow is in the background; back in the foreground, Home says Offline in one short line, which
explains itself in an alert and leads to Settings → Network → Sync. With the node back, that page's Retry
reconnects at once, well before the pool would try again by itself (30 seconds after it started), and the
wallet finds a payment the node sends it. The node serves every journey
of the run, so it goes back on the network however this one ends. -/
def retryAfterNoPeers : Journey := ⟨"retryAfterNoPeers", do
  let r ← Run.new "retry"
  let h := r.host
  r.launch "retry"
  createWallet
  let address ← step "the wallet syncs with its one peer" do
    let address ← Receive.address
    Receive.close
    waitSynced
    pure address
  try
    let start ← step "the node goes off the network: back in the foreground, Home says Offline" do
      home
      discard <| h.cli #["setnetworkactive", "false"]
      let start ← IO.monoMsNow
      activate
      waitFor homeNetworkWarning 30
      -- the warning may say "Sync problem" first, while a sync is still failing against the peer that went
      -- quiet; it is Offline once the pool has given that peer up
      waitUntil 12 "the home's warning is not Offline" (every := 0.5) do
        return (← text homeNetworkWarning) == "Offline"
      expectGone retryPeersButton
      shot "60-home-offline"
      pure start
    step "the node is back: the warning leads to Retry in Settings, which reconnects at once, and the wallet finds a payment" do
      discard <| h.cli #["setnetworkactive", "true"]
      tap homeNetworkWarning
      waitFor (.alert "Network settings") 10
      here (.text "^Couldn't reach the Bitcoin network")
      tap (.alert "Network settings")
      waitFor retryPeersButton 10
      tap retryPeersButton
      -- the pool's own redial comes 30 s after the foreground started it; Retry must beat it
      let elapsed := (← IO.monoMsNow) - start
      let within := 25 - Float.ofNat elapsed / 1000
      expect (within ≥ 10) s!"Retry came {elapsed} ms after the foreground, too late to tell it from the pool's redial"
      waitUntil within "Retry did not reconnect" do return (← text syncStatus) == "Up to date"
      expectGone retryPeersButton
      -- back through Settings to the home (the Sync page shows the balance too, so not backToWalletList)
      for _ in [0:4] do
        if ← exists? settingsButton then break
        tap .back
        pause 0.5
      waitFor settingsButton 10
      waitUntil 10 "the home is not Up to date" do return (← text syncSummaryText) == "Up to date"
      expectGone homeNetworkWarning
      discard <| h.fund address funding
      waitForBalance funding
  finally
    discard <| h.cli #["setnetworkactive", "true"]⟩

/-- A person's name typed on Receive, and their address and card made. On a phone closing the keyboard already
makes them (the name's return does what the button does; seen on CI's simulator, 2026-11-15), and the button
is then gone; the headless driver only sets the text, and the button is what makes them. -/
def makeCardFor (name : String) : UI Unit := do
  type personCardNameField name
  unless ← exists? personCardText 2 do
    let button ← state makePersonCardButton
    if button.present && button.enabled then
      -- gone between the look and the tap, the card is there: the wait below says
      try tap makePersonCardButton catch _ => pure ()
  waitFor personCardText 30

/-- A card for one person (issue #94). On the card sheet the wallet makes a card for Dana alone; the device's
owner is asked first, since making it reads the wallet's key. The node is Dana: it holds only the card's text,
derives the card's first two addresses from it and pays each. The wallet finds both payments and Activity
names each as received from Dana, though nobody labelled them. The card carries no account key, and shown
again it is the same card. -/
def cardForOnePerson : Journey := ⟨"cardForOnePerson", do
  let r ← Run.new "card"
  let h := r.host
  r.launch "card"
  createWallet

  let card ← step "on Receive, under the wallet's address, Dana's name gives her address and her card" do
    let own ← Receive.address
    makeCardFor "Dana"
    let card ← text personCardText
    expect ((card.splitOn "\"payTo\":\"twinnowcard1p").length == 2 && (card.splitOn "tweak").length == 1)
      s!"not a card with a test-network code and no tweak: {card}"
    expect ((card.splitOn "pub").length == 1) s!"the card carries an extended key: {card}"
    -- with it, an ordinary address for a payer that reads no card: the card's first payment, and not the
    -- wallet's own address above
    waitFor personAddressText 30
    let hers ← text personAddressText
    expectEq "Dana's address" hers (← h.cardAddress card 0)
    expect (hers != own) "Dana's address is the wallet's own"
    shot "50-card-for-dana"
    Receive.close
    -- asked for again, it is the same card
    discard Receive.address
    makeCardFor "Dana"
    expectEq "the card shown again" (← text personCardText) card
    Receive.close
    pure card

  let (first, second) ← step "Dana, who holds only the card, pays its first two addresses" do
    let address0 ← h.cardAddress card 0
    let address1 ← h.cardAddress card 1
    expect (address0.startsWith "bcrt1p" && address1.startsWith "bcrt1p" && address0 != address1)
      s!"the card's addresses: {address0}, {address1}"
    let first ← h.fund address0 funding
    waitForBalance funding
    let second ← h.fund address1 payment
    waitForBalance (funding + payment)
    pure (first, second)

  step "Activity names both payments as Dana's" do
    for txid in [first, second] do
      waitFor (historyPayment txid) 30
      scrolled (historyPayment txid)
      waitUntil 30 "the payment is named as Dana's" (every := 1) do
        return (← text (historyPayment txid)) == "Received from Dana"
    shot "51-card-payments-from-dana"⟩

/-- Whether a backup in the stand-in iCloud was saved after `marker` was written. -/
def savedSince (cloud marker : System.FilePath) : IO Bool := do
  let since := (← marker.metadata).modified
  for entry in ← cloud.readDir do
    if entry.fileName.endsWith ".backup" && decide ((← entry.path.metadata).modified > since) then return true
  return false

/-- An account follows a person from one device to another. Two launches with two seeds are the two devices,
and a directory both are given stands in for their iCloud (`WINNOW_E2E_CLOUD`; test mode has no iCloud
otherwise). The first builds a 2-of-2 with a Core key, is paid, and saves its backup. The second, a different
wallet, is told nothing: it lists the account by itself, with the balance its own scan confirms and the next
address Core derives, and says it only watches, since its wallet holds none of the account's keys. -/
def accountFollowsDevices : Journey := ⟨"accountFollowsDevices", do
  let r ← Run.new "devices"
  let h := r.host
  let run ← randomHex 4
  let core ← h.coreSigner s!"ui-core-devices-{run}"
  let cloud := s!"{h.fixture}/icloud-{run}"
  IO.FS.createDirAll cloud
  r.launch "devicesfirst" [("WINNOW_E2E_CLOUD", cloud)]
  createWallet

  let descriptor ← step "the first device builds a 2-of-2 of this phone and a Core key" do
    openMultisigAccounts
    Builder.start
    Builder.name "Phone and Core"
    Builder.addPastedMember r core.keyExpression
    waitFor (.beginning "Members · 2") 10
    Builder.create
  let account := accountID descriptor
  h.importAccount core descriptor

  step "the node funds it, and the first device's backup is saved with it" do
    Builder.openAccount
    let first ← h.deriveAddress descriptor 0
    expectEq "the account's first address (Core's)" (← Account.receiveAddress) first
    discard <| h.fund first funding
    waitForBalance funding multisigBalance
    let marker := s!"{cloud}/seen"
    IO.FS.writeFile marker ""
    waitUntil 60 "the first device's backup was not saved after the payment" (every := 0.5) do savedSince cloud marker
    shot "40-devices-first"

  step "a second device, another wallet, the same iCloud: the account is there by itself" do
    r.launch "devicessecond" [("WINNOW_E2E_CLOUD", cloud)]
    createWallet
    waitFor (multisigAccount account) 120
    waitFor (multisigWatchOnly account) 10
    expectEq "the account's name" (← text (multisigAccount account)) "Phone and Core"
    shot "41-devices-second-home"

  step "its page says it only watches, with the balance and Core's next address" do
    openAccountRow account
    waitFor multisigWatchOnlyNote 20
    waitForBalance funding multisigBalance
    expectEq "the next address, the one after the paid one (Core's)" (← Account.receiveAddress) (← h.deriveAddress descriptor 1)
    shot "42-devices-watch-only"⟩

/-- Two wallets on one device. Settings → Wallets adds a second beside the first, through the onboarding
there already is. The second builds a 2-of-2 of itself and the first; the node pays it; a payment from it is
signed by the wallet that is open and then, with a button and a device check of its own, by the other wallet
kept on the device; and the node takes a witness with both signatures. No other device takes part. -/
def twoWalletsOneDevice : Journey := ⟨"twoWalletsOneDevice", do
  let r ← Run.new "wallets"
  let h := r.host
  r.launch "wallets"
  createWallet

  let firstKey ← step "the first wallet's key, as it is sent to whoever builds an account" do
    openMultisigAccounts
    tap multisigAddButton
    waitFor multisigKeyText 10
    let key ← text multisigKeyText
    backToWalletList
    pure key

  step "Settings → Wallets → Add a wallet: a second one, made beside the first" do
    openSettings
    scrolled addWalletButton
    shot "60-wallets-one"
    tap addWalletButton
    waitFor cancelAddWalletButton 60
    shot "61-wallets-add"
    tap createWalletButton
    waitFor receiveButton 60
    waitFor balanceText 30
    openSettings
    scrolled addWalletButton
    waitUntil 20 "Settings does not list two wallets" do return (← exists? (.text "^Wallet [0-9a-f]{8}$"))
    shot "62-wallets-two"
    backToWalletList

  let descriptor ← step "the second wallet builds a 2-of-2 of itself and the first" do
    openMultisigAccounts
    Builder.start
    Builder.name "Both wallets"
    Builder.addPastedMember r firstKey
    waitFor (.beginning "Members · 2") 10
    Builder.create
  let account := accountID descriptor

  step "the node pays the account" do
    Builder.openAccount
    discard <| h.fund (← Account.receiveAddress) funding
    waitForBalance funding multisigBalance

  let destination ← h.bankAddress
  step "a payment from it: the open wallet signs, and one signature is not enough" do
    Send.fromAccount r account destination payment "needs 2 of 2"
    Collect.countIs multisigSignatureCount "1 of 2"
    shot "63-wallets-one-signature"

  step "the other wallet kept here signs with a button of its own" do
    scrolled (.beginning "Add wallet ")
    tap (.beginning "Add wallet ")
    Collect.countIs multisigSignatureCount "2 of 2" 60
    shot "64-wallets-two-signatures"

  step "the phone broadcasts, and the node takes it" do
    let txid ← Collect.broadcast h
    h.expectPays txid destination payment⟩

def all : List Journey :=
  [createReceiveSendConfirm, multisigTwoOfThreeWithRecovery, ledgerPairVerifySpend, ledgerCardTwoOfTwo, shippedCensus,
   silentPaymentSend, feeBumpReplaceConfirm, spentElsewhere, retryAfterNoPeers, cardForOnePerson, accountFollowsDevices,
   twoWalletsOneDevice]

end WinnowJourneys

/-- The journeys, and the app itself for the headless driver (`LEANNATIVE_DRIVER=wire`: `scripts/journeys --wire`). -/
def main (args : List String) : IO UInt32 :=
  LeanNative.Journey.main WinnowJourneys.all args (wire := some (LeanNative.Journey.Wire.app WinnowApp.app))
