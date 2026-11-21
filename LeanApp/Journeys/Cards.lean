import LeanNative.Journey
import Winnow.Wallet.Wallet
import WinnowApp.Ids
import Journeys.Screens

/-! # Person-card journeys: receiving, paying, rotating, spending, and restoring a post-backup card -/

namespace WinnowJourneys
open Lean LeanNative LeanNative.Journey WinnowApp.Ids

/-- A card for one person (issue #94), end to end between two wallets. Bob makes Dana's address and card on
Receive (no account key, no tweak; shown again, the same card). Dana tests that Send refuses the bare
`twinnowcard1p…` code and directs her to Saved recipients, saves Bob from the card, and pays him twice at two
distinct derived addresses without any address-reuse warning. Bob reopens his persisted wallet, sees both
payments named `"Received from Dana"`, verifies Dana's ordinary address on Receive rotated past both paid
indices to index 2, and spends both card coins back to Core. -/
def cardForOnePerson : Journey := ⟨"cardForOnePerson", do
  let r ← Run.new "card"
  let h := r.host
  let bobEntropy ← randomHex 16
  let secondPayment := payment / 2
  let totalReceived := payment + secondPayment
  r.launch "cardbob" [("WINNOW_E2E_ENTROPY", bobEntropy)]
  createWallet

  let card ← step "Bob makes Dana's address and card on Receive, and sees the same card again" do
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
    scrolled personAddressText
    shot "70-card-for-dana-address"
    scrolled personCardText
    scrolled ownNameField
    shot "71-card-for-dana-card"
    Receive.close
    expectGone closeReceiveButton 10
    -- asked for again, it is the same card
    discard Receive.address
    makeCardFor "Dana"
    expectEq "the card shown again" (← text personCardText) card
    Receive.close
    expectGone closeReceiveButton 10
    pure card

  let code ← cardCodeOf card
  expect (code.startsWith "twinnowcard1p") s!"not a test-network card code: {code}"
  let address0 ← h.cardAddress card 0
  let address1 ← h.cardAddress card 1
  let address2 ← h.cardAddress card 2
  expect (address0.startsWith "bcrt1p" && address1.startsWith "bcrt1p" && address2.startsWith "bcrt1p" &&
          address0 != address1 && address1 != address2 && address0 != address2)
    s!"the card's derived addresses are not distinct Taproot addresses: {address0}, {address1}, {address2}"

  let (first, second) ← step "Dana is refused on bare card code in Send, saves Bob's card, and pays him twice" do
    r.launch "carddana"
    createWallet
    let danaAddress ← Receive.address
    Receive.close
    discard <| h.fund danaAddress (2 * funding)
    waitForBalance (2 * funding)

    -- pasting the bare twinnowcard1p… code into Send is refused with guidance to Saved recipients
    tap openSendButton
    r.paste code pasteDestinationButton
    type amountField (toString payment)
    scrolled reviewButton
    tap reviewButton
    let refusal := Find.beginning "That is a Winnow card. Add it under Saved recipients"
    waitUntil 20 "Send did not refuse the bare card code" do
      if ← exists? refusal 1 then return true
      scrollTo refusal
    expectEq "bare card code refusal" (← text refusal) Winnow.Wallet.cardCodeInSendText
    expect (!(← exists? sendButton)) "Send reviewed a bare card code"

    -- save Bob from the full card JSON under Saved recipients and pay payment #1
    People.addFromCard r card (name := some "Bob")
    waitFor (.button "Bob") 10
    tap (.button "Bob")
    expectGone addPersonToolbarButton 10
    waitFor (.button "Change") 10
    expectGone refusal 10
    scrolled reviewButton
    tap reviewButton
    waitFor sendButton 30
    discard <| Send.expectReview address0 payment
    here (.text "^Bob$")
    expect (!(← exists? (.beginning "This address has been saved for reuse")))
      "first card review warned of address reuse"
    shot "72-card-payer-review"
    let first ← Send.send h
    h.expectPays first address0 payment
    h.mine 1
    waitFor broadcastConfirmed 90
    tap closeSendButton
    expectGone closeSendButton 10
    waitFor openSendButton 20

    -- pay Bob a second time: derives index 1, distinct from payment #1
    tap openSendButton
    scrolled savedRecipientsButton
    tap savedRecipientsButton
    waitFor (.button "Bob") 10
    tap (.button "Bob")
    expectGone addPersonToolbarButton 10
    waitFor (.button "Change") 10
    type amountField (toString secondPayment)
    scrolled reviewButton
    tap reviewButton
    waitFor sendButton 30
    discard <| Send.expectReview address1 secondPayment
    expect (!(← exists? (.beginning "This address has been saved for reuse")))
      "second card review warned of address reuse"
    let second ← Send.send h
    h.expectPays second address1 secondPayment
    h.mine 1
    waitFor broadcastConfirmed 90
    tap closeSendButton
    pure (first, second)

  step "Bob reopens his wallet, sees both payments from Dana, verifies address rotation, and spends the card coins" do
    r.launch "cardbob" [("WINNOW_E2E_RESET", "0"), ("WINNOW_E2E_ENTROPY", bobEntropy)]
    waitFor receiveButton 60
    waitFor balanceText 30
    waitForBalance totalReceived
    for txid in [first, second] do
      waitFor (historyPayment txid) 30
      scrolled (historyPayment txid)
      waitUntil 30 "the payment is named as Dana's" (every := 1) do
        return (← text (historyPayment txid)) == "Received from Dana"
    shot "73-card-payments-from-dana"

    -- Dana's ordinary address on Receive rotated past paid indices 0 and 1 to index 2
    discard Receive.address
    makeCardFor "Dana"
    waitFor personAddressText 30
    scrolled personAddressText
    expectEq "Dana's rotated address" (← text personAddressText) address2
    shot "74-card-address-rotated"
    Receive.close
    expectGone closeReceiveButton 10
    waitFor openSendButton 20

    -- Bob holds only card coins; sending `payment` (> 1,000,000 with fee) spends both card UTXOs
    let bank ← h.bankAddress
    tap openSendButton
    Send.fill r bank payment
    let fee ← Send.expectReview bank payment
    let spendTx ← Send.send h
    let spent := spends (← h.transaction spendTx)
    expect (spent.any (·.startsWith s!"{first}:") && spent.any (·.startsWith s!"{second}:"))
      s!"Bob's spend did not spend both card coins ({first}, {second}): {spent}"
    h.expectPays spendTx bank payment
    h.mine 1
    waitFor broadcastConfirmed 90
    expect (← h.confirmed spendTx) "the node's wallet has not confirmed Bob's spend of card coins"
    tap closeSendButton
    expectGone closeSendButton 10
    waitUntil 60 "Bob's balance after spending card coins" (every := 1) do
      return (← balance) == some (totalReceived - payment - fee)
    waitFor (historyPayment spendTx) 20
    shot "75-card-coins-spent"⟩

/-- Restoring a pre-card backup from iCloud discovers payments made to a post-backup card and spends them.
Bob backs up to iCloud before issuing any card, freezes automatic backup, issues Dana's card, and receives
funding to it. A fresh device restores that pre-card iCloud backup, discovers the post-backup card payment
through `beginCardRestore` / `finishCardRestore`, and spends it back to Core. -/
def cardRestoreFromBackup : Journey := ⟨"cardRestoreFromBackup", do
  let r ← Run.new "cardrestore"
  let h := r.host
  let cloud := s!"{h.fixture}/icloud-cardrestore-{← randomHex 4}"
  IO.FS.createDirAll cloud
  let cloudBackups : IO (List (String × ByteArray)) := do
    let mut out : Array (String × ByteArray) := #[]
    for entry in ← (System.FilePath.mk cloud).readDir do
      if entry.fileName.endsWith ".backup" then
        let id := (entry.fileName.dropEnd ".backup".length).copy
        out := out.push (id, ← IO.FS.readBinFile entry.path)
    return (out.qsort (·.1 < ·.1)).toList

  let (backupID, frozen) ← step "Bob creates a wallet, waits for its pre-card iCloud backup, and turns automatic backup off" do
    r.launch "cardrestore1" [("WINNOW_E2E_CLOUD", cloud)]
    createWallet
    waitSynced
    waitUntil 60 "the initial iCloud backup was not saved" (every := 0.5) do
      return !(← cloudBackups).isEmpty
    openSettings
    scrolled (.button "iCloud backup")
    tap (.button "iCloud backup")
    waitFor automaticCloudBackupToggle 10
    waitUntil 30 "iCloud backup did not report Backed up" (every := 0.5) do
      return (← text cloudBackupStatus).startsWith "Backed up"
    tap automaticCloudBackupToggle
    waitUntil 10 "automatic iCloud backup did not turn off" (every := 0.25) do
      return (← text cloudBackupStatus) == "Off"
    tap (.button "Close")
    expectGone automaticCloudBackupToggle 10
    backToWalletList
    let frozen ← cloudBackups
    match frozen with
    | [(id, _)] => pure (id, frozen)
    | _ => failure s!"expected one frozen backup in {cloud}, found {frozen.length}"

  let fundTx ← step "Bob issues Dana's card after the frozen backup, and Dana pays it" do
    discard Receive.address
    makeCardFor "Dana"
    let card ← text personCardText
    Receive.close
    expectGone closeReceiveButton 10
    let cardAddr ← h.cardAddress card 0
    expect (cardAddr.startsWith "bcrt1p") s!"not a regtest Taproot address: {cardAddr}"
    let fundTx ← h.fund cardAddr funding
    waitForBalance funding
    expect ((← cloudBackups) == frozen) "the frozen iCloud backup changed after automatic backup was turned off"
    pure fundTx

  step "a fresh device restores the pre-card iCloud backup, discovers the post-backup card coin, and spends it" do
    r.launch "cardrestore2" [("WINNOW_E2E_CLOUD", cloud)]
    waitFor restoreCloudBackupButton 60
    tap restoreCloudBackupButton
    let backupButton : Find := cloudRestoreBackupButton backupID
    waitFor backupButton 30
    waitUntil 20 "the iCloud backup row did not show its wallet label" (every := 0.25) do
      return (← text backupButton 1).startsWith "Wallet "
    shot "76-card-restore-icloud"
    tap backupButton
    waitFor (.button "Continue") 90
    tap (.button "Continue")
    expectGone (.button "Continue") 10
    waitFor receiveButton 60
    waitFor balanceText 30
    waitUntil 120 s!"the restored wallet's balance did not reach {funding}" (every := 0.25) do
      return (← amount balanceText) == some funding
    waitSynced
    waitFor (historyPayment fundTx) 30
    shot "77-card-restore-found"

    let destination ← h.bankAddress
    tap openSendButton
    Send.fill r destination payment
    let fee ← Send.expectReview destination payment
    let spendTx ← Send.send h
    let spent := spends (← h.transaction spendTx)
    expect (spent.any (·.startsWith s!"{fundTx}:"))
      s!"the restored wallet's spend did not spend the post-backup card coin {fundTx}: {spent}"
    h.expectPays spendTx destination payment
    h.mine 1
    waitFor broadcastConfirmed 90
    expect (← h.confirmed spendTx) "the node's wallet has not confirmed the restored wallet's spend"
    tap closeSendButton
    expectGone closeSendButton 10
    waitUntil 60 "the restored wallet's balance after the spend" (every := 1) do
      return (← balance) == some (funding - payment - fee)
    waitFor (historyPayment spendTx) 20
    shot "78-card-restore-spent"⟩

end WinnowJourneys
