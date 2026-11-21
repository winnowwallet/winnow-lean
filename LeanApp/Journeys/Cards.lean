import LeanNative.Journey
import WinnowApp.Ids
import Journeys.Screens

/-! # Person-card journeys: receiving, paying, rotating, spending, and restoring a post-backup card -/

namespace WinnowJourneys
open Lean LeanNative LeanNative.Journey WinnowApp.Ids

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

/-- Restoring a pre-card backup from iCloud discovers payments made to a post-backup card and spends them. -/
def cardRestoreFromBackup : Journey := ⟨"cardRestoreFromBackup", do
  failure "cardRestoreFromBackup not yet implemented"⟩

end WinnowJourneys
