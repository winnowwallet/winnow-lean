import Journeys.Screens

/-! # Journeys in which the chain changes under the wallet

The fixture's node can take a block back (`invalidateblock`) and mine a longer chain without it, as a reorganisation
does on mainnet: the wallet must follow the chain with the most work, and what the lost block confirmed is
unconfirmed again until a block of the new chain takes it. -/

namespace WinnowJourneys
open Lean LeanNative LeanNative.Journey WinnowApp.Ids

/-- The node takes back its tip and mines `blocks` empty blocks on the block before it (the mempool's transactions
left out, the one the tip confirmed among them): a longer chain without that tip. -/
def Host.reorganise (h : Host) (blocks : Nat := 2) : IO Unit := do
  let tip ← h.cli #["getbestblockhash"]
  discard <| h.cli #["invalidateblock", tip]
  let address ← h.bankAddress
  for _ in [0:blocks] do discard <| h.cli #["generateblock", address, "[]"]
  h.waitFilterIndex

/-- A payment confirmed, then its block replaced by a longer chain without it: Activity shows it pending again,
the wallet keeps it (its coins stay spent, its change unconfirmed), and when a block of the new chain takes it,
it is confirmed in that block. -/
def reorgBackToPending : Journey := ⟨"reorgBackToPending", do
  let r ← Run.new "reorg"
  let h := r.host
  r.launch "reorg"
  createWallet

  step "the node funds the wallet" do
    let address ← Receive.address
    Receive.close
    discard <| h.fund address funding
    waitForBalance funding

  let destination ← h.bankAddress
  let (txid, fee) ← step "pay the node and see the payment confirm" do
    tap openSendButton
    Send.fill r destination payment
    let fee ← Send.expectReview destination payment
    let txid ← Send.send h
    h.mine 1
    waitFor broadcastConfirmed 90
    tap closeSendButton
    backToWalletList
    scrolled (historyPayment txid)
    waitUntil 60 "the payment's row is not confirmed" do return (← text (historyStatus txid)) == "Confirmed"
    pure (txid, fee)

  step "the block that confirmed it is replaced by a longer chain without it: the payment is pending again" do
    let before ← h.height
    h.reorganise 2
    expect (!(← h.confirmed txid)) "the node still has the payment confirmed"
    expectEq "the node's height after the reorganisation" (← h.height) (before + 1)
    scrolled (historyPayment txid)
    waitUntil 90 "the payment's row is not pending again" (every := 1) do
      return (← text (historyStatus txid)) == "Pending"
    shot "80-reorg-pending"
    -- while the wallet scans the new chain the home may show less: once it has, the payment is still spent
    let start ← IO.monoMsNow
    waitForBalance (funding - payment - fee)
    log s!"the balance was back {(← IO.monoMsNow) - start} ms after the payment showed pending"

  step "a block of the new chain takes it: confirmed again, in that block" do
    h.mine 1
    let height ← h.height
    scrolled (historyPayment txid)
    waitUntil 90 "the payment's row is not confirmed again" (every := 1) do
      return (← text (historyStatus txid)) == "Confirmed"
    tap (historyPayment txid)
    scrolled paymentBlock
    expectEq "the block that confirmed it" (← text paymentBlock) s!"{height}"
    shot "81-reorg-confirmed-again"⟩

end WinnowJourneys
