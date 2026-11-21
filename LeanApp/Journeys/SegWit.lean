import LeanNative.Journey
import Winnow.Wallet.SegwitSpendReview
import WinnowApp.Ids
import Journeys.Screens

/-! # SegWit v0 multisig journey: `wsh(sortedmulti(2, FIXED, phoneKey, otherKey))` -/

namespace WinnowJourneys
open Lean LeanNative LeanNative.Journey WinnowApp.Ids

/-- Joining a SegWit v0 2-of-3 multisig account (`wsh(sortedmulti(2, FIXED, phoneKey, otherKey))`), receiving
bitcoin, reviewing and co-signing Core's pre-signed PSBT (where Core's watch-only wallet builds the spend and
its service wallet signs with the fixed key), verifying the finalized P2WSH witness on the node, and
confirming on both Core and the phone. -/
def segwitMultisigJoinSign : Journey := ⟨"segwitMultisigJoinSign", do
  let r ← Run.new "segwit"
  let h := r.host
  let run ← randomHex 4
  r.launch "segwit"
  createWallet

  let acct ← step "read this phone's key and construct the SegWit v0 2-of-3 account on Core" do
    openMultisigAccounts
    scrolled multisigAddButton
    tap multisigAddButton
    waitFor multisigKeyText 10
    let phoneKey ← text multisigKeyText
    h.segwitAccount run phoneKey

  try
    let account := accountID acct.descriptor
    let expectedAddr ← step "join the SegWit v0 account from its pasted descriptor" do
      scrolled multisigNameField
      type multisigNameField "Exchange"
      scrolled multisigDescriptorPasteButton
      r.paste acct.descriptor multisigDescriptorPasteButton
      waitUntil 20 "the pasted account did not validate" do
        if ← exists? multisigAddPolicy 1 then return true
        scrollTo multisigAddPolicy
      scrolled multisigAddPolicy
      expectEq "the pasted account's policy" (← text multisigAddPolicy) "2 of 3"
      expect (!(← exists? multisigAddWarning)) "the SegWit descriptor showed an unexpected warning"
      waitUntil 20 "the account's first address did not appear" do
        if ← exists? multisigFirstAddress 1 then return true
        scrollTo multisigFirstAddress
      scrolled multisigFirstAddress
      let expectedAddr ← h.deriveSegwitAddress acct.descriptor 0
      expect (expectedAddr.startsWith "bcrt1q") s!"not a regtest SegWit v0 address: {expectedAddr}"
      expectEq "the account's first address (Core's)" (← text multisigFirstAddress) expectedAddr
      shot "80-segwit-join"
      waitUntil 10 "Save did not enable" do return (← state multisigSaveButton).enabled
      tap multisigSaveButton
      openAccountRow account
      pure expectedAddr

    let fundingTx ← step "verify the account page (no Send) and fund it from Core" do
      waitFor multisigPolicy 20
      expectEq "the account's policy" (← text multisigPolicy) "2 of 3"
      expectEq "the account's first address (Core's)" (← Account.receiveAddress) expectedAddr
      scrolled multisigPastePSBTButton
      here multisigPaymentsElsewhere
      expect (!(← exists? multisigSendButton)) "a SegWit v0 account must not offer Send from this account"
      let fundingTx ← h.fund expectedAddr funding
      scrolled multisigBalance
      waitForBalance funding multisigBalance
      shot "81-segwit-funded"
      pure fundingTx

    let destination ← h.bankAddress
    let coreFee ← step "Core builds and pre-signs the PSBT; the phone reviews it at 1 of 2" do
      let (psbt, coreFee) ← h.segwitBuildAndSign acct destination payment
      expect (coreFee > 0) "Core returned a zero fee"
      r.clipboard psbt
      scrolled multisigPastePSBTButton
      tap multisigPastePSBTButton
      waitFor multisigSignatureCount 60
      Collect.countIs multisigSignatureCount "1 of 2"
      scrolled multisigFee
      expectEq "the reviewed fee (Core's)" (← amount multisigFee) (some coreFee)
      scrolled multisigBroadcastButton
      expect (!(← state multisigBroadcastButton).enabled) "one signer alone can broadcast"
      shot "82-segwit-review"
      pure coreFee

    let txid ← step "the phone co-signs to 2 of 2, finalizes and broadcasts, and Core accepts the P2WSH witness" do
      scrolled multisigSignButton
      tap multisigSignButton
      Collect.countIs multisigSignatureCount "2 of 2" 60
      scrolled multisigBroadcastButton
      expect (← state multisigBroadcastButton).enabled "two signatures did not enable broadcast"
      shot "83-segwit-signed"
      -- from the account's own PSBT collection page (not the Send sheet): shows multisigPaymentSent
      let before ← h.mempool
      tap multisigBroadcastButton
      waitFor multisigPaymentSent 30
      let txid ← h.newMempoolTransaction before 30
      expectEq "the shown txid" (← text "multisigTxid") txid
      h.expectPays txid destination payment
      expectEq "the mempool fee" (← h.mempoolFee txid) coreFee
      let input ← h.spendingInput txid
      expectEq "what the spend spends (the funding)" input.txid fundingTx
      expectEq "witness items (dummy, two ECDSA signatures, witnessScript)" input.witness.length 4
      expectEq "OP_CHECKMULTISIG dummy" input.witness[0]! ""
      for (label, sig) in [("first ECDSA signature", input.witness[1]!), ("second ECDSA signature", input.witness[2]!)] do
        expect (sig.startsWith "30" && sig.endsWith "01" && sig.length ≥ 136 && sig.length ≤ 148)
          s!"not a DER ECDSA SIGHASH_ALL signature ({label}): {sig}"
      let script := input.witness[3]!
      expect (script.startsWith "5221" && script.endsWith "53ae")
        s!"not a 2-of-3 sortedmulti witnessScript: {script}"
      let acc ← match Winnow.SegwitMultisigAccount.parse acct.descriptor .regtest with
        | .ok a => pure a
        | .error e => failure s!"could not parse SegWit descriptor: {e.name}"
      let resolved ← match acc.resolved 0 0 with
        | .ok res => pure res
        | .error e => failure s!"could not resolve SegWit address 0: {e.name}"
      expectEq "the derived first address" resolved.output.address expectedAddr
      expectEq "the sortedmulti witnessScript bytes" script (Winnow.hex resolved.witnessScript)
      expectEq "the P2WSH scriptPubKey" (← h.scriptPubKey expectedAddr)
        ("0020" ++ Winnow.hex (Winnow.sha256 resolved.witnessScript))
      pure txid

    step "the spend confirms on Core and the phone" do
      h.mine 1
      expect (← h.confirmed txid) "the node's wallet has not confirmed the payment"
      expect ((← h.tipTransactions).contains txid) "the spend was not mined in the tip block"
      backToWalletList
      waitFor (historyPayment txid) 60
      scrolled (historyPayment txid)
      waitUntil 60 "the spend is not confirmed in Activity" do
        return (← text (historyStatus txid)) == "Confirmed"
      expectEq "the payment's account" (← text (paymentAccount txid)) "Exchange"
      shot "84-segwit-confirmed"
      openAccountRow account
      waitForBalance (funding - payment - coreFee) multisigBalance
  finally
    h.unloadSegwit acct⟩

end WinnowJourneys
