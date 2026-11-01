import LeanNative.Journey
import WinnowApp.Ids
import Journeys.Host

/-! # The journeys' app side: steps, the launch, and the screens as a person uses them

A journey is a list of named steps. Each step is a few of these helpers, named for what a person does on a
screen (`createWallet`, `Send.fill`, `Builder.setRecoveryDays`), with the driver mechanics (which control, how
long to hold a stepper, when to scroll) kept here. The controls are named by `WinnowApp.Ids`, the same
definitions the views use, so a control a journey names but no view gives does not compile.

A step that cannot be done fails with the step's name, the driver's reason and what was on screen, so the
journeys themselves carry no messages or timeouts beyond the few waits that are longer than the driver's. -/

namespace WinnowJourneys
open Lean LeanNative.Journey WinnowApp.Ids

/-- A named phase of a journey, logged with its time; a failure inside says which step it was in. -/
def step (name : String) (body : UI α) : UI α := do
  let start ← IO.monoMsNow
  try
    let a ← body
    let ms := (← IO.monoMsNow) - start
    say s!"  ✓ {name} ({ms / 1000}.{ms % 1000 / 100} s)"
    pure a
  catch e => failure s!"{name}: {e}"

/-- Scrolls to the element; the journey fails if it cannot be brought into view. -/
def scrolled (f : Find) : UI Unit := do
  unless ← scrollTo f do failure s!"{f.describe} cannot be scrolled into view"

/-- The element, now. -/
def here (f : Find) : UI Unit := waitFor f 0

/-- The number a text shows ("1,000,000 sats" is 1000000). -/
def amount (f : Find) : UI (Option Nat) := do return digits (← text f)

/-! ## One journey's run of the app -/

def funding : Nat := 5000000
def payment : Nat := 1000000
def recoveryPayment : Nat := 500000
def silentPayment : Nat := 150000
/-- The builder's shortest recovery delay: one day. -/
def recoveryBlocks : Nat := 144

def randomHex (bytes : Nat) : IO String := do
  let b ← IO.getRandomBytes bytes.toUSize
  let digit (n : Nat) : Char := "0123456789abcdef".toList[n]!
  return String.ofList (b.toList.flatMap fun x => [digit (x.toNat / 16), digit (x.toNat % 16)])

/-- One journey's run of the app: the fixture, and the file test mode's Paste buttons read
(`WINNOW_E2E_CONTROL_FILE`). -/
structure Run where
  host : Host
  control : String

def Run.new (name : String) : IO Run := do
  let host ← Host.load
  return { host, control := s!"{host.fixture}/control-{name}-{← randomHex 4}.json" }

/-- What the app's Paste buttons read next. -/
def Run.clipboard (r : Run) (text : String) : IO Unit :=
  IO.FS.writeFile r.control (Json.mkObj [("clipboard", Json.str text)]).compress

/-- The app in test mode on the fixture's node, as its only peer, with a fresh seed; `extra` adds to the
environment or replaces in it. -/
def Run.launch (r : Run) (run : String) (extra : List (String × String) := []) : UI Unit := do
  let base := [("WINNOW_E2E", "1"), ("WINNOW_E2E_RUN", run), ("WINNOW_E2E_RESET", "1"),
    ("WINNOW_E2E_ENTROPY", ← randomHex 16), ("WINNOW_E2E_NETWORK", "regtest"),
    ("WINNOW_E2E_PEER", s!"127.0.0.1:{r.host.p2p}"), ("WINNOW_E2E_PEER_COUNT", "1"),
    ("WINNOW_E2E_SYNC_INTERVAL", "3"), ("WINNOW_E2E_CONTROL_FILE", r.control)]
  LeanNative.Journey.launch (base.filter (fun (k, _) => !(extra.any (·.1 == k))) ++ extra)

/-- Pastes `text` through the app's Paste button `button`. -/
def Run.paste (r : Run) (text : String) (button : Find) : UI Unit := do
  r.clipboard text
  tap button

/-! ## Onboarding and home -/

/-- Creates the wallet (creation opens it): the home screen with its balance. -/
def createWallet : UI Unit := do
  waitFor createWalletButton 60
  shot "01-onboarding"
  tap createWalletButton
  waitFor receiveButton 60
  waitFor balanceText 30

def balance : UI (Option Nat) := amount balanceText

/-- The balance reaches `target` (the wallet's, or `f`'s). -/
def waitForBalance (target : Nat) (f : Find := balanceText) : UI Unit :=
  waitUntil 90 s!"the balance did not reach {target}" (every := 0.25) do return (← amount f) == some target

def waitSynced : UI Unit :=
  waitUntil 60 "sync is not Up to date" do return (← text syncSummaryText) == "Up to date"

/-- Advanced mode, through its alert, then the Wallet tab. -/
def turnOnAdvanced : UI Unit := do
  tap advancedModeButton
  waitFor (.alert "Turn on") 10
  tap (.alert "Turn on")
  waitFor (.tab "Wallet") 15
  tap (.tab "Wallet")

/-- Back to the Wallet tab's list (the builder and the account it opened are both on its stack). -/
def backToWalletList : UI Unit := do
  for _ in [0:4] do
    if ← exists? balanceText then break
    if ← exists? .back then tap .back
    pause 0.5
  waitFor balanceText 10

/-! ## Receive -/

namespace Receive

/-- Opens Receive and reads the address it shows (its label skipped). -/
def address : UI String := do
  tap receiveButton
  if ← exists? skipReceiveAddressLabelButton 20 then tap skipReceiveAddressLabelButton
  waitFor receiveAddress 30
  let address ← text receiveAddress
  expect (address.startsWith "bcrt1") s!"not a regtest address: {address}"
  return address

def close : UI Unit := tap closeReceiveButton

end Receive

/-! ## Send -/

namespace Send

/-- The destination pasted and the amount typed, and the review opened. -/
def fill (r : Run) (destination : String) (sats : Nat) : UI Unit := do
  r.paste destination pasteDestinationButton
  type amountField (toString sats)
  tap reviewButton
  waitFor sendButton 30

/-- The review's destination and amount are what was entered; the fee it shows. -/
def expectReview (destination : String) (sats : Nat) : UI Nat := do
  expectEq "the reviewed destination" (← text reviewDestination) destination
  expectEq "the reviewed amount" (← amount reviewAmount) (some sats)
  let fee := (← amount reviewFee).getD 0
  expect (fee > 0) "the review shows no fee"
  return fee

/-- Sends the reviewed payment; the transaction the node receives. -/
def send (h : Host) : UI String := do
  let before ← h.mempool
  tap sendButton
  h.newMempoolTransaction before 60

/-- Send, From: the account: the review names the signatures it needs; "Sign and continue" signs here and
opens the collection step. -/
def fromAccount (r : Run) (account destination : String) (sats : Nat) (needs : String) : UI Unit := do
  tap (.tab "Send")
  tap (sendFrom account)
  waitFor sendSourceNote 10
  fill r destination sats
  let signatures ← text reviewSignatures
  expect ((signatures.splitOn needs).length > 1) s!"review: {signatures}"
  scrolled sendButton
  expectEq "the review's button" (← text sendButton) "Sign and continue"
  tap sendButton
  -- the collection step replaces the review once this phone's signature is filed
  waitUntil 90 "the collection step did not open" do
    return (← exists? multisigSignatureCount) || (← exists? (.nav "Collect signatures"))
  scrolled multisigSignatureCount

end Send

/-! ## The collection step -/

namespace Collect

/-- The count `f` shows (`1 of 2`) reaches `expected`. -/
def countIs (f : Find) (expected : String) (within : Float := 60) : UI Unit :=
  waitUntil within s!"{f.describe} is not {expected}" (every := 0.3) do return (← text f 1) == expected

/-- The PSBT the step shows, a BIP174 v0 one. -/
def psbt : UI String := do
  scrolled multisigPSBTText
  let p ← text multisigPSBTText
  -- v0 opens with the unsigned transaction (global key 0x00), v2 with its version (0x02: "cHNidP8BAg")
  expect (p.startsWith "cHNidP8BA" && !p.startsWith "cHNidP8BAg") s!"not a BIP174 v0 PSBT: {p.take 40}"
  return p

/-- A co-signer's signed copy added. -/
def add (r : Run) (signed : String) : UI Unit := do
  r.paste signed psbtPasteButton
  tap addPSBTButton

/-- The phone finalizes and broadcasts; the transaction the node receives. -/
def broadcast (h : Host) : UI String := do
  scrolled multisigBroadcastButton
  let before ← h.mempool
  tap multisigBroadcastButton
  waitFor broadcastPending 30
  h.newMempoolTransaction before 30

end Collect

/-! ## The account builder and the account page -/

namespace Builder

def start : UI Unit := do
  tap multisigBuildButton
  waitFor multisigBuildNameField 20

def name (n : String) : UI Unit := type multisigBuildNameField n

/-- Another Winnow's key, pasted into the member picker. -/
def addPastedMember (r : Run) (keyExpression : String) : UI Unit := do
  r.clipboard keyExpression
  tap multisigBuildAddMemberButton
  tap signerPickerPasteButton

/-- A paired Ledger, chosen in the member picker. -/
def addLedgerMember (ledgerName : String) : UI Unit := do
  tap multisigBuildAddMemberButton
  waitFor (.button ledgerName) 10
  tap (.button ledgerName)

/-- Recovery after a delay, turned on; the delay the builder proposes. -/
def turnOnRecovery : UI String := do
  tap multisigBuildRecoveryToggle
  waitFor (.beginning "Any 1 of the 3 members") 10
  scrolled multisigBuildRecoveryDaysStepper
  text (.text "^After about \\d+ days \\(")

/-- The delay stepper's text, now. -/
private def delayText : UI String := text (.text "^After about \\d+ days \\(") 5

/-- The recovery delay brought down to `days`. The stepper's step is a day, and held down it repeats faster
and faster: held 10 s it goes from 181 to 74 days, 14 s to one day; 16 s leaves a margin. The last few days
are single taps. -/
def setRecoveryDays (days : Nat) : UI Unit := do
  let dec : Find := decrement multisigBuildRecoveryDaysStepper
  for _ in [0:5] do
    let now := (digits ((← delayText).splitOn " days").head!).getD 0
    if now ≤ days then break
    if now ≤ days + 4 then tap dec (times := now - days) else press dec 16
  expectEq "the delay" (← delayText) s!"After about {days} days ({days * 144} blocks)"

/-- Creates the account; its descriptor. -/
def create : UI String := do
  tap multisigBuildCreateButton
  waitFor multisigBuildCreated 30
  scrolled multisigCreatedDescriptor
  let descriptor ← text multisigCreatedDescriptor
  expect (descriptor.startsWith "tr(") s!"not a descriptor: {descriptor}"
  return descriptor

def openAccount : UI Unit := tap multisigOpenAccountButton

end Builder

namespace Account

/-- The account page's receive address. -/
def receiveAddress : UI String := do
  waitFor multisigReceiveAddress 20
  text multisigReceiveAddress

end Account

/-! ## Signers and the Ledger -/

namespace Ledger

/-- Settings → Signers → Pair a Ledger, named `name`. -/
def pair (name : String) : UI Unit := do
  tap (.tab "Settings")
  tap signersButton
  tap signersPairLedgerButton
  type ledgerNameField name
  tap ledgerPairButton
  waitFor (.button name) 60

/-- The Ledger derives the address the page shows; what it said. -/
def verifyAddress : UI String := do
  tap ledgerVerifyButton
  waitFor ledgerVerifyResult 60
  text ledgerVerifyResult

end Ledger

end WinnowJourneys
