import LeanNative.Journey
import LeanNative.Journey.Wire
import WinnowApp.Main

/-! # The UI journeys

The app in the simulator against the regtest node `backend-test --fixture` left running (scripts/ui-fixture),
driven through LeanNative's journey driver (LeanNative.Journey: each step one command to the test kit's
LNDriver, each check here, on the Mac). Each journey launches the app in test mode with a fresh random seed,
so a reused node never shows an earlier run's coins, and checks what the app shows against what the node
holds. scripts/ui-journeys runs them locally, CI through LeanNative's ios-app workflow (`ui-journey:
journeys`); the screenshots' names are the website's (scripts/journey-media). -/

namespace WinnowJourneys
open Lean LeanNative LeanNative.Journey

def funding : Nat := 5000000
def payment : Nat := 1000000
def recoveryPayment : Nat := 500000
def silentPayment : Nat := 150000
/-- The builder's shortest recovery delay: one day. -/
def recoveryBlocks : Nat := 144

/-! ## The host: the fixture's node, bitcoin-cli and backend-test -/

def readJson (path : String) : IO Json := do
  match Json.parse (← IO.FS.readFile path) with
  | .ok j => pure j
  | .error e => failure s!"{path} is not JSON: {e}"

def field [FromJson α] (j : Json) (key : String) : IO α :=
  match j.getObjValAs? α key with
  | .ok v => pure v
  | .error e => failure s!"{key}: {e} in {j.compress.take 300}"

/-- The fixture `scripts/ui-fixture start` left: its ui.json (WINNOW_UI_CONFIG, from test-env) and the node's
fixture.json. -/
structure Host where
  bitcoinCli : String
  /-- LeanApp's backend-test: the silent payment test receiver -/
  backendTest : String
  fixture : String
  datadir : String
  rpc : Nat
  p2p : Nat

def Host.load : IO Host := do
  let some path ← IO.getEnv "WINNOW_UI_CONFIG"
    | failure "no WINNOW_UI_CONFIG: scripts/ui-fixture start writes it to the run's test-env"
  let c ← readJson path
  let fixture : String ← field c "fixture"
  let f ← readJson s!"{fixture}/fixture.json"
  return { bitcoinCli := ← field c "bitcoinCli", backendTest := ← field c "backendTest", fixture,
           datadir := ← field f "datadir", rpc := ← field f "rpc", p2p := ← field f "p2p" }

/-- A host program's standard output, trimmed; a nonzero exit fails the journey with its standard error.
backend-test reaches the node through the same pinned Core (WINNOW_BITCOIN_CLI). -/
def Host.run (h : Host) (cmd : String) (args : Array String) : IO String := do
  let out ← IO.Process.output { cmd, args, env := #[("WINNOW_BITCOIN_CLI", some h.bitcoinCli)] }
  if out.exitCode != 0 then
    failure s!"{(cmd.splitOn "/").getLast!} {" ".intercalate args.toList} exited {out.exitCode}: {out.stderr.trimAscii}"
  return out.stdout.trimAscii.copy

def Host.cli (h : Host) (args : Array String) : IO String :=
  h.run h.bitcoinCli (#["-regtest", s!"-datadir={h.datadir}", s!"-rpcport={h.rpc}"] ++ args)

/-- bitcoin-cli with -rpcwallet (the fixture's funded wallet is `w`). -/
def Host.wallet (h : Host) (wallet : String) (args : Array String) : IO String :=
  h.cli (#[s!"-rpcwallet={wallet}"] ++ args)

def parseCli (args : Array String) (text : String) : IO Json :=
  match Json.parse text with
  | .ok j => pure j
  | .error _ => failure s!"bitcoin-cli {args}: not JSON: {text.take 300}"

def Host.cliJson (h : Host) (args : Array String) : IO Json := do parseCli args (← h.cli args)
def Host.walletJson (h : Host) (wallet : String) (args : Array String) : IO Json := do
  parseCli args (← h.wallet wallet args)

def strings (j : Json) : List String :=
  match j.getArr? with
  | .ok a => a.toList.filterMap fun s => (s.getStr?).toOption
  | .error _ => []

def Host.mempool (h : Host) : IO (List String) := do return strings (← h.cliJson #["getrawmempool"])
def Host.bankAddress (h : Host) : IO String := h.wallet "w" #["getnewaddress"]
def Host.height (h : Host) : IO Nat := do return (← h.cli #["getblockcount"]).toNat!
/-- Until the node's block filter index reaches its tip. The app asks for filters up to the tip it has
synced; a request past the index goes unanswered until it times out, and the app then drops its only peer. -/
def Host.waitFilterIndex (h : Host) : IO Unit := do
  let tip ← h.height
  for _ in [0:600] do
    let info ← h.cliJson #["getindexinfo", "basic block filter index"]
    let best := ((info.getObjValD "basic block filter index").getObjValAs? Nat "best_block_height").toOption.getD 0
    if best ≥ tip then return
    IO.sleep 50
  failure "the node's block filter index did not reach its tip in 30 s"

def Host.mine (h : Host) (blocks : Nat) : IO Unit := do
  discard <| h.cli #["generatetoaddress", toString blocks, ← h.bankAddress]
  h.waitFilterIndex

/-- `blocks` blocks paying an anyone-can-spend script: no wallet on the node scans them in, so many blocks mine
in a moment. -/
def Host.mineElsewhere (h : Host) (blocks : Nat) : IO Unit := do
  let some d := ((← h.cliJson #["getdescriptorinfo", "raw(51)"]).getObjValAs? String "descriptor").toOption
    | failure "getdescriptorinfo raw(51)"
  discard <| h.cli #["generatetodescriptor", toString blocks, d]
  h.waitFilterIndex

def btc (sats : Nat) : String :=
  let frac := toString (sats % 100000000)
  s!"{sats / 100000000}.{String.ofList (List.replicate (8 - frac.length) '0')}{frac}"

/-- Pays `sats` from the funded wallet to `address` and mines it; the payment's txid. -/
def Host.fund (h : Host) (address : String) (sats : Nat) : IO String := do
  let txid ← h.wallet "w" #["sendtoaddress", address, btc sats]
  h.mine 1
  return txid

/-- A transaction in the mempool, decoded by the node (a confirmed one needs a wallet's gettransaction: the
node keeps no txindex). -/
def Host.transaction (h : Host) (txid : String) : IO Json := h.cliJson #["getrawtransaction", txid, "true"]

def Host.scriptPubKey (h : Host) (address : String) : IO String := do
  field (← h.cliJson #["validateaddress", address]) "scriptPubKey"

/-- backend-test's silent payment test receiver (written from BIP352's receiving side): its code, and the
output script it finds in a transaction on the node. -/
def Host.silentPaymentCode (h : Host) : IO String := h.run h.backendTest #["--sp-code"]
def Host.silentPaymentExpectedScript (h : Host) (txid : String) : IO String :=
  h.run h.backendTest #["--sp-expected", h.datadir, toString h.rpc, txid]

/-- The transactions in the tip block. -/
def Host.tipTransactions (h : Host) : IO (List String) := do
  return strings ((← h.cliJson #["getblock", ← h.cli #["getbestblockhash"]]).getObjValD "tx")

/-- An output of a decoded transaction: its script, address and value in sats (exact, from the JSON number). -/
structure Output where
  script : String
  address : String
  sats : Nat

def outputs (tx : Json) : List Output :=
  match (tx.getObjValD "vout").getArr? with
  | .error _ => []
  | .ok vs => vs.toList.map fun o =>
    let spk := o.getObjValD "scriptPubKey"
    let sats := match o.getObjValD "value" with
      | .num n => (n.mantissa * 100000000 / (10 : Int) ^ n.exponent).toNat
      | _ => 0
    { script := (spk.getObjValAs? String "hex").toOption.getD "", address := (spk.getObjValAs? String "address").toOption.getD "", sats }

/-- Whether the transaction pays `sats` to `script`. -/
def pays (tx : Json) (script : String) (sats : Nat) : Bool := (outputs tx).any fun o => o.script == script && o.sats == sats

/-- The first input of a decoded transaction: what it spends, its sequence and its witness. -/
structure Input where
  txid : String
  sequence : Nat
  witness : List String

def Host.spendingInput (h : Host) (txid : String) : IO Input := do
  let tx ← h.transaction txid
  let some vin := ((tx.getObjValD "vin").getArr?.toOption.bind (·[0]?)) | failure s!"{txid} has no input"
  return { txid := ← field vin "txid", sequence := ← field vin "sequence", witness := strings (vin.getObjValD "txinwitness") }

/-- Hex lengths of the witness's first `count` items, sorted. -/
def witnessSizes (witness : List String) (count : Nat) : List Nat :=
  ((witness.take count).map String.length).toArray.qsort (· < ·) |>.toList

/-! ## Descriptors, and Bitcoin Core as the other signer -/

def body (descriptor : String) : String := (descriptor.splitOn "#").head!

/-- The account's id: its descriptor's checksum. -/
def accountID (descriptor : String) : String :=
  match descriptor.splitOn "#" with
  | [_] => ""
  | parts => parts.getLast!

/-- A descriptor with its checksum, as the node computes it. -/
def Host.withChecksum (h : Host) (descriptor : String) : IO String := do
  let b := body descriptor
  let checksum : String ← field (← h.cliJson #["getdescriptorinfo", b]) "checksum"
  return s!"{b}#{checksum}"

/-- Each `<a;b>` read as `a`: a descriptor's first branch. -/
def firstBranch (s : String) : String := Id.run do
  let mut out := ""
  let mut inside := false
  let mut keep := true
  for c in s.toList do
    if c == '<' then inside := true; keep := true
    else if inside && c == ';' then keep := false
    else if inside && c == '>' then inside := false
    else if !inside || keep then out := out.push c
  return out

/-- The descriptor's address at `index` on its first branch, derived by the node. -/
def Host.deriveAddress (h : Host) (descriptor : String) (index : Nat) : IO String := do
  let addresses ← h.cliJson #["deriveaddresses", ← h.withChecksum (firstBranch (body descriptor)), s!"[{index},{index}]"]
  let some a := (strings addresses).head? | failure s!"the node derived no address from {descriptor}"
  return a

/-- A Bitcoin Core wallet as the other signer of a multisig account: its own seed, its own libsecp256k1. The
app gets its key as `[fp/86'/1'/0']tpub…/<0;1>/*`; Core gets the account's descriptor with that key's tprv in
its place, and signs the PSBTs the app shares. -/
structure CoreSigner where
  wallet : String
  fingerprint : String
  tpub : String
  tprv : String

def CoreSigner.keyExpression (c : CoreSigner) : String := s!"[{c.fingerprint}/86'/1'/0']{c.tpub}/<0;1>/*"

/-- The Taproot (BIP86) descriptor of the wallet's receive branch, public or private. -/
def Host.taprootDescriptor (h : Host) (wallet : String) (priv : Bool) : IO String := do
  let list ← h.walletJson wallet #["listdescriptors", toString priv]
  let ds := ((list.getObjValD "descriptors").getArr?.toOption.getD #[]).toList
  for d in ds do
    let desc := (d.getObjValAs? String "desc").toOption.getD ""
    if desc.startsWith "tr(" && !((d.getObjValAs? Bool "internal").toOption.getD false) then return desc
  failure s!"{wallet} has no Taproot descriptor"

/-- A new descriptor wallet `name` on the fixture's node. -/
def Host.coreSigner (h : Host) (name : String) : IO CoreSigner := do
  discard <| h.cli #["-named", "createwallet", s!"wallet_name={name}"]
  -- tr([fp/86h/1h/0h]tpub…/0/*)#… and tr(tprv…/86h/1h/0h/0/*)#…
  let pub ← h.taprootDescriptor name false
  let (fingerprint, tpub) ← match pub.splitOn "/86h/1h/0h]" with
    | [head, rest] => pure ((head.drop 4).copy, (rest.splitOn "/0/*)").head!)
    | _ => failure s!"unexpected descriptor {pub}"
  let priv ← h.taprootDescriptor name true
  let tprv := ((priv.splitOn "/86h/1h/0h/0/*)").head!.drop 3).copy
  unless fingerprint.length == 8 && tpub.startsWith "tpub" && tprv.startsWith "tprv" do
    failure s!"unexpected descriptors for {name}: {pub}"
  return { wallet := name, fingerprint, tpub, tprv }

/-- Imports the account (the descriptor the app shows) with this wallet's private key in its place. -/
def Host.importAccount (h : Host) (c : CoreSigner) (descriptor : String) : IO Unit := do
  let b := body descriptor
  let mine := ["'", "h"].foldl (fun s mark =>
    s.replace s!"[{c.fingerprint}/86{mark}/1{mark}/0{mark}]{c.tpub}" s!"{c.tprv}/86h/1h/0h") b
  if mine == b then failure s!"{c.wallet}'s key is not in {descriptor}"
  let request := Json.arr #[Json.mkObj [("desc", Json.str (← h.withChecksum mine)), ("timestamp", "now"),
                                        ("range", Json.arr #[0, 50])]]
  let result ← h.walletJson c.wallet #["importdescriptors", request.compress]
  for r in (result.getArr?.toOption.getD #[]) do
    unless (r.getObjValAs? Bool "success").toOption.getD false do failure s!"importdescriptors: {r.compress}"

/-- The PSBT with this wallet's signatures added. -/
def Host.sign (h : Host) (c : CoreSigner) (psbt : String) : IO String := do
  field (← h.walletJson c.wallet #["walletprocesspsbt", psbt, "true", "DEFAULT", "true", "false"]) "psbt"

/-! ## The app -/

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

/-- The journey fails with `message` unless the element appears within `within` seconds. -/
def need (f : Find) (within : Float) (message : String) : UI Unit := do
  unless ← exists? f within do failure message

def needScroll (f : Find) (message : String) : UI Unit := do
  unless ← scrollTo f do failure message

def amount (f : Find) : UI (Option Nat) := do return digits (← text f)
def balance : UI (Option Nat) := amount "balanceText"

/-- Creates the wallet (creation opens it): the home screen with its balance. -/
def createWallet : UI Unit := do
  need "createWalletButton" 60 "onboarding did not open"
  shot "01-onboarding"
  tap "createWalletButton"
  need "receiveButton" 60 "the wallet did not open"
  waitFor "balanceText" 30

/-- The receive address the app shows (its label skipped). -/
def receiveAddress : UI String := do
  tap "receiveButton"
  if ← exists? "skipReceiveAddressLabelButton" 20 then tap "skipReceiveAddressLabelButton"
  need "receiveAddress" 30 "Receive shows no address"
  let address ← text "receiveAddress"
  expect (address.startsWith "bcrt1") s!"not a regtest address: {address}"
  return address

def waitForBalance (target : Nat) (what : String) (f : Find := "balanceText") : UI Unit :=
  waitUntil 90 s!"{what} (balance {target})" (every := 0.25) do return (← amount f) == some target

/-- The one transaction that entered the mempool after `before`. -/
def newMempoolTransaction (h : Host) (before : List String) (within : Float) (what : String) : UI String := do
  let found ← IO.mkRef (none : Option String)
  waitUntil within what (every := 0.25) do
    let now ← h.mempool
    found.set (now.find? (!before.contains ·))
    return (← found.get).isSome
  return (← found.get).get!

/-- Advanced mode, through its alert, then the Wallet tab. -/
def turnOnAdvanced : UI Unit := do
  tap "advancedModeButton"
  need (.alert "Turn on") 10 "no Advanced mode alert"
  tap (.alert "Turn on")
  need (.tab "Wallet") 15 "Advanced mode shows no tabs"
  tap (.tab "Wallet")

/-- Back to the Wallet tab's list (the builder and the account it opened are both on its stack). -/
def backToWalletList : UI Unit := do
  for _ in [0:4] do
    if ← exists? "balanceText" then break
    if ← exists? .back then tap .back
    pause 0.5
  need "balanceText" 10 "the Wallet tab did not return to its list"

/-- Send, From: the account: the review names it and the signatures it needs; "Sign and continue" signs here
and opens the collection step. -/
def sendFromAccount (r : Run) (account destination : String) (sats : Nat) (needs : String) : UI Unit := do
  tap (.tab "Send")
  tap s!"sendFrom-{account}"
  need "sendSourceNote" 10 "the account is not the source"
  r.clipboard destination
  tap "pasteDestinationButton"
  type "amountField" (toString sats)
  tap "reviewButton"
  need "reviewSignatures" 30 "the account review did not open"
  let signatures ← text "reviewSignatures"
  expect ((signatures.splitOn needs).length > 1) s!"review: {signatures}"
  needScroll "sendButton" "no Sign and continue"
  expectEq "the review's button" (← text "sendButton") "Sign and continue"
  tap "sendButton"
  -- the collection step replaces the review once this phone's signature is filed
  waitUntil 90 "the collection step did not open" do
    return (← exists? "multisigSignatureCount") || (← exists? (.nav "Collect signatures"))
  needScroll "multisigSignatureCount" "the collection step shows no signature count"

def countIs (f : Find) (expected : String) (within : Float) (what : String) : UI Unit :=
  waitUntil within s!"{what}: the count is not {expected}" (every := 0.3) do return (← text f 1) == expected

/-! ## The journeys -/

/-- Create a wallet, receive from the node, send to it and see the payment confirm. -/
def createReceiveSendConfirm : Journey := ⟨"createReceiveSendConfirm", do
  let r ← Run.new "journey"
  let h := r.host
  let destination ← h.bankAddress
  r.clipboard destination
  r.launch "journey"
  createWallet
  let address ← receiveAddress
  shot "03-receive"
  tap "closeReceiveButton"

  let fundingTx ← h.fund address funding
  waitForBalance funding "the wallet did not find the confirmed payment"
  need s!"historyPayment-{fundingTx}" 20 "the funding transaction is missing from Activity"
  waitUntil 60 "sync is not Up to date" do return (← text "syncSummaryText") == "Up to date"
  shot "04-home-funded"

  tap "openSendButton"
  tap "pasteDestinationButton"
  type "amountField" (toString payment)
  tap "reviewButton"
  need "sendButton" 30 "the payment review did not open"
  expectEq "the reviewed destination" (← text "reviewDestination") destination
  expectEq "the reviewed amount" (← amount "reviewAmount") (some payment)
  let fee := (← amount "reviewFee").getD 0
  expect (fee > 0) "the review shows no fee"
  shot "05-send-review"

  let before ← h.mempool
  tap "sendButton"
  let txid ← newMempoolTransaction h before 60 "the node never received the payment"
  expect (pays (← h.transaction txid) (← h.scriptPubKey destination) payment)
    "the transaction the node accepted does not pay the reviewed destination the reviewed amount"

  h.mine 1
  need "broadcastConfirmed" 90 "the open receipt did not notice the confirmation"
  -- the payment is to the node's wallet, which knows it once confirmed (the node keeps no txindex)
  let confirmations : Nat ← field (← h.walletJson "w" #["gettransaction", txid]) "confirmations"
  expect (confirmations > 0) "the node's wallet has not confirmed the payment"
  shot "06-send-confirmed"
  tap "closeSendButton"
  waitUntil 60 "the balance after the payment" (every := 1) do
    return (← balance) == some (funding - payment - fee)
  need s!"historyPayment-{txid}" 20 "the payment is missing from Activity"
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
  turnOnAdvanced

  -- the account, in the app's builder: this phone and the two Core keys as members, any 2 of 3, any 1 after a day
  tap "multisigBuildButton"
  type "multisigBuildNameField" "Phone and two Cores"
  for signer in [core, second] do
    r.clipboard signer.keyExpression
    tap "multisigBuildAddMemberButton"
    tap "signerPickerPasteButton"
  need (.beginning "Members · 3") 10 "the two Core keys were not added"
  need (.beginning "Any 2 of 3 members spend") 0 "no threshold line"
  need (.beginning "2 of 3: any 2 of the 3 keys sign a spend.") 10 "no policy preview"
  tap "multisigBuildRecoveryToggle"
  need (.beginning "Any 1 of the 3 members") 10 "no recovery line"
  needScroll "multisigBuildRecoveryDaysStepper" "no recovery delay"
  let delay : Find := .text "^After about \\d+ days \\("
  let shown ← text delay
  expect (shown.startsWith "After about 181 days (26,000 blocks)") s!"the default delay: {shown}"
  -- the stepper's step is a day: held down, it repeats to its least, one day (a tap per day took minutes).
  -- Its repeat speeds up: held 10 s it goes from 181 to 74 days, 14 s to one day; 16 s leaves a margin.
  let decrement : Find := "multisigBuildRecoveryDaysStepper-Decrement"
  for _ in [0:5] do
    let days := (digits ((← text delay).splitOn " days").head!).getD 0
    if days ≤ 1 then break
    if days ≤ 5 then tap decrement (times := days - 1) else press decrement 16
  expectEq "the delay" (← text delay) s!"After about 1 days ({recoveryBlocks} blocks)"
  shot "10-multisig-build"
  tap "multisigBuildCreateButton"
  need "multisigBuildCreated" 30 "the account was not created"
  needScroll "multisigCreatedDescriptor" "the builder shows no descriptor"
  let descriptor ← text "multisigCreatedDescriptor"
  expect (descriptor.startsWith "tr(") s!"not a descriptor: {descriptor}"
  let account := accountID descriptor
  h.importAccount core descriptor
  h.importAccount second descriptor
  tap "multisigOpenAccountButton"

  -- receive: the address on screen is Core's first address of the account
  let first ← h.deriveAddress descriptor 0
  waitFor "multisigReceiveAddress" 20
  expectEq "the account's first address (Core's)" (← text "multisigReceiveAddress") first
  let fundingTx ← h.fund first funding
  waitForBalance funding "the account did not find its funding" "multisigBalance"
  shot "11-multisig-funded"

  -- Send, From: the account; Sign and continue signs here; one signature is not enough
  let destination ← h.bankAddress
  sendFromAccount r account destination payment "needs 2 of 3"
  countIs "multisigSignatureCount" "1 of 2" 60 "after Sign and continue"
  let fee := (← amount "multisigFee").getD 0
  expect (fee > 0) "the collection step shows no fee"
  needScroll "multisigBroadcastButton" "no Broadcast button"
  expect (!(← state "multisigBroadcastButton").enabled) "one signer alone can send"
  needScroll "multisigPSBTText" "the collection step shows no PSBT"
  let phoneSigned ← text "multisigPSBTText"
  -- v0 opens with the unsigned transaction (global key 0x00), v2 with its version (0x02: "cHNidP8BAg")
  expect (phoneSigned.startsWith "cHNidP8BA" && !phoneSigned.startsWith "cHNidP8BAg") s!"not a BIP174 v0 PSBT: {phoneSigned.take 40}"
  shot "12-multisig-one-signature"

  -- each Core wallet signs its own copy; the phone combines both
  for (signer, expected) in [(core, "2 of 2"), (second, "3 of 2")] do
    r.clipboard (← h.sign signer phoneSigned)
    tap "psbtPasteButton"
    tap "addPSBTButton"
    countIs "multisigSignatureCount" expected 30 s!"after {signer.wallet}"

  -- the phone finalizes and broadcasts; Core accepts a witness with exactly two signatures
  let before ← h.mempool
  tap "multisigBroadcastButton"
  need "broadcastPending" 30 "the receipt did not open"
  let txid ← newMempoolTransaction h before 30 "Core did not accept the multisig payment"
  let input ← h.spendingInput txid
  expectEq "what the spend spends (the funding)" input.txid fundingTx
  expectEq "witness items (three key slots, the leaf script and the control block)" input.witness.length 5
  expectEq "the witness's signatures (exactly two of 64 bytes)" (witnessSizes input.witness 3) [0, 128, 128]
  expectEq "the control block's hex length" (input.witness.getLast!.length) 130
  expect (pays (← h.transaction txid) (← h.scriptPubKey destination) payment)
    "the spend does not pay the destination the reviewed amount"
  shot "13-multisig-sent"
  h.mine 1
  let spentAt ← h.height
  need "broadcastConfirmed" 90 "the receipt did not see it confirm"

  -- one Transactions row for the spend, named with the account
  tap (.tab "Wallet")
  waitForBalance (funding - payment - fee) "the account's change" "multisigBalance"
  backToWalletList
  need s!"historyPayment-{txid}" 30 "the spend is missing from Transactions"
  needScroll s!"historyPayment-{txid}" "the spend's row cannot be scrolled to"
  need s!"paymentAccount-{txid}" 0 "the row does not name the account"
  shot "13b-multisig-transactions"
  needScroll s!"multisigAccount-{account}" "the account is not listed"
  tap s!"multisigAccount-{account}"

  -- past the delay, the phone alone spends the change on the recovery path. The Core signers are done, and the
  -- app is in the background while the node mines, so it next syncs to the new tip in one go.
  for signer in [core, second] do discard <| h.cli #["unloadwallet", signer.wallet]
  let height ← h.height
  if height < spentAt + recoveryBlocks - 1 then
    home
    h.mineElsewhere (spentAt + recoveryBlocks - 1 - height)
    activate
  -- the account page: no payment form of its own, Send from this account, Paste a PSBT, Share with co-signers
  needScroll "multisigPastePSBTButton" "the account page has no Paste a PSBT"
  expect (!(← exists? "multisigAddressField")) "the account page still has a payment form"
  shot "13a-account-page"
  needScroll "multisigShareButton" "the account page has no Share with co-signers"
  shot "13a-account-page-share"
  tap "multisigSendButton"
  need "sendSourceNote" 10 "Send does not start from the account"
  tap "multisigPathPicker"
  need (.button "Recovery path") 10 "Send offers no recovery path for the account"
  tap (.button "Recovery path")
  need "sendRecoveryNote" 10 "no recovery caption"
  shot "13c-send-recovery-path"
  let recoveryDestination ← h.bankAddress
  r.clipboard recoveryDestination
  tap "pasteDestinationButton"
  type "amountField" (toString recoveryPayment)
  -- the phone may not have seen the last blocks yet: review until the coin unlocks
  waitUntil 120 "the recovery spend was not reviewed" (every := 1) do
    if ← exists? "sendButton" then return true
    let review ← state "reviewButton"
    if review.present && review.enabled && (← scrollTo "reviewButton") then tap "reviewButton"
    exists? "sendButton" 0.5
  expectEq "the reviewed spend path" (← text "reviewSpendPath") "Recovery path"
  needScroll "sendButton" "no Sign and continue"
  expectEq "the review's button" (← text "sendButton") "Sign and continue"
  tap "sendButton"
  -- Sign and continue signed every leaf this phone is on: the recovery leaf's one signature is in
  need "multisigRecoverySignatureCount" 90 "the collection step shows no recovery count"
  countIs "multisigRecoverySignatureCount" "1 of 1" 30 "after the phone's recovery signature"
  let before ← h.mempool
  tap "multisigBroadcastButton"
  need "broadcastPending" 30 "the recovery receipt did not open"
  let recovered ← newMempoolTransaction h before 30 "Core did not accept the recovery spend"
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
device behind the app's real APDU program): pair it under Settings → Signers (its key filed, nothing
registered), build the account with it as a member (the Ledger registers it), have it derive the receive
address, which must also be Core's, fund the account from the wallet (one Transactions row, a transfer), pay
from it on the Send tab (Sign and continue, then the Ledger in the collection step), and Core must accept a
witness carrying both signatures; the receipt sees it confirm and Transactions shows it once, named with the
account. -/
def ledgerPairVerifySpend : Journey := ⟨"ledgerPairVerifySpend", do
  let r ← Run.new "ledger"
  let h := r.host
  -- Advanced mode from launch: the multisig journey turns it on through its alert
  r.launch "ledger" [("WINNOW_E2E_LEDGER", ← randomHex 16), ("WINNOW_E2E_ADVANCED", "1")]
  createWallet
  let walletAddress ← receiveAddress
  tap "closeReceiveButton"
  discard <| h.fund walletAddress (2 * funding)
  waitForBalance (2 * funding) "the wallet did not find its funding"

  -- Settings → Signers → Pair a Ledger
  tap (.tab "Settings")
  tap "signersButton"
  tap "signersPairLedgerButton"
  type "ledgerNameField" "Nano X"
  tap "ledgerPairButton"
  need (.button "Nano X") 60 "pairing did not file the Ledger"
  shot "19-signers-paired"

  -- the builder: this phone and the Ledger, any 2 of 2; the Ledger approves it
  tap (.tab "Wallet")
  tap "multisigBuildButton"
  type "multisigBuildNameField" "Ledger savings"
  tap "multisigBuildAddMemberButton"
  need (.button "Nano X") 10 "the picker does not offer the Ledger"
  tap (.button "Nano X")
  need (.beginning "Members · 2") 10 "the Ledger was not added"
  tap "multisigBuildCreateButton"
  need "multisigBuildLedgerRegistered" 60 "the Ledger did not register the account"
  needScroll "multisigCreatedDescriptor" "the builder shows no descriptor"
  let descriptor ← text "multisigCreatedDescriptor"
  let account := accountID descriptor
  tap "multisigOpenAccountButton"
  waitFor "multisigPolicy" 20
  expectEq "the account's policy" (← text "multisigPolicy") "2 of 2"

  -- the Ledger derives the address the phone shows, and so does Core from the account's descriptor
  waitFor "multisigReceiveAddress" 20
  let address ← text "multisigReceiveAddress"
  tap "ledgerVerifyButton"
  need "ledgerVerifyResult" 60 "the Ledger did not answer"
  let verified ← text "ledgerVerifyResult"
  expect (verified.startsWith "The Ledger derived this same address.") verified
  -- the page shares its descriptor rather than printing it; the builder showed the same one
  needScroll "multisigShareButton" "the account page has no Share with co-signers"
  expectEq "the account's first address (Core's)" (← h.deriveAddress descriptor 0) address
  shot "20-ledger-verified"

  -- the wallet pays the account: Send, From the wallet
  tap (.tab "Send")
  tap "sendFromWallet"
  r.clipboard address
  tap "pasteDestinationButton"
  type "amountField" (toString funding)
  tap "reviewButton"
  need "sendButton" 30 "the wallet's review did not open"
  let beforeFunding ← h.mempool
  tap "sendButton"
  let fundingTx ← newMempoolTransaction h beforeFunding 60 "the wallet's payment to the account never reached the node"
  h.mine 1
  need "broadcastConfirmed" 90 "the transfer did not confirm"
  tap "newPaymentButton"
  tap (.tab "Wallet")
  waitForBalance funding "the account did not find the transfer" "multisigBalance"
  backToWalletList
  need s!"historyPayment-{fundingTx}" 30 "no Transactions row for the transfer"
  needScroll s!"historyPayment-{fundingTx}" "the transfer's row cannot be scrolled to"
  expectEq "the transfer's row (one row)" (← text s!"historyPayment-{fundingTx}") "Moved to Ledger savings"
  shot "20b-ledger-transfer-row"

  let destination ← h.bankAddress
  sendFromAccount r account destination payment "needs 2 of 2"
  countIs "multisigSignatureCount" "1 of 2" 60 "after the phone"
  tap "ledgerSignButton"
  countIs "multisigSignatureCount" "2 of 2" 60 "after the Ledger"
  shot "21-ledger-signed"

  let before ← h.mempool
  tap "multisigBroadcastButton"
  need "broadcastPending" 30 "the receipt did not open"
  let txid ← newMempoolTransaction h before 30 "Core did not accept the Ledger-signed payment"
  let input ← h.spendingInput txid
  expectEq "what the spend spends (the transfer)" input.txid fundingTx
  expectEq "witness items (two signatures, the leaf script and the control block)" input.witness.length 4
  expectEq "the phone's and the Ledger's signatures" (witnessSizes input.witness 2) [128, 128]
  h.mine 1
  need "broadcastConfirmed" 90 "the receipt did not see it confirm"
  expect ((← h.tipTransactions).contains txid) "the payment was not mined"
  shot "22-ledger-confirmed"
  -- one confirmed row, named with the account
  tap (.tab "Wallet")
  need s!"historyPayment-{txid}" 60 "the spend is missing from Transactions"
  needScroll s!"historyPayment-{txid}" "the spend's row cannot be scrolled to"
  need s!"paymentAccount-{txid}" 0 "the row does not name the account"
  shot "23-ledger-transactions"⟩

/-- The census list the build ships (the app's manifest bundles build/census/peers.json): Advanced mode's
Settings on mainnet show its date and count, not the sentence for a build without one; then the plain texts
(PORT.md, deliberate departures): Settings' Backup section, the backup file sheet, the iCloud sheet, the Wallet
tab's multisig section and Join. -/
def shippedCensus : Journey := ⟨"shippedCensus", do
  let r ← Run.new "census"
  r.launch "census" [("WINNOW_E2E_NETWORK", "mainnet"), ("WINNOW_E2E_ADVANCED", "1")]
  createWallet
  need (.tab "Settings") 15 "no Settings tab"
  tap (.tab "Settings")
  need "censusCatalogText" 20 "Settings show no census line"
  needScroll "censusCatalogText" "the census line cannot be scrolled to"
  let line ← text "censusCatalogText"
  need (.text "^Observed \\d{4}-\\d{2}-\\d{2}: \\d+ candidates\\.$") 0 s!"census line: {line}"
  let count := ((line.splitOn ": ")[1]?).bind digits
  expect (count.getD 0 > 100) s!"census line: {line}"
  shot "30-settings-census"

  need "exportBundleButton" 10 "no backup file button"
  needScroll "exportBundleButton" "the backup file button cannot be scrolled to"
  expectEq "the backup file button" (← text "exportBundleButton") "Save a backup file"
  need "cloudBackupRowStatus" 0 "the iCloud row shows no status"
  shot "31-settings-backup"
  tap "exportBundleButton"
  need "exportExplanation" 10 "the backup file sheet did not open"
  need (.nav "Backup file") 0 "the sheet is not titled Backup file"
  shot "32-backup-file-sheet"
  tap (.button "Close")
  waitFor "exportBundleButton" 10
  needScroll (.button "iCloud backup") "no iCloud backup row"
  tap (.button "iCloud backup")
  need "automaticCloudBackupToggle" 10 "the iCloud sheet did not open"
  shot "33-icloud-sheet"
  tap (.button "Close")
  tap (.tab "Wallet")
  need "multisigAddButton" 10 "no Join an account"
  needScroll "multisigAddButton" "Join an account cannot be scrolled to"
  expectEq "the Join button" (← text "multisigAddButton") "Join an account"
  expectEq "the Create button" (← text "multisigBuildButton") "Create an account"
  shot "34-wallet-multisig"
  tap "multisigAddButton"
  need (.nav "Join an account") 10 "Join is not titled Join an account"
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
  let address ← receiveAddress
  tap "closeReceiveButton"
  discard <| h.fund address funding
  waitForBalance funding "the wallet did not find its funding"

  r.clipboard code
  tap "openSendButton"
  tap "pasteDestinationButton"
  type "amountField" (toString silentPayment)
  tap "reviewButton"
  need "sendButton" 30 "the silent payment review did not open"
  expectEq "the reviewed destination" (← text "reviewDestination") code
  need "silentPaymentNote" 0 "the review does not say the address is derived"
  expectEq "the reviewed amount" (← amount "reviewAmount") (some silentPayment)
  shot "40-silent-review"

  let before ← h.mempool
  tap "sendButton"
  let txid ← newMempoolTransaction h before 60 "the node never received the silent payment"
  let expected ← h.silentPaymentExpectedScript txid
  let some paid := (outputs (← h.transaction txid)).find? (fun o => o.script == expected && o.sats == silentPayment)
    | failure s!"the transaction pays no output the code's holder would find ({expected})"
  need "derivedOutputAddress" 20 "the receipt does not show where the code was paid"
  needScroll "derivedOutputAddress" "the derived address cannot be scrolled to"
  expectEq "the receipt's derived address" (← text "derivedOutputAddress") paid.address
  h.mine 1
  need "broadcastConfirmed" 90 "the receipt did not see it confirm"
  shot "41-silent-confirmed"⟩

def all : List Journey :=
  [createReceiveSendConfirm, multisigTwoOfThreeWithRecovery, ledgerPairVerifySpend, shippedCensus, silentPaymentSend]

end WinnowJourneys

/-- The journeys, and the app itself for the headless driver (`LEANNATIVE_DRIVER=wire`: scripts/wire-journeys). -/
def main (args : List String) : IO UInt32 :=
  LeanNative.Journey.main WinnowJourneys.all args (wire := some (LeanNative.Journey.Wire.app WinnowApp.app))
