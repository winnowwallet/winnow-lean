import WinnowApp.Real
open Lean Winnow Winnow.IO Winnow.Net WinnowApp

/-! `backend-test`: `Backend.real` end to end against a disposable regtest bitcoind, through the
Backend fields only (plus the diagnostics handle for "no loop survives a stop").

The node is started as `Lean/IOTest.lean` does (temp datadir, random free ports, compact-filter
serving) and killed by PID at the end, also on failure. The backend runs with an in-memory key store
and `curlFetch`, the app's settings on the regtest network with the node as the manual peer.

create → start networking → sync to tip → receive address → fund + mine → syncNow → balance and
history → fee rate + preview → send → the node's mempool → mine → confirmed, balance arithmetic →
a second send, fee bump (RBF accepted by the node) → mine → a 2-of-2 multisig account with a test key
(funded, credited by the sync, a spend created, signed by the phone and by the other key in Lean,
combined, finalized, broadcast, confirmed) → export (carrying the account) → import into a fresh
directory (same balance, the account restored) → stop networking (no loop, no peer, no file change while blocks arrive) → reopen from
disk → delete. One `ok`/`FAIL` line per check; the exit code is the verdict. -/

/-- A Bitcoin Core binary: `$WINNOW_BITCOIND` / `$WINNOW_BITCOIN_CLI`, else Homebrew's, else the PATH. -/
def findTool (env name : String) : IO String := do
  if let some path := (← IO.getEnv env) then return path
  for dir in ["/opt/homebrew/bin", "/usr/local/bin"] do
    if ← System.FilePath.pathExists s!"{dir}/{name}" then return s!"{dir}/{name}"
  return name

initialize bitcoind : String ← findTool "WINNOW_BITCOIND" "bitcoind"
initialize bitcoinCli : String ← findTool "WINNOW_BITCOIN_CLI" "bitcoin-cli"

initialize failures : IO.Ref (Array String) ← IO.mkRef #[]
/-- Every `Deps.journal` line of the run: which backend (A, B, C), the event, its fields. -/
initialize journalEvents : IO.Ref (Array (String × String × List (String × String))) ← IO.mkRef #[]
initialize passes : IO.Ref Nat ← IO.mkRef 0

def say (s : String) : IO Unit := do IO.println s; (← IO.getStdout).flush

def check (name : String) (cond : Bool) (detail : String := "") : IO Unit := do
  if cond then
    passes.modify (· + 1)
    say s!"  ok   {name}{if detail.isEmpty then "" else " — " ++ detail}"
  else
    failures.modify (·.push name)
    say s!"  FAIL {name}{if detail.isEmpty then "" else " — " ++ detail}"

/-! ## The node (as IOTest) -/

structure Node where
  datadir : String
  p2p : UInt16
  rpc : UInt16
  pid : UInt32

def Node.cli (n : Node) (args : Array String) : IO String := do
  let out ← IO.Process.output { cmd := bitcoinCli, args := #["-regtest", s!"-datadir={n.datadir}", s!"-rpcport={n.rpc}"] ++ args }
  if out.exitCode != 0 then throw (IO.userError s!"bitcoin-cli {args}: {out.stderr.trimAscii}")
  return out.stdout.trimAscii.toString

def Node.wallet (n : Node) (args : Array String) : IO String := n.cli (#["-rpcwallet=w"] ++ args)

def Node.json (n : Node) (args : Array String) : IO Json := do
  match Json.parse (← n.cli args) with
  | .ok j => return j
  | .error e => throw (IO.userError s!"json {args}: {e}")

def Node.height (n : Node) : IO Nat := do return (← n.cli #["getblockcount"]).toNat!
def Node.mine (n : Node) (count : Nat) (addr : String) : IO Unit := do
  let mut left := count
  while left > 0 do
    let k := min left 500
    discard <| n.cli #["generatetoaddress", toString k, addr]
    left := left - k

def killPid (pid : UInt32) (signal : String := "-TERM") : IO Unit := do
  discard <| IO.Process.output { cmd := "kill", args := #[signal, toString pid] }

def startNode (dir : String) : IO Node := do
  for attempt in [0:5] do
    let r ← randomU64
    let p2p := (30000 + r.toNat % 25000).toUInt16
    let rpc := p2p + 1
    let datadir := s!"{dir}/node{attempt}"
    IO.FS.createDirAll datadir
    let child ← IO.Process.spawn {
      cmd := bitcoind
      args := #["-regtest", s!"-datadir={datadir}", s!"-port={p2p}", s!"-rpcport={rpc}", "-bind=127.0.0.1",
        "-listen=1", "-server=1", "-blockfilterindex=1", "-peerblockfilters=1", "-fallbackfee=0.0002",
        "-printtoconsole=0", "-dnsseed=0", "-discover=0", "-listenonion=0", "-whitelist=noban@127.0.0.1"]
      stdout := .null, stderr := .null, stdin := .null }
    let n : Node := { datadir, p2p, rpc, pid := child.pid }
    let mut ready := false
    for _ in [0:100] do
      IO.sleep 200
      if (← child.tryWait).isSome then break
      match ← (n.cli #["getblockchaininfo"]).toBaseIO with
      | .ok _ => ready := true; break
      | .error _ => pure ()
    if ready then return n
    killPid child.pid "-KILL"
  throw (IO.userError "bitcoind did not start")

def Node.waitFilterIndex (n : Node) : IO Unit := do
  for _ in [0:300] do
    let tip ← n.height
    let info ← n.json #["getindexinfo"]
    match info.getObjVal? "basic block filter index" with
    | .ok idx =>
      let synced := (idx.getObjValAs? Bool "synced").toOption.getD false
      let best := (idx.getObjValAs? Nat "best_block_height").toOption.getD 0
      if synced && best == tip then return
    | .error _ => pure ()
    IO.sleep 100
  throw (IO.userError "filter index did not catch up")

def Node.mempool (n : Node) : IO (Array String) := do
  match ← n.json #["getrawmempool"] with
  | .arr xs => return xs.filterMap fun | .str s => some s | _ => none
  | _ => return #[]

def Node.winnowPeers (n : Node) : IO Nat := do
  match ← n.json #["getpeerinfo"] with
  | .arr xs => return (xs.filter fun p => (p.getObjValAs? String "subver").toOption == some "/winnow:0.1/").size
  | _ => return 0

def waitUntil (ms : Nat) (cond : IO Bool) : IO Bool := do
  let deadline := (← IO.monoMsNow) + ms
  while (← IO.monoMsNow) < deadline do
    if ← cond then return true
    IO.sleep 250
  cond

/-! ## The flow -/

def regtestSettings (n : Node) : Settings :=
  { network := .regtest, regtest := { manualPeers := [s!"127.0.0.1:{n.p2p}"] } }

def deps (keys : IO.Ref Keys.InMemorySecrets) (tag : String := "A") : Real.Deps :=
  { keyStore := inMemoryKeyStore keys, fetch := curlFetch "/usr/bin/curl", peerCount := 1,
    journal := fun name fields => journalEvents.modify (·.push (tag, name, fields)) }

/-! ## The journal (test mode's `story-events.jsonl`, captured) -/

def sortedKeys (fields : List (String × String)) : List String := ((fields.map (·.1)).toArray.qsort (· < ·)).toList

def journaled (name : String) : IO (Array (String × List (String × String))) := do
  return (← journalEvents.get).filterMap fun (tag, n, f) => if n == name then some (tag, f) else none

def field (f : List (String × String)) (k : String) : String := (f.lookup k).getD "<missing>"

/-- At least one `name` event, every one of them with exactly `keys`, and one satisfying `ok`. -/
def checkJournal (name : String) (keys : List String) (ok : List (String × String) → Bool := fun _ => true)
    (what : String := "") : IO Unit := do
  let es ← journaled name
  let want := (keys.toArray.qsort (· < ·)).toList
  let shaped := es.all fun (_, f) => sortedKeys f == want
  check s!"journal: {name} {keys}{if what.isEmpty then "" else " — " ++ what}" (!es.isEmpty && shaped && es.any (ok ·.2))
    s!"{es.size} event(s){match es.find? (fun (_, f) => sortedKeys f != want) with
      | some (_, f) => s!", one with {sortedKeys f}" | none => ""}"

/-- A journaled `raw` decodes to the transaction the journal names. -/
def rawIsTxid (raw txid : String) : Bool :=
  match Winnow.ofHex? raw with
  | some bytes => match Transaction.decode bytes with
    | .ok tx => Winnow.displayHex tx.txid == txid
    | .error _ => false
  | none => false

def attempt {α} (x : IO α) : IO (Except String α) := do
  try return .ok (← x) catch e => return .error (toString e)

/-- syncNow until `cond` holds of the snapshot (the loop may hold the pass; syncNow then returns at once). -/
def syncUntil (b : Backend) (ms : Nat) (cond : Status → SyncPhase → Bool) : IO (Status × SyncPhase) := do
  let deadline := (← IO.monoMsNow) + ms
  repeat
    b.syncNow
    let (s, p) ← b.snapshot
    if cond s p || (← IO.monoMsNow) ≥ deadline then return (s, p)
    IO.sleep 500
  b.snapshot

def history? (s : Status) (txid : String) : Option HistoryItem := s.history.find? (·.txid == txid)

def showPhase : SyncPhase → String
  | .idle => "idle" | .connecting c t => s!"connecting {c}/{t}" | .headers s e => s!"headers {s}/{e}"
  | .filters s t => s!"filters {s}/{t}" | .synced => "synced" | .peerDiscoveryFailed => "peerDiscoveryFailed"


/-! ## A multisig account end to end -/

structure MultisigResult where
  id : String
  balance : Int
  txid : String
  firstAddress : String

/-- `[fp/86'/1'/0']tpub…/<0;1>/*` of a master from 16 repeated bytes (TestKeys), and the master. -/
def testSigner (entropyByte : UInt8) : IO (Keys.HDKey × String) := do
  let some words := (Keys.BIP39.mnemonic (ByteArray.mk (Array.replicate 16 entropyByte))).toOption
    | throw (IO.userError "mnemonic")
  let some master := (Keys.HDKey.ofSeed (Keys.BIP39.seed words)).toOption | throw (IO.userError "master")
  let some account := (master.derived "m/86'/1'/0'").toOption | throw (IO.userError "account")
  return (master, s!"[{Descriptor.hex8 master.fingerprint}/86'/1'/0']{account.neutered.serialized .testnet}/<0;1>/*")

def multisigAccount? (b : Backend) (id : String) : IO (Option MultisigInfo) := do
  return (← b.multisigOverview).accounts.find? (·.id == id)

/-- Create a 2-of-2 with a test key, receive to it, see the coin credited by the sync loop, create the
spend, sign with the phone and with the other key in Lean, combine, finalize and broadcast, confirm. -/
def multisigFlow (n : Node) (a : Backend) (msA : Real.MultisigApp) (mineAddr : String) : IO MultisigResult := do
  let (otherMaster, otherKey) ← testSigner 0xB2
  let phoneKey := (← a.multisigOverview).keyExpression.getD ""
  let members := [([phoneKey], none), ([otherKey], none)]
  let refusedSimple ← attempt (a.createMultisigAccount false "Shared" 2 members none)
  check "multisig: the builder is Advanced mode only" (refusedSimple matches .error _)
  let (id, descriptor, _) ← a.createMultisigAccount true "Shared" 2 members none
  let account ← match MultisigAccount.parse descriptor .regtest with
    | .ok acc => pure acc
    | .error e => throw (IO.userError s!"account: {e.name}")
  let some info ← multisigAccount? a id | throw (IO.userError "the account is not listed")
  check "multisig: 2 of 2, listed with no coins" (info.policy == some "2 of 2" && info.balance == 0 && info.coins.isEmpty)
  let some address := info.receiveAddress | throw (IO.userError "no receive address")
  check "multisig: the receive address is the descriptor's first" ((account.address 0).toOption == some address && address.startsWith "bcrt1p")
  let again ← a.createMultisigAccount true "Shared" 2 members none
  check "multisig: building the same account again returns it" (again.1 == id && (← a.multisigOverview).accounts.length == 1)
  let check1 ← attempt (a.checkMultisigDescriptor descriptor)
  check "multisig: the descriptor checks as 2 of 2 for this phone" (match check1 with
    | .ok c => c.policy == "2 of 2" && c.firstAddress == some address | .error _ => false)
  -- 1. Receive.
  let fundTxid ← n.wallet #["sendtoaddress", address, "0.5"]
  discard <| waitUntil 20_000 (do return (← n.mempool).contains fundTxid)
  n.mine 1 mineAddr
  let fundHeight ← n.height
  n.waitFilterIndex
  let credited ← waitUntil 90_000 (do
    a.syncNow
    return ((← multisigAccount? a id).map (·.balance)) == some 50_000_000)
  let some funded ← multisigAccount? a id | throw (IO.userError "account gone")
  check "multisig: the sync credits the account's coin" (credited && funded.coins.length == 1)
    s!"{funded.balance}, {funded.coins.map (·.line)}"
  check "multisig: the coin row" (funded.coins.any fun c => c.amount == 50_000_000 &&
    (c.line.splitOn s!"receive 0 · block {fundHeight}").length > 1)
  check "multisig: the receive frontier moved past the paid address" (funded.nextReceiveIndex == 1)
  let (sw, _) ← a.snapshot
  check "multisig: the account's coin is not the wallet's" (sw.history.all (·.txid != fundTxid))
  -- 2. Send, From: the account (upstream #259): the review is the PSBT this phone built.
  let dest ← n.wallet #["getnewaddress"]
  let inputs : SendInputs := { destination := dest, amount := "20000000", network := .regtest, accountID := some id }
  let preview ← a.previewSend inputs
  check "send tab: the review names the account" ((preview.account.map fun x => (x.name, x.threshold, x.signerCount)) ==
    some ("Shared", 2, 2) && preview.amount == 20_000_000 && preview.inputCount == 1 &&
    preview.change == some (50_000_000 - 20_000_000 - preview.fee))
  let silent ← attempt (a.previewSend { inputs with destination := "tsp1qqnonsense" })
  check "send tab: no silent payment code from an account" (match silent with
    | .error e => e == Real.silentPaymentUnsupportedText | .ok _ => false)
  -- 3. Sign and continue: this phone's signature, the draft filed (BIP174 v0) and listed on top.
  discard <| a.signAndDraft true inputs preview
  let some drafted ← multisigAccount? a id | throw (IO.userError "account gone")
  let some d := drafted.draft | throw (IO.userError "no draft")
  let some screen := d.screen | throw (IO.userError s!"review: {d.reviewError}")
  check "send tab: the draft reviews: pays the node, change back to the account"
    (screen.outputs.length == 2 && screen.outputs.any (fun o => !o.owned && o.address == dest && o.amount == 20_000_000) &&
     screen.outputs.any (·.owned) && screen.inputTotal == 50_000_000 && screen.fee == preview.fee)
  check "send tab: this phone's signature verifies" (screen.signatures == [(false, 1, 2)] && screen.progress.signedHere)
  check "send tab: the shared text is BIP174 v0" (match PSBT.ofBase64 d.psbt with
    | .ok p => p.base64V0.toOption == some d.psbt | .error _ => false)
  let (sd, _) ← a.snapshot
  check "send tab: the draft row on top, 1 of 2" ((sd.payments.head?.map (·.source)) == some (.draft "Shared" "1 of 2"))
  let finalizeEarly ← attempt (a.broadcastDraft id)
  check "multisig: one signature cannot be finalized" (finalizeEarly matches .error _)
  -- the other signer signs its copy in Lean; this phone combines it into the draft
  let record ← Real.record msA id
  let unsigned ← match PSBT.ofBase64 d.psbt with
    | .ok p => pure p
    | .error _ => throw (IO.userError "psbt")
  let tip ← n.height
  let theirs ← match account.sign unsigned otherMaster record.utxos (Real.ownedCoordinates record) tip.toUInt32
      (← IO.getRandomBytes 32) with
    | .ok p => pure p
    | .error e => throw (IO.userError s!"other signer: {e.name}")
  let some theirText := theirs.base64V0.toOption | throw (IO.userError "v0")
  a.adoptDraft id theirText
  let some combined ← multisigAccount? a id | throw (IO.userError "account gone")
  check "multisig: combined, enough signatures verify" (((combined.draft.bind (·.screen)).map (·.progress.complete)) == some true &&
    ((combined.draft.bind (·.screen)).map (·.signatures)) == some [(false, 2, 2)])
  -- 4. Finalize and broadcast.
  let txid ← a.broadcastDraft id
  let inMempool ← waitUntil 20_000 (do return (← n.mempool).contains txid)
  check "multisig: the node's mempool holds the spend" inMempool txid
  let some pending ← multisigAccount? a id | throw (IO.userError "account gone")
  let change := 50_000_000 - 20_000_000 - (screen.fee : Int)
  check "multisig: the change waits as a pending coin" (pending.balance == change &&
    pending.coins.any fun c => (c.line.splitOn "change 0 · pending").length > 1) s!"{pending.balance} vs {change}"
  check "multisig: the draft retired, the spend in flight" (pending.draft.isNone && pending.inFlight == [txid])
  let (sp, _) ← a.snapshot
  check "send tab: the pending spend is one row named with the account" ((sp.payments.filter (·.item.txid == txid)).map
    (fun r => (r.source, r.item.height, r.item.fee)) == [(.account "Shared", 0, some (screen.fee : Int))])
  let again2 ← attempt (a.broadcastDraft id)
  check "multisig: a spent coin cannot be spent again" (again2 matches .error _)
  -- 5. Confirm.
  n.mine 1 mineAddr
  let spendHeight ← n.height
  n.waitFilterIndex
  let confirmed ← waitUntil 90_000 (do
    a.syncNow
    let r ← Real.record msA id
    return r.allUtxos.any fun u => u.spent.any (·.height == some spendHeight.toUInt32))
  let final ← Real.record msA id
  check "multisig: the spent coin is tombstoned at the confirming block" confirmed
  check "multisig: the change confirmed in the same block" (final.utxos.size == 1 &&
    final.utxos.all (·.height == spendHeight.toUInt32) && final.balance.toInt == change)
  let blockHash ← n.cli #["getblockhash", toString spendHeight]
  let blk ← n.json #["getblock", blockHash]
  check "multisig: the node's block holds the spend" ((blk.getObjValAs? (List String) "tx").toOption.any (·.contains txid))
  let (sc, _) ← a.snapshot
  check "send tab: confirmed in place, one row" ((sc.payments.filter (·.item.txid == txid)).map (fun r => (r.source, r.item.height)) ==
    [(.account "Shared", spendHeight)])
  -- 6. The wallet pays the account: one row, a transfer.
  let some to := (account.address 1).toOption | throw (IO.userError "address 1")
  let tIn : SendInputs := { destination := to, amount := "1000000", network := .regtest }
  let tp ← a.previewSend tIn
  let moved := (← a.sendPayment tIn tp).txid
  discard <| waitUntil 20_000 (do return (← n.mempool).contains moved)
  n.mine 1 mineAddr
  n.waitFilterIndex
  let landed ← waitUntil 90_000 (do
    a.syncNow
    return ((← multisigAccount? a id).map (·.balance)) == some (change + 1_000_000))
  check "transfer: the account received it" landed
  let (st, _) ← a.snapshot
  let rows := st.payments.filter (·.item.txid == moved)
  check "transfer: one row, wallet to account" (rows.map (·.source) == [.transfer "Wallet" "Shared" 1_000_000])
    s!"{repr (rows.map (·.source))}"
  check "transfer: the row carries the wallet's spend" (rows.all fun r => r.accountID.isNone && r.item.spent > 0)
  check "the headline sums the wallet and the account" (st.accountsBalance ≥ change + 1_000_000)
  return { id, balance := change + 1_000_000, txid, firstAddress := address }

/-- Pair a simulated Ledger (Settings → Signers), build the 2-of-2 of this phone and it and a 2-of-3 with
another key, the Ledger and a recovery path (the paired Ledger registers each),
verify an address of each on the Ledger, fund both, and spend from each with the phone's and the
Ledger's signatures. The two accounts' ids. -/
def ledgerFlow (n : Node) (a : Backend) (msA : Real.MultisigApp) (device : IO.Ref Ledger.Simulator) (mineAddr : String) :
    IO (Array String) := do
  let (_, otherKey) ← testSigner 0xB2
  let refusedSimple ← attempt (a.pairLedger false "Nano X")
  check "ledger: pairing is Advanced mode only" (refusedSimple matches .error _)
  let ledgerID ← a.pairLedger true "Nano X"
  let o ← a.multisigOverview
  let ledgerKeys := ((o.signers.find? (·.id == ledgerID)).map (·.keys)).getD []
  check "ledger: paired, nothing registered" ((← device.get).registeredNames.isEmpty && ledgerKeys.length == 1)
  let phoneKey := o.keyExpression.getD ""
  let (pair, _, _) ← a.createMultisigAccount true "Phone and Ledger" 2 [([phoneKey], none), (ledgerKeys, none)] none
  let (family, _, _) ← a.createMultisigAccount true "Family 2-of-3" 2
    [([phoneKey], none), ([otherKey], none), (ledgerKeys, none)] (some (.fewerSigners 1 4320))
  check "ledger: the Ledger approved both accounts by name"
    ((← device.get).registeredNames == #["Phone and Ledger", "Family 2-of-3"])
  let ids := #[pair, family]
  let mut funding : Array (String × MultisigAccount) := #[]
  for id in ids do
    let r ← Real.record msA id
    let account ← match MultisigAccount.parse r.descriptor .regtest with
      | .ok acc => pure acc
      | .error e => throw (IO.userError s!"account: {e.name}")
    check s!"ledger: {r.name} has its registration" (r.ledger.isSome)
    check s!"ledger: {r.name} is {account.threshold} of {account.signers.size}"
      ((account.threshold, account.signers.size) == (if id == pair then (2, 2) else (2, 3)))
    let shown ← a.verifyLedgerAddress true id 0
    check s!"ledger: the Ledger shows {r.name}'s first address" ((account.address 0).toOption == some shown) shown
    funding := funding.push (id, account)
  check "ledger: both addresses were on the Ledger's screen" ((← device.get).displayedAddresses.size == 2)
  -- Receive.
  let mut fundTxids : Array String := #[]
  for (_, account) in funding do
    let some address := (account.address 0).toOption | throw (IO.userError "address")
    fundTxids := fundTxids.push (← n.wallet #["sendtoaddress", address, "0.3"])
  discard <| waitUntil 20_000 (do
    let mp ← n.mempool
    return fundTxids.all mp.contains)
  n.mine 1 mineAddr
  n.waitFilterIndex
  let credited ← waitUntil 90_000 (do
    a.syncNow
    let o ← a.multisigOverview
    return ids.all fun id => (o.accounts.find? (·.id == id)).any (·.balance == 30_000_000))
  check "ledger: the sync credits both accounts" credited
  -- Spend from each: the Ledger signs, then the phone, then broadcast.
  let mut spends : Array (String × String) := #[]
  for id in ids do
    let dest ← n.wallet #["getnewaddress"]
    -- the account page's spend, filed as the draft; the Ledger signs it, then the phone (the collection step)
    a.createDraft id dest 10_000_000 2.0 false
    let screenOf : IO MultisigScreen := do
      let some info ← multisigAccount? a id | throw (IO.userError "account gone")
      let some d := info.draft | throw (IO.userError "no draft")
      let some sc := d.screen | throw (IO.userError s!"review: {d.reviewError}")
      return sc
    let s0 ← screenOf
    check s!"ledger {id}: the phone and the Ledger both still sign" (s0.progress.phoneUnsigned && s0.progress.ledgerUnsigned &&
      s0.progress.nextStep.startsWith "Add this phone's signature and the Ledger's")
    a.signDraftWithLedger true id
    let s1 ← screenOf
    check s!"ledger {id}: the Ledger's signature verifies" (s1.signatures == [(false, 1, 2)] && !s1.progress.ledgerUnsigned)
    a.signDraft id
    check s!"ledger {id}: complete" (← screenOf).progress.complete
    let txid ← a.broadcastDraft id
    spends := spends.push (id, txid)
  let inMempool ← waitUntil 20_000 (do
    let mp ← n.mempool
    return spends.all fun (_, t) => mp.contains t)
  check "ledger: the node's mempool holds both spends" inMempool
  n.mine 1 mineAddr
  let spendHeight ← n.height
  n.waitFilterIndex
  let confirmed ← waitUntil 90_000 (do
    a.syncNow
    let mut all := true
    for (id, txid) in spends do
      let r ← Real.record msA id
      unless r.allUtxos.any (fun u => u.spent.any (·.height == some spendHeight.toUInt32)) &&
          r.utxos.any (fun u => Winnow.displayHex u.txid == txid && u.height == spendHeight.toUInt32) do all := false
    return all)
  check "ledger: both spends confirmed, the coins tombstoned and the change confirmed" confirmed
  let blk ← n.json #["getblock", ← n.cli #["getblockhash", toString spendHeight]]
  check "ledger: the node's block holds both spends" ((blk.getObjValAs? (List String) "tx").toOption.any fun txs =>
    spends.all fun (_, t) => txs.contains t)
  return ids

/-- BIP352 receiving for one output (k = 0), written from the BIP's receiver side (upstream's
SilentPaymentTestReceiver): A = Σ the inputs' keys, input_hash over the smallest outpoint,
ecdh = (input_hash · b_scan) · A, P = B_spend + t_0·G. The app computed a · B_scan; the two scripts agree
only when its derivation is right. Prevouts come from the node's wallet `w`, which funded the coins. -/
def receiverScript (n : Node) (tx : Json) (scanSecret spendKey : ByteArray) : IO ByteArray := do
  let some vins := (tx.getObjValAs? (Array Json) "vin").toOption | throw (IO.userError "vin")
  let mut keys : Array Keys.Point := #[]
  let mut outpoints : Array ByteArray := #[]
  for v in vins do
    let txid := (v.getObjValAs? String "txid").toOption.getD ""
    let vout := (v.getObjValAs? Nat "vout").toOption.getD 0
    let funding ← n.json #["decoderawtransaction", (← n.json #["-rpcwallet=w", "gettransaction", txid]).getObjValD "hex" |>.getStr? |>.toOption |>.getD ""]
    let some outs := (funding.getObjValAs? (Array Json) "vout").toOption | throw (IO.userError "prevout")
    let script := ((outs[vout]!.getObjValD "scriptPubKey").getObjValAs? String "hex").toOption.getD ""
    let witness := ((v.getObjValAs? (List String) "txinwitness").toOption.getD []).filterMap ofHex?
    let scriptSig := (((v.getObjValD "scriptSig").getObjValAs? String "hex").toOption.bind ofHex?).getD .empty
    let vo := vout.toUInt32
    outpoints := outpoints.push (ByteArray.mk (ofHex? txid).get!.toList.reverse.toArray ++
      ByteArray.mk #[vo.toUInt8, (vo >>> 8).toUInt8, (vo >>> 16).toUInt8, (vo >>> 24).toUInt8])
    if let some key := Keys.SilentPaymentSending.eligiblePublicKey ((ofHex? script).getD .empty) scriptSig witness then
      keys := keys.push (← IO.ofExcept ((Keys.parsePublicKey key).mapError (·.name)))
  let sumA ← IO.ofExcept ((Keys.combine keys.toList).mapError (·.name))
  let smallest := outpoints.foldl (fun m o => if Keys.SilentPaymentSending.bytesLess o m then o else m) outpoints[0]!
  let inputHash := taggedHash "BIP0352/Inputs" (smallest ++ Keys.serializeCompressed sumA)
  let scalar := (Secp.fromBE inputHash * Secp.fromBE scanSecret) % Keys.groupN
  let shared ← IO.ofExcept ((Keys.publicMultiply sumA (Secp.toBE32 scalar)).mapError (·.name))
  let t0 := taggedHash "BIP0352/SharedSecret" (Keys.serializeCompressed shared ++ ByteArray.mk #[0, 0, 0, 0])
  let spend ← IO.ofExcept ((Keys.parsePublicKey spendKey).mapError (·.name))
  let p ← IO.ofExcept (((do Keys.combine [spend, ← Keys.pointOfSecret (Secp.fromBE t0)] : Keys.PK Keys.Point)).mapError (·.name))
  return ByteArray.mk #[0x51, 0x20] ++ Keys.xonlyBytes p

/-- The test receiver's keys: fixed, so the UI journey can ask for its code and its expected output. -/
def testScanSecret : ByteArray := Secp.toBE32 0x5ca1ab1e
def testSpendSecret : ByteArray := Secp.toBE32 0x5be17

def testReceiverCode : IO String := IO.ofExcept ((do
  let scan ← (Keys.publicKeyOf testScanSecret).mapError (·.name)
  let spend ← (Keys.publicKeyOf testSpendSecret).mapError (·.name)
  let a ← (SilentPaymentAddress.make scan spend "tsp").mapError (·.name)
  a.encoded.mapError (·.name) : Except String String))

def testReceiverScript (n : Node) (tx : Json) : IO ByteArray := do
  receiverScript n tx testScanSecret (← IO.ofExcept ((Keys.publicKeyOf testSpendSecret).mapError (·.name)))

/-- 2b and 2c of the flow (its own definition: the flow's `do` block is at Lean's recursion limit). -/
def routingAndBackground (a : Backend) (envA : Real.Env) (n : Node) (settings : Settings) (mineAddr : String) : IO Unit := do
  -- 2b. Peer routing (upstream #181, #190): Manual with only a Tor gateway never dials the clearnet node;
  -- Direct only and Automatic (no gateway answers here) reach it again.
  let torGateway : Net.PeerEndpoint := { host := "127.0.0.1", port := 9 }
  let torManual : Winnow.IO.PeerGatewayConfiguration := { networks := [.tor], torProxy := some torGateway }
  a.reconnect { settings with peerGatewaySettings := { mode := "manual", manual := torManual } }
  IO.sleep 3_000
  let (sTor, _) ← a.snapshot
  check "Manual Tor only: the clearnet node is never dialled" (sTor.peerCount == 0 && sTor.activeGateways == torManual)
    s!"peers {sTor.peerCount}"
  check "Manual Tor only: Simple mode says private through Tor"
    (PeerRoutingState.current "manual" sTor.activeGateways sTor.discoveringGateways == .overlay true false)
  a.reconnect { settings with peerGatewaySettings := { mode := "direct" } }
  let (sDirect, _) ← syncUntil a 30_000 fun s _ => s.peerCount > 0
  check "Direct only: the node is reached" (sDirect.peerCount > 0 && sDirect.activeGateways == {})
  a.reconnect settings
  let (sAuto, _) ← syncUntil a 30_000 fun s p => s.peerCount > 0 && p == .synced
  check "Automatic with no gateway answering: clearnet, and the banner says so"
    (sAuto.peerCount > 0 && PeerRoutingState.current "automatic" sAuto.activeGateways sAuto.discoveringGateways == .direct true)
  -- 2c. A background check (upstream #192): with the scene in the background, one bounded scan reaches the
  -- node's new tip through the same routing, then nothing keeps running.
  a.stopNetworking
  n.mine 1 mineAddr
  n.waitFilterIndex
  let tip2 ← n.height
  let complete ← a.runBackgroundSync settings
  let (sBg, _) ← a.snapshot
  check "background check: reaches the new tip" (complete && sBg.nextScanHeight == tip2 + 1)
    s!"complete {complete}, next scan {sBg.nextScanHeight}, tip {tip2}"
  check "background check: networking torn down, the check recorded"
    (sBg.peerCount == 0 && sBg.lastCheckedAgo == some "under a minute" &&
     (← waitUntil 5_000 do return (← envA.diagnostics).liveLoops == 0))
  a.startNetworking settings
  check "background check: refused while the scene is active" (!(← a.runBackgroundSync settings))

set_option maxRecDepth 4096 in
def flow (dir : String) (n : Node) : IO Unit := do
  say s!"node: bitcoind regtest pid {n.pid}, p2p {n.p2p}"
  discard <| n.cli #["createwallet", "w"]
  let mineAddr ← n.wallet #["getnewaddress"]
  n.mine 101 mineAddr
  n.waitFilterIndex
  let settings := regtestSettings n
  let keysA ← IO.mkRef ({} : Keys.InMemorySecrets)
  -- the phone's Ledger: the simulated device, seeded from 0xC3 (`Tests/Support/TestKeys.swift`'s third master)
  let (ledgerMaster, _) ← testSigner 0xC3
  let device ← IO.mkRef (Ledger.Simulator.new ledgerMaster .regtest)
  let (a, envA, msA) ← Backend.realWithMultisig (deps keysA) (Real.simulatedLedger device)
  let dirA := s!"{dir}/A/BTCSwift/regtest"
  IO.FS.createDirAll dirA
  -- 1. Boot with no wallet, networking, create.
  let boot ← a.openWallet .regtest dirA
  check "openWallet on an empty directory is missing" (boot matches .missing)
  a.startNetworking settings
  let walletID ← a.createWallet .regtest dirA
  let words ← a.revealMnemonic
  check "createWallet stores a wallet with 12 recovery words" (words.length == 12) s!"{words.length} words"
  let walletFile ← (System.FilePath.mk dirA / "wallet.json").pathExists
  check "wallet.json written, secret in the key store" (walletFile && (← keysA.get).size == 1)
  -- upstream 4228c6b: no phrase checklist; a new wallet, and one an earlier build left unfinished, open ready
  let readyBoot ← a.openWallet .regtest dirA
  check "a created wallet opens ready, without a phrase checklist" (readyBoot matches .opened _)
  let legacyFlag := System.FilePath.mk dirA / s!"backup-pending.{walletID}"
  IO.FS.writeFile legacyFlag ""
  let legacyBoot ← a.openWallet .regtest dirA
  check "a legacy unfinished checklist opens ready and is cleared" ((legacyBoot matches .opened _) && !(← legacyFlag.pathExists))
  a.startNetworking settings
  -- 2. Sync to the tip.
  let tip ← n.height
  let (s0, p0) ← syncUntil a 90_000 fun s p => s.tipHeight == tip && s.nextScanHeight == tip + 1 && p == .synced
  check "sync reaches the node's tip" (s0.tipHeight == tip && s0.nextScanHeight == tip + 1)
    s!"tip {s0.tipHeight}/{tip}, next scan {s0.nextScanHeight}, peers {s0.peerCount}, error {s0.lastSyncError}"
  check "phase is synced" (p0 == .synced) (showPhase p0)
  -- Core sends its (bucketed) relay floor as BIP133 feefilter, in sat/kvB: the app's milli-sat/vB.
  check "fee floor from the peer's feefilter" (match s0.feeFloorMilli with | some f => 0 < f && f ≤ 1000 | none => false)
    s!"{s0.feeFloorMilli}"
  routingAndBackground a envA n settings mineAddr
  -- 3. Receive and fund.
  let addr ← a.receiveAddress false
  check "receive address is a regtest taproot address" (addr.startsWith "bcrt1p") addr
  let again ← a.receiveAddress false
  check "the current receive address is peeked, not advanced" (again == addr)
  let fundTxid ← n.wallet #["sendtoaddress", addr, "1.0"]
  n.mine 1 mineAddr
  let fundHeight ← n.height
  n.waitFilterIndex
  let (s1, _) ← syncUntil a 60_000 fun s _ => s.balance == 100_000_000
  check "balance after funding" (s1.balance == 100_000_000 && s1.utxoCount == 1) s!"{s1.balance} sat, {s1.utxoCount} coin(s), error {s1.lastSyncError}"
  let fundRow := history? s1 fundTxid
  check "history has the funding payment, confirmed" (match fundRow with
    | some h => h.height == fundHeight && h.received == 100_000_000 && h.spent == 0
    | none => false) s!"{fundRow.map (·.height)}"
  check "history row carries its decoded outputs" (match fundRow.bind (·.outputs) with
    | some outs => outs.any fun o => o.address == some addr && o.amount == 100_000_000 && o.ownedByWallet
    | none => false)
  let fresh ← a.receiveAddress true
  check "a fresh receive address moves past a used one" (fresh != addr && fresh.startsWith "bcrt1p")
  -- 4. Fee rate and preview.
  let rate ← a.resolveFeeRate 1 none
  check "resolveFeeRate: the medium preset (no observed rates), above the floor" (rate == 5000) s!"{rate} milli-sat/vB"
  let dest ← n.wallet #["getnewaddress"]
  let amount : Nat := 25_000_000
  let inputs : SendInputs := { destination := dest, amount := toString amount, network := .regtest }
  let p ← a.previewSend inputs
  check "previewSend: amount, fee, one input, change" (p.amount == amount && p.fee > 0 && p.inputCount == 1 &&
    p.change == some (100_000_000 - amount - p.fee) && p.feeRateMilli == 5000) s!"fee {p.fee}, change {p.change}"
  check "previewSend: synced, so the locktime does not lag" (!p.locktimeLagsTip)
  -- the node's BIP133 feefilter, as the seat majority of the one configured seat (bitcoind rounds its floor)
  let (sFloor, _) ← a.snapshot
  check "fee floor: the node's feefilter, as the seat majority" (sFloor.feeFloorMilli.any (· > 0)) s!"{sFloor.feeFloorMilli}"
  -- A summary the review never produced is refused.
  let forged ← attempt (a.sendPayment inputs { p with fee := p.fee + 1 })
  check "sendPayment refuses a summary that was not reviewed" (match forged with
    | .error e => e == "The available coins, fee, or change changed. Review the payment again before signing." | _ => false)
  -- 5. Send.
  let txid := (← a.sendPayment inputs p).txid
  let inMempool ← waitUntil 20_000 (do return (← n.mempool).contains txid)
  check "sendPayment: the node's mempool holds the txid" inMempool txid
  let raw ← a.rawTransactionHex txid
  check "rawTransactionHex while pending" raw.isSome
  let (s2, _) ← a.snapshot
  check "pending send in history at height 0" (match history? s2 txid with
    | some h => h.height == 0 && h.fee == some p.fee | none => false)
  n.mine 1 mineAddr
  let sendHeight ← n.height
  n.waitFilterIndex
  let expected : Int := 100_000_000 - amount - p.fee
  let (s3, _) ← syncUntil a 60_000 fun s _ => (history? s txid).any (·.height > 0)
  check "send confirmed in history" ((history? s3 txid).any (·.height == sendHeight)) s!"{(history? s3 txid).map (·.height)}"
  check "balance = previous − amount − fee" (s3.balance == expected) s!"{s3.balance} vs {expected}"
  check "relay entry gone once confirmed" ((← a.rawTransactionHex txid).isNone)
  -- 6. Fee bump an unconfirmed send.
  let dest2 ← n.wallet #["getnewaddress"]
  let inputs2 : SendInputs := { destination := dest2, amount := "10000000", network := .regtest }
  let p2 ← a.previewSend inputs2
  let txid2 := (← a.sendPayment inputs2 p2).txid
  discard <| waitUntil 20_000 (do return (← n.mempool).contains txid2)
  let (s4, _) ← a.snapshot
  check "the unconfirmed send is fee-bumpable" (s4.feeBumpable.contains txid2)
  let (current, _) ← a.pendingFeeRate txid2
  check "pendingFeeRate of the send" (current ≥ 4900 && current ≤ 5100) s!"{current}"
  let bp ← a.previewFeeBump txid2 (current + 5000)
  check "previewFeeBump: a higher rate and fee" (bp.fee > p2.fee && bp.feeRateMilli > current) s!"fee {bp.fee}, rate {bp.feeRateMilli}"
  let replacement ← match ← attempt (a.bumpFee txid2 bp) with
    | .ok r => pure r
    | .error e => check "bumpFee" false e; pure ""
  let replaced ← waitUntil 20_000 (do
    let mp ← n.mempool
    return mp.contains replacement && !mp.contains txid2)
  check "bumpFee: the node accepted the replacement and dropped the original" (replacement != "" && replaced) replacement
  let relayed ← IO.mkRef (#[] : Array String)
  a.watchRelay replacement fun e => relayed.modify (·.push (match e with
    | .announced k => s!"announced {k}" | .requested p => s!"requested {p}" | .echoed p => s!"echoed {p}"
    | .feeFloorExceeded => "feeFloorExceeded" | .confirmed => "confirmed"))
  let (s5, _) ← a.snapshot
  check "history marks the original replaced" ((history? s5 txid2).any (·.replacedBy == some replacement))
  n.mine 1 mineAddr
  n.waitFilterIndex
  let expected2 : Int := expected - 10_000_000 - bp.fee
  let (s6, _) ← syncUntil a 60_000 fun s _ => (history? s replacement).any (·.height > 0)
  check "replacement confirmed; balance = previous − amount − replacement fee" (s6.balance == expected2 &&
    (history? s6 replacement).any (·.height > 0)) s!"{s6.balance} vs {expected2}"
  let confirmedEvent ← waitUntil 10_000 (do return (← relayed.get).contains "confirmed")
  check "watchRelay reports the confirmation" confirmedEvent s!"{← relayed.get}"
  -- 6b. A silent payment (BIP352) to a receiver this test holds the keys of.
  let code ← testReceiverCode
  let spInputs : SendInputs := { destination := code, amount := "150000", network := .regtest }
  let sp ← a.previewSend spInputs
  check "silent payment: the review knows it is one" (sp.silent && sp.destination == code && sp.amount == 150_000)
  let sent ← a.sendPayment spInputs sp
  discard <| waitUntil 20_000 (do return (← n.mempool).contains sent.txid)
  let spTx ← n.json #["getrawtransaction", sent.txid, "true"]
  let expectedScript ← testReceiverScript n spTx
  let paid := ((spTx.getObjValAs? (Array Json) "vout").toOption.getD #[]).any fun o =>
    ((o.getObjValD "scriptPubKey").getObjValAs? String "hex").toOption == some (hex expectedScript) &&
    (o.getObjValAs? Float "value").toOption == some 0.0015
  check "silent payment: the node's transaction pays the output the receiver finds" paid (hex expectedScript)
  check "silent payment: the receipt's address is that output's"
    (sent.derivedAddresses == [(AddressDecoder.address expectedScript .regtest).getD ""]) s!"{sent.derivedAddresses}"
  -- Core, told only the derived key, sees the coin once it is mined
  discard <| n.cli #["-named", "createwallet", "wallet_name=sp-watch", "disable_private_keys=true"]
  let desc ← n.json #["getdescriptorinfo", s!"rawtr({hex (expectedScript.extract 2 34)})"]
  let request := s!"[\{\"desc\":\"{(desc.getObjValAs? String "descriptor").toOption.getD ""}\",\"timestamp\":\"now\"}]"
  discard <| n.cli #["-rpcwallet=sp-watch", "importdescriptors", request]
  n.mine 1 mineAddr
  n.waitFilterIndex
  let watched ← n.json #["-rpcwallet=sp-watch", "listunspent", "1"]
  check "silent payment: Core's watch-only wallet finds the coin"
    (((watched.getArr?).toOption.getD #[]).any fun u => (u.getObjValAs? String "txid").toOption == some sent.txid)
  let (s6b, _) ← syncUntil a 60_000 fun s _ => (history? s sent.txid).any (·.height > 0)
  check "silent payment: confirmed in the app's history" ((history? s6b sent.txid).any (·.height > 0))
  -- 7. The receive window sees a relayed payment.
  let watched ← a.receiveAddress false
  let seen ← IO.mkRef (#[] : Array (String × Int))
  -- a window on an earlier address first: the second call replaces it
  a.watchAddress addr fun t amt => seen.modify (·.push (t, amt))
  a.watchAddress watched fun t amt => seen.modify (·.push (t, amt))
  let incoming ← n.wallet #["sendtoaddress", watched, "0.001"]
  let sawIt ← waitUntil 45_000 (do return (← seen.get).any (·.1 == incoming))
  check "watchAddress: the mempool window reports the payment" sawIt
  a.stopWatchingAddress
  n.mine 1 mineAddr
  n.waitFilterIndex
  -- less the silent payment (6b) and its fee
  let expected3 := expected2 - 150_000 - sp.fee + 100_000
  let (s7, _) ← syncUntil a 60_000 fun s _ => s.balance == expected3
  check "the watched payment confirms" (s7.balance == expected3) s!"{s7.balance}"
  -- 7b. A person from a second phone's card (pay-to only: signer keys went with vaults).
  let keysBob ← IO.mkRef ({} : Keys.InMemorySecrets)
  let bob ← match ← (Wallet.create .regtest (inMemoryKeyStore keysBob)).run with
    | .ok w => pure w
    | .error e => throw (IO.userError s!"Wallet.create: {e.name}")
  let cardBob ← RecordsReal.RM.toIO (do return (← RecordsReal.ownPersonCard bob "Bob").serialized)
  let r0 ← a.records
  check "records: no people yet" r0.people.isEmpty
  let r1 ← a.addPerson "Bob" (some cardBob) (some .supplied) none none
  check "addPerson Bob from his card: paid at fresh addresses"
    ((r1.people.find? (·.name == "Bob")).any (·.payTo == some true))
  -- 7c. A 2-of-2 multisig account with another signer's key, funded, spent and confirmed.
  let ms ← multisigFlow n a msA mineAddr
  -- 7d. A Ledger: paired 2-of-2 and a 2-of-3 with recovery, registered, addresses verified, both funded,
  -- each spend signed by the phone and the Ledger, broadcast and confirmed.
  let ledgerIDs ← ledgerFlow n a msA device mineAddr
  -- 8. Export, and import into a fresh directory (the wallet as exported: it paid the account in 7c, and a
  -- payment it just sent is still unconfirmed).
  let pendingInputs : SendInputs := { destination := ← n.wallet #["getnewaddress"], amount := "1000000", network := .regtest }
  let pendingTxid := (← a.sendPayment pendingInputs (← a.previewSend pendingInputs)).txid
  check "a payment pending at export" (← waitUntil 20_000 (do return (← n.mempool).contains pendingTxid))
  let (sExported, _) ← a.snapshot
  let bundle ← a.exportBundle false
  check "exportBundle carries the pending payment with the coins it spends" (match ImportBundle.decode bundle with
    | .ok b => b.pendingSends.size == 1 && b.pendingSends.all (fun p =>
        (Winnow.Transaction.decode p.rawTransaction).toOption.any (fun t => Winnow.displayHex t.txid == pendingTxid) && !p.selected.isEmpty)
    | .error _ => false)
  check "exportBundle (watch-only)" ((bundle.splitOn "\"regtest\"").length > 1 && (bundle.splitOn "mnemonic").length == 1)
  check "exportBundle carries the multisig accounts, the Ledger's registrations with them" (match ImportBundle.decode bundle with
    | .ok b => match b.vaults with
      | some vs => vs.map (·.id) == #[ms.id] ++ ledgerIDs && (vs.filter (·.ledger.isSome)).size == 2
      | none => false
    | .error _ => false)
  -- A bundle from the shared-account Winnow (accounts under "vaults") is refused, not restored without them.
  -- a well-formed account record as the shared-account Winnow wrote it (a MuSig2 account: upstream refuses
  -- it with unsupportedWalletData; a malformed record would be a decoding error there)
  let account := "{\"id\":\"q9x7v2kd\",\"name\":\"Joint\",\"descriptor\":\"tr(musig([a1b2c3d4/86'/1'/0']tpubA,[0badcafe/86'/1'/0']tpubB)/<0;1>/*)#q9x7v2kd\"," ++
    "\"createdAtHeight\":100,\"nextReceiveIndex\":0,\"nextChangeIndex\":0,\"utxos\":[]}"
  let withAccounts := "{\"vaults\":[" ++ account ++ "]," ++ (bundle.drop 1).toString
  let emptyAccounts := "{\"vaults\":[]," ++ (bundle.drop 1).toString
  check "ImportBundle: an empty accounts list decodes" ((ImportBundle.decode emptyAccounts) matches .ok _)
  check "ImportBundle: accounts are refused (unsupportedWalletData)"
    (match ImportBundle.decode withAccounts with | .error (.wallet .unsupportedWalletData) => true | _ => false)
  let keysB ← IO.mkRef ({} : Keys.InMemorySecrets)
  let (bImp, envB) ← Backend.realWithEnv (deps keysB "B")
  let dirB := s!"{dir}/B/BTCSwift/regtest"
  IO.FS.createDirAll dirB
  discard <| bImp.openWallet .regtest dirB
  bImp.startNetworking settings
  let refused ← attempt (bImp.importBundle .regtest dirB withAccounts)
  check "importBundle refuses a bundle with accounts, with unsupportedWalletData's text"
    (match refused with | .error e => toString e == WalletError.unsupportedWalletData.description | _ => false)
    (match refused with | .error e => toString e | .ok _ => "imported")
  let (_, report) ← bImp.importBundle .regtest dirB bundle
  say s!"  import report: {report.replace "\n" " | "}"
  let (sb, _) ← bImp.snapshot
  check "importBundle reproduces the balance" (sb.balance == sExported.balance && sb.utxoCount == sExported.utxoCount)
    s!"{sb.balance} vs {sExported.balance}"
  check "import report: scanned and confirmed every claim" (report.startsWith "Scanned from block" &&
    (report.splitOn "Claimed but spent since: 0").length > 1)
  check "importBundle: the pending payment is in history, unconfirmed" ((history? sb pendingTxid).any (·.height == 0))
  check "importBundle: the pending payment is handed to the relay" ((← bImp.rawTransactionHex pendingTxid).isSome)
  -- a pending payment whose coins are not its inputs is refused
  let forgedPending := match ImportBundle.decode bundle with
    | .ok b =>
      let forged : ImportBundle := { b with pendingSends := b.pendingSends.map fun (p : Winnow.PendingSend) => { p with selected := p.selected.extract 1 p.selected.size } }
      some forged.serialized
    | .error _ => none
  let keysF ← IO.mkRef ({} : Keys.InMemorySecrets)
  let (fImp, _) ← Backend.realWithEnv (deps keysF "F")
  let dirF := s!"{dir}/F/BTCSwift/regtest"
  IO.FS.createDirAll dirF
  discard <| fImp.openWallet .regtest dirF
  let forgedResult ← attempt (fImp.importBundle .regtest dirF (forgedPending.getD ""))
  check "importBundle refuses a pending payment whose coins are not its inputs"
    (match forgedResult with | .error e => toString e == (WalletError.invalidBundle "pending payment: its coins are not its inputs").description | _ => false)
    (match forgedResult with | .error e => toString e | .ok _ => "imported")
  let restored := (← bImp.multisigOverview).accounts.find? (·.id == ms.id)
  check "importBundle restores the multisig account with its balance" ((restored.map (·.balance)) == some ms.balance)
    s!"{restored.map (·.balance)} vs {ms.balance}"
  bImp.stopNetworking
  -- 9. Stop networking: nothing keeps running.
  a.stopNetworking
  let quiet ← waitUntil 5_000 (do
    return (← envA.diagnostics).liveLoops == 0 && (← envB.diagnostics).liveLoops == 0)
  check "stopNetworking: no loop thread left" quiet s!"{repr (← envA.diagnostics)}"
  let (sStop, pStop) ← a.snapshot
  check "after stop: no stack, idle, no peers" (pStop == .idle && sStop.peerCount == 0 && !(← envA.diagnostics).hasStack)
  let gone ← waitUntil 5_000 (do return (← n.winnowPeers) == 0)
  check "after stop: the node has no Winnow peer" gone
  let headersBefore ← IO.FS.readBinFile (System.FilePath.mk dirA / "headers.bin")
  let filtersBefore ← IO.FS.readBinFile (System.FilePath.mk dirA / "filters.json")
  let walletBefore ← IO.FS.readBinFile (System.FilePath.mk dirA / "wallet.json")
  let d0 ← envA.diagnostics
  n.mine 2 mineAddr
  IO.sleep 6_000
  let d1 ← envA.diagnostics
  check "after stop: no sync pass and no phase tick while blocks arrive"
    (d1.syncPasses == d0.syncPasses && d1.phaseTicks == d0.phaseTicks && !d1.syncing) s!"{repr d0} → {repr d1}"
  check "after stop: still no Winnow peer (no reconnect)" ((← n.winnowPeers) == 0)
  check "after stop: headers.bin, filters.json, wallet.json unchanged"
    (headersBefore == (← IO.FS.readBinFile (System.FilePath.mk dirA / "headers.bin")) &&
     filtersBefore == (← IO.FS.readBinFile (System.FilePath.mk dirA / "filters.json")) &&
     walletBefore == (← IO.FS.readBinFile (System.FilePath.mk dirA / "wallet.json")))
  let late ← attempt a.syncNow
  let d2 ← envA.diagnostics
  check "after stop: syncNow without a stack does nothing" (late matches .ok _ && d2.syncPasses == d1.syncPasses)
  -- 10. Open the wallet again from disk (a new backend, the same key store).
  let (c, envC) ← Backend.realWithEnv (deps keysA "C")
  let reopened ← c.openWallet .regtest dirA
  let (sc, _) ← c.snapshot
  check "openWallet from disk: same wallet, same balance and history" (match reopened with
    | .opened _ => sc.balance == sExported.balance && sc.history.length == sExported.history.length | _ => false) s!"{sc.balance}"
  let words2 ← c.revealMnemonic
  check "revealMnemonic reads the same words back" (words2 == words)
  c.deleteWallet
  -- AppModel deletes the wallet's key only; the records' store keys stay (as in the Keychain)
  check "deleteWallet removes the wallet key and wallet.json" ((← keysA.get).keys.all (·.startsWith "store-key.") &&
    !(← (System.FilePath.mk dirA / "wallet.json").pathExists))
  let afterDelete ← c.openWallet .regtest dirA
  check "after deleteWallet the directory opens as missing" (afterDelete matches .missing)
  check "no loop thread in the reopened backend" ((← envC.diagnostics).liveLoops == 0)
  -- 11. The journal: the events AppModel writes, with its field names and value formats.
  checkJournal "wallet.created" ["walletID", "height", "headersContinueInBackground"]
    (fun f => field f "walletID" == walletID && (field f "height").toNat?.isSome && field f "headersContinueInBackground" == "true")
  checkJournal "import.onboardingCompleted" ["walletID"] (field · "walletID" == walletID) "creation finishes onboarding by itself"
  checkJournal "background.completed" ["complete"] (field · "complete" == "true")
  checkJournal "wallet.ready" ["walletID", "balance", "utxoCount", "historyCount", "nextScanHeight"]
    (fun f => field f "walletID" == walletID && field f "balance" == "0")
  let receives ← journaled "address.receive"
  checkJournal "address.receive" ["address"] (field · "address" == addr)
  check "journal: address.receive once per current-address peek, never for New address" (receives.size == 3) s!"{receives.size}"
  checkJournal "transaction.broadcast" ["txid", "raw"] (fun f => field f "txid" == txid && rawIsTxid (field f "raw") txid)
  check "journal: every transaction.broadcast raw decodes to its txid"
    ((← journaled "transaction.broadcast").all fun (_, f) => rawIsTxid (field f "raw") (field f "txid"))
  checkJournal "transaction.sent" ["txid", "raw", "silent", "silentOutputs"]
    (fun f => field f "txid" == txid && rawIsTxid (field f "raw") txid && field f "silent" == "false" && field f "silentOutputs" == "")
    "its raw decodes to the sent txid; not a silent payment"
  check "journal: the silent payment's transaction.sent names its derived output"
    ((← journaled "transaction.sent").any fun (_, f) => field f "silent" == "true" && (field f "silentOutputs").startsWith "5120")
  checkJournal "transaction.replaced" ["original", "replacement", "raw"]
    (fun f => field f "original" == txid2 && field f "replacement" == replacement && rawIsTxid (field f "raw") replacement)
  checkJournal "person.added" ["name", "payToKind"]
    (fun f => field f "name" == "Bob" && field f "payToKind" == "descriptor")
  checkJournal "wallet.exported" ["bundleVersion", "seedBearing", "lastKnownHeight", "utxoCount", "historyCount"]
    (fun f => field f "seedBearing" == "false" && field f "bundleVersion" == "2")
  checkJournal "import.started" ["bundleVersion", "seedBearing", "lastKnownHeight", "utxoCount", "historyCount"]
    (fun f => field f "seedBearing" == "false")
  checkJournal "import.verified" ["scannedFromHeight", "scannedToHeight", "matchesBundle", "confirmedUTXOCount",
      "spentSinceBundleCount", "discoveredUTXOCount", "balance", "utxoCount", "historyCount", "nextScanHeight"]
    (fun f => field f "matchesBundle" == "true" && field f "balance" == toString sExported.balance && field f "spentSinceBundleCount" == "0")
  -- B imports; F starts an import of a forged pending payment, which is refused before anything verifies
  check "journal: import events come from the importing backends"
    ((← journaled "import.started").all (fun e => e.1 == "B" || e.1 == "F") && (← journaled "import.verified").all (·.1 == "B"))
  check "journal: no import.verificationWaiting (the import verified)" (← journaled "import.verificationWaiting").isEmpty
  checkJournal "wallet.destroyed" ["walletID"] (field · "walletID" == walletID)
  checkJournal "multisig.accountAdded" ["id", "descriptor", "height", "firstAddress"]
    (fun f => field f "id" == ms.id && field f "firstAddress" == ms.firstAddress && (field f "height").toNat?.isSome)
  for stage in ["multisig-created", "multisig-signed", "multisig-combined"] do
    checkJournal "psbt.generated" ["stage", "base64", "inputCount", "outputCount"]
      (fun f => field f "stage" == stage && field f "inputCount" == "1" && field f "outputCount" == "2") stage
  checkJournal "multisig.spendBroadcast" ["id", "txid"] (fun f => field f "id" == ms.id && field f "txid" == ms.txid)
  checkJournal "signer.ledgerPaired" ["id", "fingerprint"] (fun f => (field f "fingerprint").length == 8)
  checkJournal "multisig.ledgerRegistered" ["id"] (fun f => ledgerIDs.contains (field f "id"))
  let registered ← journaled "multisig.ledgerRegistered"
  check "journal: multisig.ledgerRegistered for both Ledger accounts" (ledgerIDs.all fun id => registered.any (field ·.2 "id" == id))
  checkJournal "psbt.generated" ["stage", "base64", "inputCount", "outputCount"]
    (fun f => field f "stage" == "multisig-ledger-signed") "multisig-ledger-signed"
  check "journal: the multisig spend's transaction.broadcast raw decodes to its txid"
    ((← journaled "transaction.broadcast").any fun (_, f) => field f "txid" == ms.txid && rawIsTxid (field f "raw") ms.txid)
  checkJournal "peers.status" ["connected", "target", "dialing", "exhausted", "peers", "rejected"]
    (fun f => field f "connected" == "1" && field f "dialing" ∈ ["true", "false"] && (field f "peers").startsWith "127.0.0.1:")
  checkJournal "wallet.snapshot" ["walletID", "balance", "utxoCount", "historyCount", "nextScanHeight", "tipHeight",
      "peerCount", "confirmedTransactions", "pendingTransactions", "replacements"]
    (fun f => field f "walletID" == walletID && ((field f "confirmedTransactions").splitOn s!"{txid}@{sendHeight}").length > 1 &&
       ((field f "replacements").splitOn s!"{txid2}>{replacement}").length > 1)
  let deduped (name : String) : IO Bool := do
    let es ← journaled name
    return ["A", "B", "C"].all fun tag =>
      let fs := (es.filter (·.1 == tag)).map (·.2)
      (List.range (fs.size - 1)).all fun i => fs[i]! != fs[i + 1]!
  check "journal: peers.status and wallet.snapshot are journaled only when they change"
    ((← deduped "peers.status") && (← deduped "wallet.snapshot"))
  let phrase := " ".intercalate words
  check "journal: no field carries the recovery phrase"
    ((← journalEvents.get).all fun (_, _, f) => f.all fun (_, v) => (v.splitOn phrase).length == 1)

/-- `backend-test --fixture <dir>`: a regtest node left running (for driving the iOS app against it) and a
funded wallet's watch-only backup at `<dir>/bundle.json`; prints the node's pid and ports. -/
def fixture (dir : String) : IO UInt32 := do
  IO.FS.createDirAll dir
  let n ← startNode dir
  discard <| n.cli #["createwallet", "w"]
  let mineAddr ← n.wallet #["getnewaddress"]
  n.mine 101 mineAddr
  n.waitFilterIndex
  let keys ← IO.mkRef ({} : Keys.InMemorySecrets)
  let (a, _) ← Backend.realWithEnv (deps keys)
  let wdir := s!"{dir}/wallet/regtest"
  IO.FS.createDirAll wdir
  discard <| a.openWallet .regtest wdir
  a.startNetworking (regtestSettings n)
  discard <| a.createWallet .regtest wdir
  a.finishOnboarding
  let addr ← a.receiveAddress false
  discard <| n.wallet #["sendtoaddress", addr, "0.5"]
  n.mine 1 mineAddr
  n.waitFilterIndex
  let tip ← n.height
  let (s, _) ← syncUntil a 90_000 fun s _ => s.tipHeight == tip && s.balance > 0
  IO.FS.writeFile s!"{dir}/bundle.json" (← a.exportBundle false)
  -- with the recovery phrase: imported, it can spend (the UI test's normal-mode send)
  IO.FS.writeFile s!"{dir}/bundle-seed.json" (← a.exportBundle true)
  IO.FS.writeFile s!"{dir}/fixture.json"
    s!"\{\"p2p\": {n.p2p}, \"rpc\": {n.rpc}, \"pid\": {n.pid}, \"datadir\": \"{n.datadir}\"}"
  a.stopNetworking
  say s!"fixture: node pid {n.pid} p2p {n.p2p} rpc {n.rpc} datadir {n.datadir}; wallet balance {s.balance} at {tip}"
  return 0

def main (args : List String) : IO UInt32 := do
  if let ["--fixture", dir] := args then return ← fixture dir
  -- for the UI journey: the test receiver's code, and the output it finds in a transaction on a fixture
  if let ["--sp-code"] := args then IO.println (← testReceiverCode); return 0
  if let ["--sp-expected", datadir, rpc, txid] := args then
    let n : Node := { datadir, p2p := 0, rpc := rpc.toNat!.toUInt16, pid := 0 }
    IO.println (hex (← testReceiverScript n (← n.json #["getrawtransaction", txid, "true"])))
    return 0
  let tmp ← IO.FS.createTempDir
  let dir := tmp.toString
  say s!"backend-test: work dir {dir}"
  let node ← (startNode dir).toBaseIO
  let n ← match node with
    | .ok n => pure n
    | .error e => say s!"FAIL could not start bitcoind: {e}"; return 1
  spawn do
    IO.sleep 900_000
    say "FAIL watchdog: the test ran for 15 minutes"
    killPid n.pid "-KILL"
    IO.Process.exit 2
  try
    flow dir n
  catch e =>
    failures.modify (·.push s!"exception: {e}")
    say s!"  FAIL exception: {e}"
  finally
    discard <| (n.cli #["stop"]).toBaseIO
    discard <| waitUntil 10_000 (do
      let r ← IO.Process.output { cmd := "kill", args := #["-0", toString n.pid] }
      return r.exitCode != 0)
    killPid n.pid "-KILL"
    try IO.FS.removeDirAll tmp catch _ => pure ()
  let fs ← failures.get
  say s!"backend-test: {← passes.get} passed, {fs.size} failed{if fs.isEmpty then "" else ": " ++ ", ".intercalate fs.toList}"
  IO.Process.exit (if fs.isEmpty then 0 else 1)
