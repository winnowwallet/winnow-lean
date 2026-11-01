import Lean.Data.Json
import TestKit.Check

/-! # A disposable regtest bitcoind, through bitcoin-cli

`startNode` starts `bitcoind -regtest` in a directory of its own on random free ports (up to five attempts),
with the block-filter index served to peers (`filters`, io-test's and backend-test's node) or as
multisig-differential's: no P2P listening and no filters. `withNode` runs a test against one under a watchdog
and stops it after, also on failure; the journeys reach the fixture's node with `Node.attach`. The binaries are
`$WINNOW_BITCOIND` / `$WINNOW_BITCOIN_CLI` (scripts/install-bitcoin's pinned Core), else Homebrew's, else the
PATH's. -/

namespace TestKit.Regtest
open Lean

/-- A Bitcoin Core binary: `$<env>`, else Homebrew's, else the PATH. -/
def findTool (env name : String) : IO String := do
  if let some path := (← IO.getEnv env) then return path
  for dir in ["/opt/homebrew/bin", "/usr/local/bin"] do
    if ← System.FilePath.pathExists s!"{dir}/{name}" then return s!"{dir}/{name}"
  return name

structure Node where
  datadir : String
  rpc : UInt16
  /-- 0 when the node does not listen. -/
  p2p : UInt16 := 0
  /-- 0 for a node this process did not start. -/
  pid : UInt32 := 0
  bitcoinCli : String

/-- A node already running (the UI fixture's), reached through `$WINNOW_BITCOIN_CLI`. -/
def Node.attach (datadir : String) (rpc : UInt16) (p2p : UInt16 := 0) : IO Node := do
  return { datadir, rpc, p2p, bitcoinCli := ← findTool "WINNOW_BITCOIN_CLI" "bitcoin-cli" }

/-- bitcoin-cli's standard output, trimmed; a nonzero exit throws its standard error. -/
def Node.cli (n : Node) (args : Array String) : IO String := do
  let out ← IO.Process.output { cmd := n.bitcoinCli, args := #["-regtest", s!"-datadir={n.datadir}", s!"-rpcport={n.rpc}"] ++ args }
  if out.exitCode != 0 then throw (IO.userError s!"bitcoin-cli {args}: {out.stderr.trimAscii}")
  return out.stdout.trimAscii.toString

/-- bitcoin-cli with `-rpcwallet` (the funded wallet is `w`). -/
def Node.wallet (n : Node) (args : Array String) (wallet := "w") : IO String := n.cli (#[s!"-rpcwallet={wallet}"] ++ args)

private def parse (args : Array String) (text : String) : IO Json :=
  match Json.parse text with
  | .ok j => return j
  | .error e => throw (IO.userError s!"json {args}: {e}")

def Node.json (n : Node) (args : Array String) : IO Json := do parse args (← n.cli args)
def Node.walletJson (n : Node) (args : Array String) (wallet := "w") : IO Json := do parse args (← n.wallet args wallet)

def Node.height (n : Node) : IO Nat := do return (← n.cli #["getblockcount"]).toNat!

/-- `count` blocks to `addr`, 500 at a time. -/
def Node.mine (n : Node) (count : Nat) (addr : String) : IO Unit := do
  let mut left := count
  while left > 0 do
    let k := min left 500
    discard <| n.cli #["generatetoaddress", toString k, addr]
    left := left - k

/-- `count` blocks paying an anyone-can-spend script, so no wallet on the node records any of them (and many
mine in a moment). -/
def Node.mineElsewhere (n : Node) (count : Nat) : IO Unit := do
  let some d := ((← n.json #["getdescriptorinfo", "raw(51)"]).getObjValAs? String "descriptor").toOption
    | throw (IO.userError "getdescriptorinfo raw(51)")
  let mut left := count
  while left > 0 do
    let k := min left 500
    discard <| n.cli #["generatetodescriptor", toString k, d]
    left := left - k

def Node.mempool (n : Node) : IO (Array String) := do
  match ← n.json #["getrawmempool"] with
  | .arr xs => return xs.filterMap fun | .str s => some s | _ => none
  | _ => return #[]

/-- Waits (up to 30 s) until the block-filter index has caught up with the tip. A peer asking for filters past
the index goes unanswered until it times out. -/
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
  throw (IO.userError "the node's block filter index did not reach its tip in 30 s")

/-- `sats` as bitcoin-cli's BTC amount: `0.00012000`. -/
def btc (sats : Nat) : String :=
  let frac := toString (sats % 100000000)
  s!"{sats / 100000000}.{String.ofList (List.replicate (8 - frac.length) '0')}{frac}"

/-- Pays `sats` from the funded wallet `w` to `address`, mines it and waits for the filter index; the txid. -/
def Node.fund (n : Node) (address : String) (sats : Nat) : IO String := do
  let txid ← n.wallet #["sendtoaddress", address, btc sats]
  n.mine 1 (← n.wallet #["getnewaddress"])
  n.waitFilterIndex
  return txid

def killPid (pid : UInt32) (signal : String := "-TERM") : IO Unit := do
  discard <| IO.Process.output { cmd := "kill", args := #[signal, toString pid] }

/-- Waits for a condition, polling every `every` ms; the condition's value at the deadline. -/
def waitUntil (ms : Nat) (cond : IO Bool) (every : UInt32 := 100) : IO Bool := do
  let deadline := (← IO.monoMsNow) + ms
  while (← IO.monoMsNow) < deadline do
    if ← cond then return true
    IO.sleep every
  cond

private def randomPort : IO UInt16 := do
  let b ← IO.getRandomBytes 2
  return (30000 + (b[0]!.toNat * 256 + b[1]!.toNat) % 25000).toUInt16

/-- `bitcoind -regtest` in `dir/node<attempt>`, on random ports (P2P, and RPC the one after it); another
attempt when it does not answer within 30 s (a port taken), five in all. `filters`: listening on 127.0.0.1 and
serving the block-filter index (BIP157/158), else no P2P at all. -/
def startNode (dir : String) (filters := true) : IO Node := do
  let bitcoind ← findTool "WINNOW_BITCOIND" "bitcoind"
  let bitcoinCli ← findTool "WINNOW_BITCOIN_CLI" "bitcoin-cli"
  for attempt in [0:5] do
    let p2p ← randomPort
    let rpc := p2p + 1
    let datadir := s!"{dir}/node{attempt}"
    IO.FS.createDirAll datadir
    let network := if filters then
        #["-bind=127.0.0.1", "-listen=1", "-blockfilterindex=1", "-peerblockfilters=1", "-whitelist=noban@127.0.0.1"]
      else #["-rpcbind=127.0.0.1", "-rpcallowip=127.0.0.1", "-listen=0"]
    let child ← IO.Process.spawn {
      cmd := bitcoind
      args := #["-regtest", s!"-datadir={datadir}", s!"-port={p2p}", s!"-rpcport={rpc}"] ++ network ++
        #["-server=1", "-fallbackfee=0.0002", "-printtoconsole=0", "-dnsseed=0", "-discover=0", "-listenonion=0",
          "-keypool=1", "-unsafesqlitesync=1"]
      stdout := .null, stderr := .null, stdin := .null }
    let n : Node := { datadir, rpc, p2p := if filters then p2p else 0, pid := child.pid, bitcoinCli }
    let mut ready := false
    for _ in [0:150] do
      IO.sleep 200
      if (← child.tryWait).isSome then break
      match ← (n.cli #["getblockchaininfo"]).toBaseIO with
      | .ok _ => ready := true; break
      | .error _ => pure ()
    if ready then return n
    killPid child.pid "-KILL"
  throw (IO.userError "bitcoind did not start")

/-- `bitcoin-cli stop`, at most 10 s for the node to exit (gone, or a zombie: this process never reaps it, so
`kill -0` would answer until the time ran out), then `kill -KILL`. -/
def Node.stop (n : Node) : IO Unit := do
  discard <| (n.cli #["stop"]).toBaseIO
  discard <| waitUntil 10_000 (every := 200) do
    let r ← IO.Process.output { cmd := "ps", args := #["-o", "stat=", "-p", toString n.pid] }
    return r.exitCode != 0 || r.stdout.trimAscii.toString.startsWith "Z"
  killPid n.pid "-KILL"

/-- `body` against a node started in `dir`, stopped after, also on failure; a watchdog kills the node and the
process (exit 2) after `watchdogMs`. -/
def withNode (dir : String) (body : Node → IO Unit) (filters := true) (watchdogMs : Nat := 900_000) : IO Unit := do
  let n ← startNode dir filters
  discard <| IO.asTask (prio := .dedicated) do
    IO.sleep watchdogMs.toUInt32
    say s!"  FAIL watchdog: the test ran for {watchdogMs / 60_000} minutes"
    killPid n.pid "-KILL"
    (IO.Process.exit 2 : IO Unit)
  try body n finally n.stop

end TestKit.Regtest
