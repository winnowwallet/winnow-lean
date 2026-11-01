import LeanNative.Journey

/-! # The journeys' host side: the fixture's regtest node, Bitcoin Core as a co-signer, backend-test's receiver

Everything a journey checks the app against lives on the Mac: the node `scripts/ui-fixture start` left running
(its config in `WINNOW_UI_CONFIG`), `bitcoin-cli` against it, Bitcoin Core wallets that sign an account's PSBTs
with their own libsecp256k1, and backend-test's silent payment receiver. Nothing here touches the app. -/

namespace WinnowJourneys
open Lean LeanNative.Journey

def readJson (path : String) : IO Json := do
  match Json.parse (← IO.FS.readFile path) with
  | .ok j => pure j
  | .error e => failure s!"{path} is not JSON: {e}"

def field [FromJson α] (j : Json) (key : String) : IO α :=
  match j.getObjValAs? α key with
  | .ok v => pure v
  | .error e => failure s!"{key}: {e} in {j.compress.take 300}"

def strings (j : Json) : List String :=
  match j.getArr? with
  | .ok a => a.toList.filterMap fun s => (s.getStr?).toOption
  | .error _ => []

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

namespace Host

def load : IO Host := do
  let some path ← IO.getEnv "WINNOW_UI_CONFIG"
    | failure "no WINNOW_UI_CONFIG: scripts/ui-fixture start writes it to the run's test-env"
  let c ← readJson path
  let fixture : String ← field c "fixture"
  let f ← readJson s!"{fixture}/fixture.json"
  return { bitcoinCli := ← field c "bitcoinCli", backendTest := ← field c "backendTest", fixture,
           datadir := ← field f "datadir", rpc := ← field f "rpc", p2p := ← field f "p2p" }

/-- A host program's standard output, trimmed; a nonzero exit fails the journey with its standard error.
backend-test reaches the node through the same pinned Core (WINNOW_BITCOIN_CLI). -/
def run (h : Host) (cmd : String) (args : Array String) : IO String := do
  let out ← IO.Process.output { cmd, args, env := #[("WINNOW_BITCOIN_CLI", some h.bitcoinCli)] }
  if out.exitCode != 0 then
    failure s!"{(cmd.splitOn "/").getLast!} {" ".intercalate args.toList} exited {out.exitCode}: {out.stderr.trimAscii}"
  return out.stdout.trimAscii.copy

def cli (h : Host) (args : Array String) : IO String :=
  h.run h.bitcoinCli (#["-regtest", s!"-datadir={h.datadir}", s!"-rpcport={h.rpc}"] ++ args)

/-- bitcoin-cli with -rpcwallet (the fixture's funded wallet is `w`). -/
def wallet (h : Host) (wallet : String) (args : Array String) : IO String :=
  h.cli (#[s!"-rpcwallet={wallet}"] ++ args)

private def parseCli (args : Array String) (text : String) : IO Json :=
  match Json.parse text with
  | .ok j => pure j
  | .error _ => failure s!"bitcoin-cli {args}: not JSON: {text.take 300}"

def cliJson (h : Host) (args : Array String) : IO Json := do parseCli args (← h.cli args)
def walletJson (h : Host) (wallet : String) (args : Array String) : IO Json := do
  parseCli args (← h.wallet wallet args)

def mempool (h : Host) : IO (List String) := do return strings (← h.cliJson #["getrawmempool"])
def bankAddress (h : Host) : IO String := h.wallet "w" #["getnewaddress"]
def height (h : Host) : IO Nat := do return (← h.cli #["getblockcount"]).toNat!

/-- Until the node's block filter index reaches its tip. The app asks for filters up to the tip it has
synced; a request past the index goes unanswered until it times out, and the app then drops its only peer. -/
def waitFilterIndex (h : Host) : IO Unit := do
  let tip ← h.height
  for _ in [0:600] do
    let info ← h.cliJson #["getindexinfo", "basic block filter index"]
    let best := ((info.getObjValD "basic block filter index").getObjValAs? Nat "best_block_height").toOption.getD 0
    if best ≥ tip then return
    IO.sleep 50
  failure "the node's block filter index did not reach its tip in 30 s"

def mine (h : Host) (blocks : Nat) : IO Unit := do
  discard <| h.cli #["generatetoaddress", toString blocks, ← h.bankAddress]
  h.waitFilterIndex

/-- `blocks` blocks paying an anyone-can-spend script: no wallet on the node scans them in, so many blocks mine
in a moment. -/
def mineElsewhere (h : Host) (blocks : Nat) : IO Unit := do
  let some d := ((← h.cliJson #["getdescriptorinfo", "raw(51)"]).getObjValAs? String "descriptor").toOption
    | failure "getdescriptorinfo raw(51)"
  discard <| h.cli #["generatetodescriptor", toString blocks, d]
  h.waitFilterIndex

def btc (sats : Nat) : String :=
  let frac := toString (sats % 100000000)
  s!"{sats / 100000000}.{String.ofList (List.replicate (8 - frac.length) '0')}{frac}"

/-- Pays `sats` from the funded wallet to `address` and mines it; the payment's txid. -/
def fund (h : Host) (address : String) (sats : Nat) : IO String := do
  let txid ← h.wallet "w" #["sendtoaddress", address, btc sats]
  h.mine 1
  return txid

/-- A transaction in the mempool, decoded by the node (a confirmed one needs a wallet's gettransaction: the
node keeps no txindex). -/
def transaction (h : Host) (txid : String) : IO Json := h.cliJson #["getrawtransaction", txid, "true"]

def scriptPubKey (h : Host) (address : String) : IO String := do
  field (← h.cliJson #["validateaddress", address]) "scriptPubKey"

/-- Whether the node's wallet `w` has the payment confirmed. -/
def confirmed (h : Host) (txid : String) : IO Bool := do
  let confirmations : Nat ← field (← h.walletJson "w" #["gettransaction", txid]) "confirmations"
  return confirmations > 0

/-- backend-test's silent payment test receiver (written from BIP352's receiving side): its code, and the
output script it finds in a transaction on the node. -/
def silentPaymentCode (h : Host) : IO String := h.run h.backendTest #["--sp-code"]
def silentPaymentExpectedScript (h : Host) (txid : String) : IO String :=
  h.run h.backendTest #["--sp-expected", h.datadir, toString h.rpc, txid]

/-- The transactions in the tip block. -/
def tipTransactions (h : Host) : IO (List String) := do
  return strings ((← h.cliJson #["getblock", ← h.cli #["getbestblockhash"]]).getObjValD "tx")

/-- The one transaction that enters the mempool after `before`, within `within` seconds. -/
def newMempoolTransaction (h : Host) (before : List String) (within : Float) : UI String := do
  let found ← IO.mkRef (none : Option String)
  waitUntil within "the node never received the payment" (every := 0.25) do
    let now ← h.mempool
    found.set (now.find? (!before.contains ·))
    return (← found.get).isSome
  return (← found.get).get!

end Host

/-! ## Transactions as the node decodes them -/

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

/-- The node's view of a payment the app made: it pays `destination` exactly `sats`. -/
def Host.expectPays (h : Host) (txid destination : String) (sats : Nat) : UI Unit := do
  expect (pays (← h.transaction txid) (← h.scriptPubKey destination) sats)
    s!"the transaction the node accepted does not pay {destination} {sats} sats"

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

/-- The Core signers are done: their wallets unloaded. -/
def Host.unload (h : Host) (signers : List CoreSigner) : IO Unit := do
  for s in signers do discard <| h.cli #["unloadwallet", s.wallet]

end WinnowJourneys
