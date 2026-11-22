import LeanNative.Journey
import TestKit.Fixtures
import TestKit.Regtest
import Winnow.Crypto.Base58
import Winnow.Crypto.Sha2
import Winnow.Keys.BIP32
import Winnow.Keys.BIP39
import Winnow.Keys.Secp256k1
import Winnow.Wallet.People

/-! # The journeys' host side: the fixture's regtest node, Bitcoin Core as a co-signer, backend-test's receiver

Everything a journey checks the app against lives on the Mac: the node `scripts/ui-fixture start` left running
(its config in `WINNOW_UI_CONFIG`), reached as a `TestKit.Regtest.Node` (bitcoin-cli, mining, the filter index,
funding), Bitcoin Core wallets that sign an account's PSBTs with their own libsecp256k1, and backend-test's silent
payment receiver. Nothing here touches the app. -/

namespace WinnowJourneys
open Lean LeanNative.Journey
open TestKit.Regtest (Node)

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
fixture.json. The node's own calls (`cli`, `json`, `wallet`, `walletJson`, `height`, `mempool`, `fund`, …) are
`Node`'s. -/
structure Host extends Node where
  /-- LeanApp's backend-test: the silent payment test receiver -/
  backendTest : String
  fixture : String
  /-- the fixture's SOCKS5 gateway (scripts/socks-gateway), standing in for a person's Tor and I2P gateways: every
  .onion and .i2p name reaches the node; and its log of each CONNECT (`<name>:<port> ok|refused`) -/
  socksGateway : Nat := 0
  socksLog : String := ""
  /-- the fixture's proxy in front of the node (scripts/peer-proxy), the file that says what it does (`{"mode":
  "pass" | "drop" | "stall"}`), and its log -/
  peerProxy : Nat := 0
  peerProxyControl : String := ""
  peerProxyLog : String := ""

namespace Host

def load : IO Host := do
  let some path ← IO.getEnv "WINNOW_UI_CONFIG"
    | failure "no WINNOW_UI_CONFIG: scripts/ui-fixture start writes it to the run's test-env"
  let c ← readJson path
  let fixture : String ← field c "fixture"
  let f ← readJson s!"{fixture}/fixture.json"
  let rpc : Nat ← field f "rpc"
  let p2p : Nat ← field f "p2p"
  return { bitcoinCli := ← field c "bitcoinCli", backendTest := ← field c "backendTest", fixture,
           datadir := ← field f "datadir", rpc := rpc.toUInt16, p2p := p2p.toUInt16,
           socksGateway := (c.getObjValAs? Nat "socksGateway").toOption.getD 0,
           socksLog := (c.getObjValAs? String "socksLog").toOption.getD "",
           peerProxy := (c.getObjValAs? Nat "peerProxy").toOption.getD 0,
           peerProxyControl := (c.getObjValAs? String "peerProxyControl").toOption.getD "",
           peerProxyLog := (c.getObjValAs? String "peerProxyLog").toOption.getD "" }

/-- A host program's standard output, trimmed; a nonzero exit fails the journey with its standard error.
backend-test reaches the node through the same pinned Core (WINNOW_BITCOIN_CLI). -/
def run (h : Host) (cmd : String) (args : Array String) : IO String := do
  let out ← IO.Process.output { cmd, args, env := #[("WINNOW_BITCOIN_CLI", some h.bitcoinCli)] }
  if out.exitCode != 0 then
    failure s!"{(cmd.splitOn "/").getLast!} {" ".intercalate args.toList} exited {out.exitCode}: {out.stderr.trimAscii}"
  return out.stdout.trimAscii.copy

def bankAddress (h : Host) : IO String := h.wallet #["getnewaddress"]

/-- `blocks` blocks to the funded wallet, and the node's block filter index at its tip: the app asks for filters
up to the tip it has synced, and a request past the index goes unanswered until the app drops its only peer. -/
def mine (h : Host) (blocks : Nat) : IO Unit := do
  h.toNode.mine blocks (← h.bankAddress)
  h.waitFilterIndex

/-- `blocks` blocks paying an anyone-can-spend script: no wallet on the node scans them in, so many blocks mine
in a moment. -/
def mineElsewhere (h : Host) (blocks : Nat) : IO Unit := do
  h.toNode.mineElsewhere blocks
  h.waitFilterIndex

/-- A transaction in the mempool, decoded by the node (a confirmed one needs a wallet's gettransaction: the
node keeps no txindex). -/
def transaction (h : Host) (txid : String) : IO Json := h.json #["getrawtransaction", txid, "true"]

def scriptPubKey (h : Host) (address : String) : IO String := do
  field (← h.json #["validateaddress", address]) "scriptPubKey"

/-- Whether the node's wallet `w` has the payment confirmed. -/
def confirmed (h : Host) (txid : String) : IO Bool := do
  let confirmations : Nat ← field (← h.walletJson #["gettransaction", txid]) "confirmations"
  return confirmations > 0

/-- backend-test's silent payment test receiver (written from BIP352's receiving side): its code, and the
output script it finds in a transaction on the node. -/
def silentPaymentCode (h : Host) : IO String := h.run h.backendTest #["--sp-code"]
/-- The address payment `index` of a person card's code goes to, derived from the card's text alone. -/
def cardAddress (h : Host) (card : String) (index : Nat) : IO String :=
  h.run h.backendTest #["--card-address", card, toString index]

def silentPaymentExpectedScript (h : Host) (txid : String) : IO String :=
  h.run h.backendTest #["--sp-expected", h.datadir, toString h.rpc, txid]

/-- The transactions in the tip block. -/
def tipTransactions (h : Host) : IO (List String) := do
  return strings ((← h.json #["getblock", ← h.cli #["getbestblockhash"]]).getObjValD "tx")

/-- The one transaction that enters the mempool after `before`, within `within` seconds. -/
def newMempoolTransaction (h : Host) (before : Array String) (within : Float) : UI String := do
  let found ← IO.mkRef (none : Option String)
  waitUntil within "the node never received the payment" (every := 0.25) do
    let now ← h.mempool
    found.set (now.find? (!before.contains ·))
    return (← found.get).isSome
  return (← found.get).get!

end Host

/-! ## Transactions as the node decodes them -/

/-- A bitcoin amount as the node writes it (a JSON number of BTC), in sats: exact. -/
def satsOf : Json → Nat
  | .num n => (n.mantissa * 100000000 / (10 : Int) ^ n.exponent).toNat
  | _ => 0

/-- An output of a decoded transaction: its script, address and value in sats. -/
structure Output where
  script : String
  address : String
  sats : Nat

def outputs (tx : Json) : List Output :=
  match (tx.getObjValD "vout").getArr? with
  | .error _ => []
  | .ok vs => vs.toList.map fun o =>
    let spk := o.getObjValD "scriptPubKey"
    { script := (spk.getObjValAs? String "hex").toOption.getD "", address := (spk.getObjValAs? String "address").toOption.getD "",
      sats := satsOf (o.getObjValD "value") }

/-- The coins a decoded transaction spends, as `txid:vout`, in its order. -/
def spends (tx : Json) : List String :=
  match (tx.getObjValD "vin").getArr? with
  | .error _ => []
  | .ok vs => vs.toList.map fun v =>
    s!"{(v.getObjValAs? String "txid").toOption.getD ""}:{(v.getObjValAs? Nat "vout").toOption.getD 0}"

/-- The fee of a transaction in the node's mempool, in sats, as the node computed it. -/
def Host.mempoolFee (h : Host) (txid : String) : IO Nat := do
  let fee := satsOf (((← h.json #["getmempoolentry", txid]).getObjValD "fees").getObjValD "base")
  if fee == 0 then failure s!"the node's mempool entry for {txid} has no fee"
  return fee

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
  let checksum : String ← field (← h.json #["getdescriptorinfo", b]) "checksum"
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
  let addresses ← h.json #["deriveaddresses", ← h.withChecksum (firstBranch (body descriptor)), s!"[{index},{index}]"]
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
  let list ← h.walletJson #["listdescriptors", toString priv] wallet
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
  let result ← h.walletJson #["importdescriptors", request.compress] c.wallet
  for r in (result.getArr?.toOption.getD #[]) do
    unless (r.getObjValAs? Bool "success").toOption.getD false do failure s!"importdescriptors: {r.compress}"

/-- The PSBT with this wallet's signatures added. -/
def Host.sign (h : Host) (c : CoreSigner) (psbt : String) : IO String := do
  field (← h.walletJson #["walletprocesspsbt", psbt, "true", "DEFAULT", "true", "false"] c.wallet) "psbt"

/-- The phone's recovery phrase restored on another device: a blank Core wallet on the seed of `entropy`, with
the app's receive and change branches and their private keys, that signs with its own libsecp256k1. -/
def Host.samePhrase (h : Host) (name : String) (entropy : ByteArray) : IO Unit := do
  let (.ok words) := Winnow.Keys.BIP39.mnemonic entropy | failure "no recovery phrase from this entropy"
  let (.ok master) := Winnow.Keys.HDKey.ofSeed (Winnow.Keys.BIP39.seed words) | failure "no master key from this seed"
  discard <| h.cli #["-named", "createwallet", s!"wallet_name={name}", "blank=true"]
  let branch (n : Nat) : IO Json := do
    let desc ← h.withChecksum s!"tr({master.serialized .testnet}/86h/1h/0h/{n}/*)"
    return Json.mkObj [("desc", Json.str desc), ("timestamp", "now"), ("range", Json.arr #[0, 50])]
  let result ← h.walletJson #["importdescriptors", (Json.arr #[← branch 0, ← branch 1]).compress] name
  for r in (result.getArr?.toOption.getD #[]) do
    unless (r.getObjValAs? Bool "success").toOption.getD false do failure s!"importdescriptors: {r.compress}"

/-- Everything the wallet holds, sent to `destination` at `rate` sat/vB: the transaction, in the node's mempool. -/
def Host.sweep (h : Host) (wallet destination : String) (rate : Nat) : IO String := do
  field (← h.walletJson #["-named", "sendall", s!"recipients=[\"{destination}\"]", s!"fee_rate={rate}"] wallet) "txid"

/-- One of the wallet's coins alone, sent to `destination` at `rate` sat/vB: the transaction, in the node's mempool. -/
def Host.sweepOneCoin (h : Host) (wallet destination : String) (rate : Nat) : IO String := do
  let some coin := ((← h.walletJson #["listunspent"] wallet).getArr?.toOption.bind (·[0]?)) | failure s!"{wallet} has no coin"
  let input := Json.arr #[Json.mkObj [("txid", coin.getObjValD "txid"), ("vout", coin.getObjValD "vout")]]
  field (← h.walletJson #["-named", "sendall", s!"recipients=[\"{destination}\"]", s!"fee_rate={rate}",
    s!"inputs={input.compress}"] wallet) "txid"

/-- The Core signers are done: their wallets unloaded. -/
def Host.unload (h : Host) (signers : List CoreSigner) : IO Unit := do
  for s in signers do discard <| h.cli #["unloadwallet", s.wallet]

/-! ## Person cards and SegWit v0 multisig accounts -/

/-- Extracts the raw `twinnowcard1p…` code from a person card JSON string. -/
def cardCodeOf (cardJson : String) : IO String := do
  match Winnow.PersonCard.decode cardJson with
  | .ok c =>
    match c.payTo with
    | some code => return code
    | none => failure s!"person card has no payTo code: {cardJson}"
  | .error e => failure s!"could not decode person card ({e.name}): {cardJson}"

/-- A SegWit v0 2-of-3 multisig account (`wsh(sortedmulti(2, FIXED, phoneKey, otherKey))`) backed by two
Bitcoin Core wallets: `watchWallet` (watch-only, builds funded PSBTs) and `serviceWallet` (holds the fixed
key's WIF and adds Core's ECDSA signature). -/
structure SegWitAccount where
  watchWallet : String
  serviceWallet : String
  descriptor : String

private def Host.importSegwitWallet (h : Host) (name descriptor : String) (privateKeys : Bool) : IO Unit := do
  discard <| h.cli #["-named", "createwallet", s!"wallet_name={name}", "blank=true", s!"disable_private_keys={!privateKeys}"]
  let withCs ← h.withChecksum descriptor
  let request := Json.arr #[Json.mkObj [("desc", Json.str withCs), ("active", Json.bool true),
    ("timestamp", Json.str "now"), ("range", Json.arr #[(0 : Nat), (19 : Nat)])]]
  let result ← h.walletJson #["importdescriptors", request.compress] name
  let imported := match result with
    | .arr rows => rows.all fun row => (row.getObjValAs? Bool "success").toOption == some true
    | _ => false
  unless imported do failure s!"Core did not import the descriptor into {name}: {result.compress}"

/-- Creates `watchWallet` and `serviceWallet` on the fixture node for `wsh(sortedmulti(2, FIXED, phoneKey,
otherKey))` with descriptor range `[0, 19]`, mirroring `BackendTest.segwitFlow`. -/
def Host.segwitAccount (h : Host) (tag phoneKey : String) : IO SegWitAccount := do
  let otherKey ← TestKit.keyExpression (← TestKit.master 0xB2)
  -- a regtest key, written here on purpose: it has never held anything and must never be used for anything else
  let fixedSecret := Winnow.sha256 s!"winnow journey fixed key {tag}".toUTF8
  let some fixedPublic := (Winnow.Keys.publicKeyOf fixedSecret).toOption
    | failure "could not derive the fixed public key"
  let wif := Winnow.Base58Check.encode ((ByteArray.mk #[0xEF] ++ fixedSecret).push 0x01)
  let descriptorWith (fixed : String) := s!"wsh(sortedmulti(2,{fixed},{phoneKey.trimAscii.copy},{otherKey}))"
  let rawDescriptor := descriptorWith (Winnow.hex fixedPublic)
  let watchWallet := s!"wsh-watch-{tag}"
  let serviceWallet := s!"wsh-service-{tag}"
  h.importSegwitWallet watchWallet rawDescriptor (privateKeys := false)
  h.importSegwitWallet serviceWallet (descriptorWith wif) (privateKeys := true)
  return { watchWallet, serviceWallet, descriptor := ← h.withChecksum rawDescriptor }

/-- The SegWit v0 descriptor's receive address at `index`, derived by the node. -/
def Host.deriveSegwitAddress (h : Host) (descriptor : String) (index : Nat) : IO String := do
  let single := (body descriptor).replace "<0;1>" "0"
  let withCs ← h.withChecksum single
  let addresses ← h.json #["deriveaddresses", withCs, s!"[{index},{index}]"]
  let some a := (strings addresses).head? | failure s!"the node derived no address from {descriptor}"
  return a

/-- `watchWallet` builds a funded PSBT paying `destination` `amountSats` (fee_rate 2, changePosition 1), and
`serviceWallet` signs it with the fixed key; returns `(signedPSBT, feeSats)`. -/
def Host.segwitBuildAndSign (h : Host) (acct : SegWitAccount) (destination : String) (amountSats : Nat) : IO (String × Nat) := do
  let outs := Json.arr #[Json.mkObj [(destination, Json.str (TestKit.Regtest.btc amountSats))]]
  let options := Json.mkObj [("fee_rate", (2 : Nat)), ("changePosition", (1 : Nat))]
  let built ← h.walletJson #["walletcreatefundedpsbt", "[]", outs.compress, "0", options.compress] acct.watchWallet
  let fee := satsOf (built.getObjValD "fee")
  if fee == 0 then failure s!"walletcreatefundedpsbt returned no fee: {built.compress}"
  let unsignedPsbt : String ← field built "psbt"
  let processed ← h.walletJson #["walletprocesspsbt", unsignedPsbt, "true", "DEFAULT", "true", "false"] acct.serviceWallet
  let signedPsbt : String ← field processed "psbt"
  return (signedPsbt, fee)

/-- Unloads both Core wallets created for a SegWit v0 multisig account. -/
def Host.unloadSegwit (h : Host) (acct : SegWitAccount) : IO Unit := do
  discard <| h.cli #["unloadwallet", acct.watchWallet]
  discard <| h.cli #["unloadwallet", acct.serviceWallet]

end WinnowJourneys
