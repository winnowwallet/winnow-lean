import Winnow
import TestKit.Check
import TestKit.Fixtures
import TestKit.Regtest

/-! `card-regtest`: a card per person (issue #94) against a regtest Bitcoin Core, which is the payer.

The wallet issues a card. Core's wallet pays the addresses that card's text derives, replaces one payment
before it confirms, and a block of them is reorganised away and mined again. The wallet finds each payment
through BIP157/158 basic filters as Core serves them, verifies the block, and credits each once. Then the two
halves of "only the issuer spends": one transaction spending a card's coin, signed with what the payer holds
(Core refuses it) and with the card's private key plus the tweak (Core takes it). Last, the same phrase on a
wallet with no file: its frontier is already past every payment, it records the cards it could have issued,
scans back over the same filters, finds the coins and spends one.

Run from `Lean/` (`scripts/ci-regtest cards` uses the pinned Core). -/

open Winnow Winnow.Net Winnow.IO Winnow.Keys Lean TestKit TestKit.Regtest

def regtest := NetworkParams.regtest

def runNet {α} (what : String) (x : NetM α) : IO α := do
  match ← x.attempt with
  | .ok a => return a
  | .error e => throw (IO.userError s!"{what}: {e}")

def jsonStr (j : Json) (k : String) : String := (j.getObjValAs? String k).toOption.getD ""

def TestKit.Regtest.Node.endpoint (n : Node) : PeerEndpoint := { host := "127.0.0.1", port := n.p2p }

def entropy : ByteArray := ByteArray.mk (Array.replicate 16 0x94)
def zeros32 : ByteArray := ByteArray.mk (Array.replicate 32 0)

/-- A wallet step inside a scan's callback: a failure is kept for the check after the scan. -/
def walletStep (problems : IO.Ref (Array String)) (what : String) (x : WM Unit) : NetM Unit := do
  match ← x.run.toBaseIO with
  | .ok (.ok ()) => pure ()
  | .ok (.error e) => problems.modify (·.push s!"{what}: {e.name}")
  | .error e => problems.modify (·.push s!"{what}: {e}")

/-- One forward pass: headers, filters for the wallet's scripts, each matched block applied, the frontier
recorded. A reorg rolls the wallet back first, as the app does. -/
def syncWallet (w : Wallet) (fs : FilterSyncIO) (problems : IO.Ref (Array String)) (n : Node) : IO Unit := do
  n.waitFilterIndex
  let scripts ← need "watch scripts" w.watchScripts
  runNet "filter sync" (fs.sync scripts
    (onReorg := some fun fork => walletStep problems "roll back" (w.rollBack fork))
    (onMatch := fun m => walletStep problems "apply" (discard (w.apply m))))
  need "record the frontier" (w.recordScanHeight (← fs.nextScanHeight))

/-- What the payer does with a card's text: the address of payment `i`. -/
def payerAddress (codeText : String) (i : UInt32) : IO (String × ByteArray) := do
  let code ← needE "the payer reads the code" (·.name) (CardCode.decode codeText (some CardCode.regtestHRP))
  let script ← needE "the payer derives the script" (·.name) (CardKeys.scriptPubKey code i)
  let some address := AddressDecoder.address script .regtest | throw (IO.userError "no address for the script")
  return (address, script)

def scriptOf (n : Node) (address : String) : IO ByteArray := do
  let info ← IO.ofExcept (Json.parse (← n.wallet #["getaddressinfo", address]))
  let some script := ofHex? (jsonStr info "scriptPubKey") | throw (IO.userError "getaddressinfo scriptPubKey")
  return script

/-- Core's verdict on a transaction it is not asked to keep: whether it would take it, and why not. -/
def mempoolVerdict (n : Node) (tx : Transaction) : IO (Bool × String) := do
  let answer ← n.json #["testmempoolaccept", s!"[\"{hex (tx.serialized true)}\"]"]
  let some first := (answer.getArr?.toOption.bind (·[0]?)) | throw (IO.userError "testmempoolaccept answered nothing")
  return ((first.getObjValAs? Bool "allowed").toOption.getD false, jsonStr first "reject-reason")

def cardCoins (w : Wallet) : IO (Array (UInt32 × Int64)) := do
  return (((← w.utxos).filter (·.card.isSome)).map fun u => (u.index, u.amount)).qsort (·.1 < ·.1)

def cardChecks (n : Node) : IO Unit := do
  say s!"node: bitcoind regtest pid {n.pid}, p2p {n.p2p}"
  discard <| n.cli #["createwallet", "w"]
  let mineAddress ← n.wallet #["getnewaddress"]
  n.mine 101 mineAddress
  let pool ← PeerPool.new regtest (manualPeers := #[n.endpoint]) (seedResolver := some { lookup := fun _ _ _ => pure #[] })
  pool.start
  check "the node is the wallet's one peer" (← waitUntil 10_000 (do return (← pool.connectedPeers).size == 1))
  let store ← runNet "headers" (HeaderStore.open regtest none)
  let problems ← IO.mkRef (#[] : Array String)

  -- the issuer
  let issuedAt := (← n.height).toUInt32
  let keys ← IO.mkRef {}
  let w ← need "create" (Wallet.create .regtest (inMemoryKeyStore keys) none (some entropy) issuedAt)
  let fs ← runNet "filters" (FilterSyncIO.new pool store issuedAt none)
  let (cardIndex, code) ← need "issue a card" w.issueCard
  let codeText ← needE "encode" (·.name) code.encoded
  check "a regtest card" (cardIndex == 0 && codeText.startsWith "rwnc1")

  -- Core pays payments 0 and 1 of the card
  let (address0, script0) ← payerAddress codeText 0
  let (address1, _) ← payerAddress codeText 1
  let paid0 ← n.wallet #["sendtoaddress", address0, btc 50_000_000]
  let paid1 ← n.wallet #["sendtoaddress", address1, btc 25_000_000]
  n.mine 1 mineAddress
  let paidHeight := (← n.height).toUInt32
  syncWallet w fs problems n
  check "both payments are found through the node's basic filters and credited"
    ((← cardCoins w) == #[(0, 50_000_000), (1, 25_000_000)] && (← w.balance) == 75_000_000) s!"{← cardCoins w}"
  check "each at its block, under its own transaction"
    (((← w.utxos).map fun (u : WalletUTXO) => (Winnow.displayHex u.txid, u.height)).all fun (txid, height) =>
      height == paidHeight && (txid == paid0 || txid == paid1))
  check "the card's cursor is past them" ((← w.cards).map (·.nextIndex) == #[2])

  -- a payment Core replaces before it confirms
  let (address2, _) ← payerAddress codeText 2
  let original ← n.wallet #["sendtoaddress", address2, btc 10_000_000, "", "", "false", "true"]
  let replacement := jsonStr (← n.walletJson #["bumpfee", original]) "txid"
  check "Core replaced its payment" (replacement.length == 64 && replacement != original && (← n.mempool) == #[replacement])
  n.mine 1 mineAddress
  syncWallet w fs problems n
  check "a replaced payment is credited once, as the transaction that confirmed"
    ((← cardCoins w) == #[(0, 50_000_000), (1, 25_000_000), (2, 10_000_000)] &&
     ((← w.utxos).filter (·.index == 2)).map (fun (u : WalletUTXO) => Winnow.displayHex u.txid) == #[replacement])

  -- the block that paid it is reorganised away; the payment confirms again in another block
  let replacedHeight ← n.height
  let orphaned ← n.cli #["getblockhash", toString replacedHeight]
  discard <| n.cli #["invalidateblock", orphaned]
  check "the reorganised payment is back in the node's mempool" ((← n.mempool) == #[replacement])
  -- to another script: the same coinbase in the same second would be the block just invalidated
  n.mineElsewhere 2
  syncWallet w fs problems n
  let found := (← w.history).find? fun (e : HistoryEntry) => Winnow.displayHex e.txid == replacement
  check "after the reorg the payment is credited once, in the block that now holds it"
    ((← w.balance) == 85_000_000 && ((← cardCoins w).map (·.1)) == #[0, 1, 2] &&
     (found.bind (·.blockHash)).map Winnow.displayHex == some (← n.cli #["getblockhash", toString replacedHeight]) &&
     (found.bind (·.blockHash)).map Winnow.displayHex != some orphaned)

  -- only the issuer spends: one transaction, two signers
  let nodeScript ← scriptOf n (← n.wallet #["getnewaddress", "", "bech32m"])
  let some coin := (← w.utxos).find? (fun u => u.card == some 0 && u.index == 0) | throw (IO.userError "no coin at payment 0")
  check "the coin is at the script the payer derived" (coin.scriptPubKey == script0)
  let unsigned ← needE "build" (·.name)
    (TransactionBuilder.build #[coin.outpoint] #[{ amount := coin.amount - 1_000, scriptPubKey := nodeScript }])
  let signedBy (secret : ByteArray) : IO Transaction := do
    let witness ← needE "sign" (fun _ => "signing failed") (Signer.witness unsigned 0 #[coin.spentOutput] secret (auxiliaryRand := zeros32))
    return { unsigned with inputs := unsigned.inputs.modify 0 fun i => { i with witness } }
  let tweak ← needE "tweak" (·.name) (CardKeys.tweak code 0)
  let (allowed, reason) ← mempoolVerdict n (← signedBy tweak)
  check "signed with the tweak, which is all the payer holds: Core refuses it" (!allowed && !reason.isEmpty) reason
  -- the card's private key, from the phrase and not from the wallet
  let words ← needE "mnemonic" (fun _ => "bip39") (BIP39.mnemonic entropy)
  let node ← needE "node" (·.name) (do (← HDKey.ofSeed (BIP39.seed words)).derived "m/86'/1'/0'/2'/0'")
  let some cardSecret := node.privateKey | throw (IO.userError "no private key")
  let (allowed, reason) ← mempoolVerdict n (← signedBy cardSecret)
  check "signed with the card's private key alone: Core refuses it" (!allowed) reason
  let issuerSecret ← needE "sum" (·.name) (do return Secp.toBE32 (← privateAdd (← secretOf cardSecret) tweak))
  let (allowed, reason) ← mempoolVerdict n (← signedBy issuerSecret)
  check "signed with the card's private key plus the tweak: Core takes it" allowed reason

  -- the same phrase, no wallet file: the frontier is already past every payment
  let tip := (← n.height).toUInt32
  let rebuilt ← need "rebuild" (Wallet.create .regtest (inMemoryKeyStore (← IO.mkRef {})) none (some entropy) tip)
  let forward ← runNet "filters" (FilterSyncIO.new pool store tip none)
  syncWallet rebuilt forward problems n
  check "a wallet rebuilt from the phrase starts past the payments and has found none"
    ((← rebuilt.nextScanHeight) > paidHeight && (← rebuilt.balance) == 0 && (← rebuilt.cards).isEmpty)
  let back ← runNet "range filters" (FilterSyncIO.new pool store 0 none)
  let mut passes := 0
  let mut complete := true
  while (← need "restore cards" rebuilt.restoreCards) do
    passes := passes + 1
    let outcome ← runNet "scan back" (back.scanRange issuedAt tip (← need "watch scripts" rebuilt.watchScripts)
      (onMatch := fun m => walletStep problems "apply" (discard (rebuilt.apply m))))
    complete := complete && outcome.isComplete
  check "it scans back over the same filters, twice: the cards it could have issued, then further"
    (passes == 2 && complete && (← rebuilt.cards).size == Wallet.cardLookahead.toNat + 1) s!"{passes} passes"
  check "and holds the coins the issuing wallet holds"
    ((← cardCoins rebuilt) == (← cardCoins w) && (← rebuilt.balance) == 85_000_000) s!"{← cardCoins rebuilt}"
  check "its card 0 is the card that was issued" ((← (rebuilt.cardCode 0).run).toOption == some code)
  check "the forward frontier did not move for the scan back" ((← forward.nextScanHeight) == tip + 1)

  -- the rebuilt wallet spends everything; the issuing wallet sees its coins go
  let prepared ← need "send" (rebuilt.buildSend #[{ amount := 84_000_000, scriptPubKey := nodeScript }] 2 tip)
  let spend := prepared.built.transaction
  check "the spend takes all three of the card's coins" (spend.inputs.size == 3)
  let sent ← n.cli #["sendrawtransaction", hex (spend.serialized true)]
  check "Core takes the rebuilt wallet's spend of the card's coins" (sent == Winnow.displayHex spend.txid) sent
  need "commit" (rebuilt.commit prepared)
  n.mine 1 mineAddress
  syncWallet rebuilt forward problems n
  syncWallet w fs problems n
  let change := prepared.built.changeAmount.getD 0
  check "confirmed: the rebuilt wallet holds the change" ((← rebuilt.balance) == change && (← rebuilt.state).pendingSends.isEmpty)
    s!"{← rebuilt.balance}"
  check "and the issuing wallet, which did not make the spend, sees its card's coins spent and the change arrive"
    ((← cardCoins w).isEmpty && (← w.balance) == change) s!"{← w.balance}"
  check "no wallet step failed inside a scan" (← problems.get).isEmpty s!"{← problems.get}"
  pool.stop

def main (_args : List String) : IO UInt32 := runMain "card-regtest" (progress := true) do
  let tmp ← IO.FS.createTempDir
  try
    withNode tmp.toString cardChecks
  finally
    try IO.FS.removeDirAll tmp catch _ => pure ()
