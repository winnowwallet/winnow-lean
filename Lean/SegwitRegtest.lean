import Winnow
import Lean.Data.Json
import TestKit.Check
import TestKit.Fixtures
import TestKit.Regtest

/-! # SegWit v0 multisig accounts against Bitcoin Core, on regtest

The account is `wsh(sortedmulti(2, FIXED, OURS/<0;1>/*, OTHER/<0;1>/*))`: FIXED one compressed public key with
nothing derived from it, the other two extended keys. It is the wallet a key service and two people share:
FIXED stands for a key that can only sign with ECDSA and cannot derive (here its private half is in a Bitcoin
Core wallet, which signs where the service would); OURS is this wallet's; OTHER is another member's, in a
Bitcoin Core wallet of its own. A third Core wallet holds no private key at all and makes the PSBTs, as
whoever runs the account's node does.

What Core is asked to judge:

* the addresses: this wallet's, at the first indices of both chains, are the ones Core derives from the same
  descriptor;
* a spend Core's FIXED wallet signs first, this wallet reviews (the fee is the fee Core states), signs and
  finalizes: Core's mempool takes it and its chain confirms it. So Core's signature is one this wallet's
  verifier and DER reader accept, and this wallet's signature and witness are ones Core's script check accepts;
* a spend this wallet signs first and Core's OTHER wallet signs and finalizes: Core's finalizer takes this
  wallet's partial signature from the PSBT, and the chain confirms the result;
* a spend the two Core wallets sign and this wallet only finalizes: its transaction is byte for byte the one
  Core's own finalizer makes;
* this wallet's signature alone: Core's finalizer says the spend is not complete, and so does this wallet's.

Needs bitcoind and bitcoin-cli (`TestKit.Regtest.findTool`). Run from `Lean/`; `scripts/ci-regtest segwit`
runs it against the pinned release. Regtest only: it makes its own chain and its coins are worth nothing. -/

open Winnow Winnow.Keys Lean TestKit
open TestKit.Regtest (Node startNode btc)
open MultisigAccount (OutputCoordinate)

initialize nodeRef : IO.Ref (Option Node) ← IO.mkRef none

def node : IO Node := do
  let some n ← nodeRef.get | throw (IO.userError "no node")
  return n

def cli (args : Array String) (wallet : Option String := none) : IO String := do
  let n ← node
  match wallet with
  | some w => n.wallet args w
  | none => n.cli args

def cliJson (args : Array String) (wallet : Option String := none) : IO Json := do
  match Json.parse (← cli args wallet) with
  | .ok j => return j
  | .error e => throw (IO.userError s!"json {args}: {e}")

def jstr (j : Json) (k : String) : IO String := match j.getObjValAs? String k with
  | .ok s => pure s | .error e => throw (IO.userError s!"{k}: {e}")

/-- A BTC amount (8 decimals) as exact sats. -/
def sats (j : Json) : IO Int64 := do
  let .num n := j | throw (IO.userError "amount")
  unless n.exponent ≤ 8 do throw (IO.userError "amount precision")
  return Int64.ofInt (n.mantissa * 10 ^ (8 - n.exponent))

def hexOf (s : String) : IO ByteArray := match Wire.dataOfHex? s with
  | some b => pure b | none => throw (IO.userError s!"hex {s}")

def bank := "bank"
/-- Holds no private key: makes the PSBTs. -/
def watch := "watch"
/-- Holds FIXED's private half, standing in for a key service. -/
def service := "service"
/-- Holds OTHER's private half: another member. -/
def otherMember := "other"

def mine (blocks : Nat) : IO Unit := do
  discard <| cli #["generatetoaddress", toString blocks, ← cli #["getnewaddress", "", "bech32m"] bank]

/-- The fixed key's private half: a regtest key, written here on purpose. It has never held anything and must
never be used for anything else. -/
def fixedSecret : ByteArray := sha256 "winnow segwit-regtest fixed key".toUTF8

def wif (secret : ByteArray) : String := Base58Check.encode ((ByteArray.mk #[0xEF] ++ secret).push 0x01)

/-- A descriptor with the checksum Core gives it. -/
def checksummed (descriptor : String) : IO String := do
  return s!"{descriptor}#{← jstr (← cliJson #["getdescriptorinfo", descriptor]) "checksum"}"

/-- A blank Core wallet holding `descriptor`, receive and change. -/
def coreWallet (name descriptor : String) (privateKeys : Bool) : IO Unit := do
  discard <| cli #["-named", "createwallet", s!"wallet_name={name}", "blank=true", s!"disable_private_keys={!privateKeys}"]
  let request := Json.arr #[Json.mkObj [("desc", .str (← checksummed descriptor)), ("active", .bool true), ("timestamp", .str "now"),
    -- the node runs with a key pool of one (TestKit.Regtest): say how far to look
    ("range", Json.arr #[(0 : Nat), (19 : Nat)])]]
  let result ← cliJson #["importdescriptors", request.compress] name
  let imported := match result with
    | .arr rows => rows.all fun row => (row.getObjValAs? Bool "success").toOption == some true
    | _ => false
  unless imported do throw (IO.userError s!"Core did not import the descriptor into {name}: {result.compress}")

/-- An account key Core made, as `[fingerprint/84h/1h/0h]tprv…` and `[…]tpub…`: the external wpkh descriptor
of a fresh Core wallet, without its `wpkh(` and its `/0/*)#checksum`. -/
def coreAccountKey (wallet : String) : IO (String × String) := do
  discard <| cli #["-named", "createwallet", s!"wallet_name={wallet}"]
  let half (withPrivate : Bool) : IO String := do
    let listed ← cliJson #["listdescriptors", toString withPrivate] wallet
    let rows := (listed.getObjValAs? (Array Json) "descriptors").toOption.getD #[]
    for row in rows do
      let text := (row.getObjValAs? String "desc").toOption.getD ""
      if text.startsWith "wpkh(" && (row.getObjValAs? Bool "internal").toOption == some false then
        let inner := (text.drop 5).toString
        match inner.splitOn "/0/*)" with
        | key :: _ :: _ => return key
        | _ => pure ()
    throw (IO.userError s!"no wpkh descriptor in {wallet}")
  return (← half true, ← half false)

structure World where
  account : SegwitMultisigAccount
  ours : HDKey
  /-- Every (choice, index) below twenty, with its script: where a coin or an output of the account can be. -/
  places : Array (OutputCoordinate × ByteArray)

def World.owned (w : World) : Array OutputCoordinate := w.places.map (·.1)

/-- The account's unspent coins as Core's watching wallet lists them, each placed by its script. -/
def World.coins (w : World) : IO (Array WalletUTXO) := do
  let tip := (← (← node).height)
  let .arr rows ← cliJson #["listunspent", "0"] watch | throw (IO.userError "listunspent")
  rows.mapM fun row => do
    let txid := ByteArray.reverse (← hexOf (← jstr row "txid"))
    let vout := (row.getObjValAs? Nat "vout").toOption.getD 0
    let amount ← sats ((row.getObjVal? "amount").toOption.getD Json.null)
    let script ← hexOf (← jstr row "scriptPubKey")
    let confirmations := (row.getObjValAs? Nat "confirmations").toOption.getD 0
    let some (place, _) := w.places.find? (·.2 == script) | throw (IO.userError "Core lists a coin at no address of the account")
    return { txid, vout := vout.toUInt32, amount, scriptPubKey := script,
             chain := if place.choice == 1 then .change else .receive, index := place.index,
             height := if confirmations == 0 then 0 else (tip + 1 - confirmations).toUInt32 }

/-- A PSBT from Core's watching wallet paying `amount` sats to an address outside the account. -/
def fundedPSBT (amount : Nat) : IO (String × Json) := do
  let outside ← cli #["getnewaddress", "", "bech32m"] bank
  let outputs := Json.arr #[Json.mkObj [(outside, .str (btc amount))]]
  let options := Json.mkObj [("fee_rate", (2 : Nat)), ("changePosition", (1 : Nat))]
  let made ← cliJson #["walletcreatefundedpsbt", "[]", outputs.compress, "0", options.compress] watch
  return (← jstr made "psbt", made)

/-- Core's `walletprocesspsbt`: signs what the wallet can, without finalizing. -/
def coreSigns (wallet psbt : String) : IO String := do
  jstr (← cliJson #["walletprocesspsbt", psbt, "true", "DEFAULT", "true", "false"] wallet) "psbt"

def read (what text : String) : IO PSBT := needE what (·.name) (PSBT.ofBase64 text)

/-- Core's mempool takes `tx`, it is sent and mined, and the chain has it. -/
def confirms (name : String) (tx : Transaction) : IO Unit := do
  let raw := hex (tx.serialized true)
  let verdict ← cliJson #["testmempoolaccept", (Json.arr #[.str raw]).compress]
  let allowed := match verdict with
    | .arr #[row] => (row.getObjValAs? Bool "allowed").toOption == some true
    | _ => false
  check s!"{name}: Core's mempool accepts it" allowed (if allowed then "" else verdict.compress)
  unless allowed do return
  let sent ← cli #["sendrawtransaction", raw]
  check s!"{name}: its identifier is the one Core gives it" (sent == hex (ByteArray.reverse tx.txid))
  mine 1
  let confirmed ← cliJson #["gettransaction", sent] watch
  check s!"{name}: Core's chain confirms it" ((confirmed.getObjValAs? Nat "confirmations").toOption.getD 0 ≥ 1)

def run : TM Unit := do
  -- Keys: the fixed one, ours, and another member's from a Core wallet.
  let fixedPublic ← needE "the fixed key" (·.name) (publicKeyOf fixedSecret)
  let ours ← master 0xA1
  let oursKey ← bareKeyExpression ours
  let (otherPrivate, otherPublic) ← coreAccountKey "keys-other"
  let descriptorWith (fixed other : String) := s!"wsh(sortedmulti(2,{fixed},{oursKey}/<0;1>/*,{other}/<0;1>/*))"
  let descriptor := descriptorWith (hex fixedPublic) otherPublic
  let account ← need "this wallet reads the descriptor" (SegwitMultisigAccount.parse (← checksummed descriptor) .regtest)
  -- Core's checksum is of the text it is given, so it is asked about this wallet's own spelling of the paths
  let written := account.serialized
  check "the checksum this wallet writes is Core's"
    (written == (← checksummed (String.ofList (written.toList.take (written.length - 9))))) written
  coreWallet watch descriptor (privateKeys := false)
  coreWallet service (descriptorWith (wif fixedSecret) otherPublic) (privateKeys := true)
  coreWallet otherMember (descriptorWith (hex fixedPublic) otherPrivate) (privateKeys := true)
  -- Addresses: Core derives each chain from the descriptor with that chain's step in place of the pair.
  let mut places : Array (OutputCoordinate × ByteArray) := #[]
  for choice in [0:2] do
    let single := descriptor.replace "<0;1>" (toString choice)
    let theirs := match ← cliJson #["deriveaddresses", ← checksummed single, "[0,19]"] with
      | .arr rows => rows.filterMap fun (row : Json) => row.getStr?.toOption
      | _ => #[]
    let mut same := theirs.size == 20
    for index in [0:20] do
      let output ← need "an address" (account.derivedOutput index.toUInt32 choice)
      places := places.push ({ choice, index := index.toUInt32 }, output.scriptPubKey)
      same := same && theirs[index]? == some output.address
    check s!"{if choice == 0 then "receive" else "change"} addresses 0 to 19 are the ones Core derives" same
  let w : World := { account, ours, places }
  -- Coins: 1 BTC to receive address 0 and 0.5 BTC to receive address 3.
  for (index, amount) in [((0 : UInt32), 100_000_000), (3, 50_000_000)] do
    discard <| cli #["sendtoaddress", ← need "an address" (account.address index), btc amount] bank
  mine 1
  let coins ← w.coins
  check "Core's watching wallet sees both coins where this wallet puts them"
    (coins.size == 2 && coins.any (·.index == 0) && coins.any (·.index == 3) && coins.all (·.chain == .receive))
    s!"{coins.map fun coin => (coin.chain.rawValue, coin.index, coin.amount.toInt)}"
  let fixedPosition := 0
  let oursPosition := 1
  let otherPosition := 2

  -- 1. Core signs with the fixed key; this wallet reviews, signs and finalizes.
  let (made, details) ← fundedPSBT 60_000_000
  let tip := (← (← node).height).toUInt32
  let unsigned ← read "Core's PSBT" made
  let reviewed ← need "this wallet reviews Core's PSBT" (account.reviewSpend unsigned coins w.owned tip)
  check "the fee this wallet finds is the fee Core states" (reviewed.fee == (← sats ((details.getObjVal? "fee").toOption.getD Json.null)))
    s!"{reviewed.fee.toInt} sats"
  check "what leaves is the payment, and what returns is the change at the position Core chose"
    (reviewed.outputs.size == 2 && reviewed.outputs[0]!.amount == 60_000_000 && !reviewed.outputs[0]!.isAccountOwned &&
      reviewed.outputs[1]!.isAccountOwned)
  check "nobody has signed Core's PSBT" ((account.approvals unsigned coins).toOption == some #[])
  let byService ← read "the PSBT Core's fixed key signed" (← coreSigns service made)
  check "Core's signature with the fixed key is one this wallet counts"
    ((account.approvals byService coins).toOption == some #[fixedPosition])
  let both ← need "this wallet signs" (account.sign byService ours coins w.owned tip aux0)
  check "the fixed key and this wallet have signed" ((account.approvals both coins).toOption == some #[fixedPosition, oursPosition])
  let (_, first) ← need "this wallet finalizes" (account.finalizeSpend both coins w.owned tip)
  confirms "the fixed key and this wallet" first

  -- 2. This wallet signs first; Core's other member signs and Core finalizes. Another deposit first, and a
  -- payment of all but a little, so that the spend takes every coin: one at least from each chain.
  discard <| cli #["sendtoaddress", ← need "an address" (account.address 5), btc 30_000_000] bank
  mine 1
  let coins ← w.coins
  let tip := (← (← node).height).toUInt32
  check "the change came back to the account, on its change chain"
    (coins.any (·.chain == .change) && coins.any (·.chain == .receive) && coins.size ≥ 2)
  let balance := coins.foldl (fun total coin => total + coin.amount.toInt.toNat) 0
  let (made, _) ← fundedPSBT (balance - 100_000)
  let unsigned ← read "Core's second PSBT" made
  check "the second spend takes every coin the account has" (unsigned.inputs.size == coins.size) s!"{unsigned.inputs.size} of {coins.size}"
  let oursOnly ← need "this wallet signs first" (account.sign unsigned ours coins w.owned tip aux0)
  let exported ← needE "the PSBT as BIP174 version 0" (·.name) oursOnly.base64V0
  let alone ← cliJson #["finalizepsbt", exported]
  check "this wallet's signature alone: Core's finalizer says the spend is not complete"
    ((alone.getObjValAs? Bool "complete").toOption == some false)
  refused "and so does this wallet's" (account.finalizeSpend oursOnly coins w.owned tip) "missingField"
  let withOther ← coreSigns otherMember exported
  check "this wallet and the other member have signed, by this wallet's count"
    ((account.approvals (← read "the PSBT the other member signed" withOther) coins).toOption == some #[oursPosition, otherPosition])
  let theirs ← cliJson #["finalizepsbt", withOther]
  check "Core's finalizer takes this wallet's signature and completes the spend"
    ((theirs.getObjValAs? Bool "complete").toOption == some true) theirs.compress
  let second ← needE "the transaction Core finalized" (·.name) (Transaction.decode (← hexOf (← jstr theirs "hex")))
  let (_, sameByUs) ← need "this wallet finalizes the same PSBT"
    (account.finalizeSpend (← read "the PSBT the other member signed" withOther) coins w.owned tip)
  check "this wallet's finalizer makes the same transaction, byte for byte"
    (sameByUs.serialized true == second.serialized true)
  confirms "this wallet and the other member" second

  -- 3. The two Core wallets sign; this wallet signs nothing and finalizes.
  discard <| cli #["sendtoaddress", ← need "an address" (account.address 7), btc 20_000_000] bank
  mine 1
  let coins ← w.coins
  let tip := (← (← node).height).toUInt32
  let (made, _) ← fundedPSBT 3_000_000
  let byCore ← coreSigns otherMember (← coreSigns service made)
  let signed ← read "the PSBT both Core wallets signed" byCore
  check "the fixed key and the other member have signed, by this wallet's count"
    ((account.approvals signed coins).toOption == some #[fixedPosition, otherPosition])
  let (_, third) ← need "this wallet finalizes what it did not sign" (account.finalizeSpend signed coins w.owned tip)
  let theirs ← cliJson #["finalizepsbt", byCore]
  check "its transaction is the one Core's finalizer makes, byte for byte"
    ((theirs.getObjValAs? String "hex").toOption == some (hex (third.serialized true)))
  confirms "the fixed key and the other member" third
  -- and all three: the witness still carries two signatures
  let coins ← w.coins
  let tip := (← (← node).height).toUInt32
  let (made, _) ← fundedPSBT 1_000_000
  let byAll ← need "this wallet signs after both"
    (account.sign (← read "the PSBT both signed" (← coreSigns otherMember (← coreSigns service made))) ours coins w.owned tip aux0)
  check "all three have signed" ((account.approvals byAll coins).toOption == some #[fixedPosition, oursPosition, otherPosition])
  let (_, fourth) ← need "this wallet finalizes three signatures" (account.finalizeSpend byAll coins w.owned tip)
  check "the witness carries two signatures and the script" (fourth.inputs.all (·.witness.size == 4))
  confirms "all three" fourth

def main : IO UInt32 := runMain "segwit-regtest" (progress := true) do
  let dir := s!"/tmp/winnow-segwit-core-{← IO.monoNanosNow}"
  let n ← startNode dir (filters := false)
  nodeRef.set (some n)
  try
    discard <| cli #["-named", "createwallet", s!"wallet_name={bank}"]
    mine 101
    runTest "segwit multisig with Bitcoin Core" run
  finally
    n.stop
    discard <| (IO.FS.removeDirAll dir).toBaseIO
