import Winnow
import Lean.Data.Json

/-! `multisig-test`: upstream 1cf93fb's multisig tests, ported.

* `Tests/WalletCoreTests/MultisigAccountTests.swift` (all 16 tests but the bundle one, which is in
  `bundleAccounts` here too),
* `Tests/WalletCoreTests/TimelockedMultisigTests.swift` (all 10),
* the script-path half of `SighashBIP341Tests.swift` over `bip341-scriptpath-test-vectors.json` (shape,
  sighash, signatures, BIP387 witness), since `Multisig.parse` and `Signer.multisigWitness` changed,
* `core-timelocked-multisig.json` (Bitcoin Core 31.1's checksums and addresses),
* upstream d2ca878's `NestedMultisigTests.swift` (#256): all ten tests without a Ledger here, the three
  with simulated Ledgers in `ledger-test`,
* upstream d2ca878's `HistoryLedgerTests.swift` (#259, all four) and `ImportBundleTests.signers`, with
  the account record's spend records (an old record encoding byte for byte, the v0 draft) and the new
  bundle bounds,
* upstream d2ca878's `WalletCursorTests.swift` (all six).

Fixtures as `Tests/Support/TestKeys.swift`: masters from BIP39 over 16 repeated bytes (0xA1, 0xB2, 0xC3;
0x0D a stranger; 0xD4–0xD6 recovery keys), signet keys at m/86'/1'/0', `testChainTip` 840 000, BIP340
auxiliary randomness zero. Run from `Lean/` (reads `Vectors/`). Exits 1 on any failure. -/

open Winnow Keys
open Tx (BitcoinNetwork)
open MultisigAccount (OutputCoordinate SpendPath RecoveryPlan)

initialize passed : IO.Ref Nat ← IO.mkRef 0
initialize failures : IO.Ref (Array String) ← IO.mkRef #[]

abbrev TM := ExceptT String IO

def check (name : String) (ok : Bool) (detail : String := "") : TM Unit := do
  if ok then passed.modify (· + 1)
  else
    failures.modify (·.push name)
    IO.println s!"FAIL {name}{if detail.isEmpty then "" else ": " ++ detail}"

def need {α} (name : String) (r : MAM α) : TM α :=
  match r with
  | .ok a => pure a
  | .error e => throw s!"{name}: {e.name}{match e with | .account a => " (" ++ a.description ++ ")" | _ => ""}"

def needE {ε α} (name : String) (render : ε → String) (r : Except ε α) : TM α :=
  match r with | .ok a => pure a | .error e => throw s!"{name}: {render e}"

/-- Expects a failure; `kind` the case name, `account` an account error (any case), or neither (any). -/
def refused {α} (name : String) (r : MAM α) (kind : Option String := none) (account : Bool := false) : TM Unit :=
  match r with
  | .ok _ => check name false "accepted"
  | .error e =>
    let isAccount := match e with | .account _ => true | _ => false
    check name ((kind.map (· == e.name)).getD true && (!account || isAccount)) s!"got {e.name}"

def refusedWith {α} (name : String) (r : MAM α) (expected : MultisigAccountError) : TM Unit :=
  match r with
  | .ok _ => check name false "accepted"
  | .error (.account e) => check name (e == expected) s!"got {e.description}"
  | .error e => check name false s!"got {e.name}"

def runTest (name : String) (t : TM Unit) : IO Unit := do
  let start ← IO.monoMsNow
  match ← t.run with
  | .ok () => pure ()
  | .error msg =>
    failures.modify (·.push name)
    IO.println s!"FAIL {name} (aborted): {msg}"
  IO.println s!"  {name}: {(← IO.monoMsNow) - start} ms"
  (← IO.getStdout).flush

/-! ## Fixtures -/

def testChainTip : UInt32 := 840_000
def aux0 : ByteArray := ByteArray.mk (Array.replicate 32 0)
def destination : ByteArray := ByteArray.mk (#[0x51, 0x20] ++ Array.replicate 32 0x77)
def owned : Array OutputCoordinate := #[{ choice := 1, index := 0 }]

initialize masterCache : IO.Ref (Array (UInt8 × HDKey)) ← IO.mkRef #[]

/-- BIP39 seeds take 2048 PBKDF2 rounds, so each master is made once. -/
def master (entropyByte : UInt8) : TM HDKey := do
  if let some (_, m) := (← masterCache.get).find? (·.1 == entropyByte) then return m
  let words ← needE "mnemonic" (fun _ => "bip39") (BIP39.mnemonic (ByteArray.mk (Array.replicate 16 entropyByte)))
  let m ← needE "master" (·.name) (HDKey.ofSeed (BIP39.seed words))
  masterCache.modify (·.push (entropyByte, m))
  return m

def masters : TM (Array HDKey) := #[0xA1, 0xB2, 0xC3].mapM master

def accountKeyOf (m : HDKey) : TM HDKey := needE "account key" (·.name) (m.derived "m/86'/1'/0'")

def bareKeyExpression (m : HDKey) : TM String := do
  let account ← accountKeyOf m
  return s!"[{Descriptor.hex8 m.fingerprint}/86'/1'/0']{account.neutered.serialized .testnet}"

def keyExpression (m : HDKey) : TM String := return (← bareKeyExpression m) ++ "/<0;1>/*"

/-- `masters` in the order the account lists their keys. -/
def inSignerOrder (ms : Array HDKey) (a : MultisigAccount) : TM (Array HDKey) := do
  let listed := a.signers.filterMap fun s => (MultisigAccount.extendedKey? s).map (·.1.publicKey)
  let keyed ← ms.mapM fun m => do
    let pub := (← accountKeyOf m).publicKey
    return (m, (listed.findIdx? (· == pub)).getD 1_000_000)
  return (keyed.toList.mergeSort (fun a b => a.2 ≤ b.2)).toArray.map (·.1)

def accountWith (threshold : Int := 2) (count : Nat := 3) : TM (MultisigAccount × Array HDKey) := do
  let ms := (← masters).extract 0 count
  let d ← need "descriptor" (MultisigAccount.makeDescriptor threshold (← ms.mapM keyExpression) none .signet)
  let a ← need "account" (MultisigAccount.make d .signet)
  return (a, ← inSignerOrder ms a)

def funding (a : MultisigAccount) (amount : Int64) (chain : AddressChain := .receive) (index : UInt32 := 0)
    (height : UInt32 := 100) (txidByte : UInt8 := 0x5A) : TM WalletUTXO := do
  return { txid := ByteArray.mk (Array.replicate 32 txidByte), vout := 0, amount,
           scriptPubKey := ← need "spk" (a.scriptPubKey index chain.rawValue), chain, index, height }

def spend (a : MultisigAccount) (u : WalletUTXO) (amount : Int64 := 50_000) (tip : UInt32 := testChainTip)
    (path : SpendPath := .signers) : MAM PSBT :=
  a.createSpend #[u] #[{ amount, scriptPubKey := destination }] 0 2 tip path (0.5, 0.5)

def sign (a : MultisigAccount) (p : PSBT) (key : HDKey) (known : Array WalletUTXO) (tip : UInt32 := testChainTip) :
    MAM PSBT := a.sign p key known owned tip aux0

def finalize (a : MultisigAccount) (p : PSBT) (known : Array WalletUTXO) (tip : UInt32 := testChainTip) :
    MAM Transaction := return (← a.finalizeSpend p known owned tip).2

def sameP (a b : PSBT) : Bool := a.serialized == b.serialized

def suffixBytes (b : ByteArray) (n : Nat) : ByteArray := b.extract (b.size - n) b.size

/-- BIP342 multi_a validation replayed for input 0 of a finalized spend: the control block commits the
leaf to the spent output key, then each witness item is verified against its key. The valid count. -/
def verifiedSignatures (tx : Transaction) (spent : SighashBIP341.SpentOutput) : TM Nat := do
  let some input := tx.inputs[0]? | throw "no input"
  let w := input.witness
  unless w.size ≥ 2 do throw "short witness"
  let leafScript := w[w.size - 2]!
  let cb ← needE "control block" (·.name) (Taproot.ControlBlock.parse w[w.size - 1]!)
  let root := cb.path.foldl Taproot.branchHash (Taproot.leafHash cb.leafVersion leafScript)
  let (outputKey, parity) ← needE "tweak" (·.name) (Taproot.tweakedOutputKey cb.internalKey (some root))
  check "replay: output key" (outputKey == suffixBytes spent.scriptPubKey 32)
  check "replay: parity" (cb.outputKeyParity == parity)
  let some (_, keys) := Multisig.parse ⟨leafScript⟩ | throw "leaf does not parse"
  let sighash ← needE "sighash" (·.name)
    (SighashBIP341.sighash tx 0 #[spent] .default (some (SighashBIP341.ScriptPath.ofLeaf ⟨leafScript⟩)))
  let mut valid := 0
  for h : position in [0:keys.size] do
    let item := w[keys.size - 1 - position]!
    if !item.isEmpty then
      if (schnorrVerify keys[position] sighash (item.extract 0 64)).toOption.getD false then valid := valid + 1
  return valid

def witnessSize (w : Array ByteArray) : Nat :=
  let compact := fun (v : Nat) => if v < 0xFD then 1 else 3
  compact w.size + w.foldl (fun t x => t + compact x.size + x.size) 0

def hexOf (s : String) : TM ByteArray := match Wire.dataOfHex? s with | some b => pure b | none => throw s!"hex {s}"

/-! ## MultisigAccountTests -/

def twoOfThree : TM Unit := do
  let (account, ms) ← accountWith
  check "2of3: threshold" (account.threshold == 2)
  check "2of3: signers" (account.signers.size == 3)
  let address ← need "address" (account.address 0)
  check "2of3: tb1p address" (address.startsWith "tb1p")
  check "2of3: watch scripts" ((← need "watch" (account.watchScripts 2)).size == 4)
  let reparsed ← need "reparse" (MultisigAccount.parse account.descriptor.serialized .signet)
  check "2of3: reparsed address" ((← need "address" (reparsed.address 0)) == address)
  let utxo ← funding account 100_000
  let created ← need "create" (spend account utxo)
  let input := created.inputs[0]!
  let (internal0, _) ← need "taproot" (MultisigAccount.lift (·.name) (account.descriptor.resolvedTaproot 0 0))
  let (internal1, _) ← need "taproot" (MultisigAccount.lift (·.name) (account.descriptor.resolvedTaproot 0 1))
  check "2of3: input internal key" (input.tapInternalKey == some internal0)
  check "2of3: one leaf" (input.tapLeafScripts.size == 1)
  check "2of3: no signatures" input.tapScriptSignatures.isEmpty
  check "2of3: three origins" (input.tapBIP32Derivation.size == 3)
  check "2of3: one leaf hash each" (input.tapBIP32Derivation.all (·.2.leafHashes.size == 1))
  let changeScript ← need "spk" (account.scriptPubKey 0 1)
  let some change := created.outputs.find? (·.script == some changeScript) | throw "no change output"
  check "2of3: change tap tree" ((change.tapTree.map (·.size)) == some 1)
  check "2of3: change internal key" (change.tapInternalKey == some internal1)
  check "2of3: change origins" (change.tapBIP32Derivation.size == 3)
  let base64 := created.base64
  check "2of3: base64 round trip" (match PSBT.ofBase64 base64 with | .ok p => sameP p created | .error _ => false)
  let wrongCoin := { utxo with amount := utxo.amount + 1 }
  refused "2of3: review refuses a wrong coin" (sign account created ms[0]! #[wrongCoin]) (account := true)
  let partialC ← need "sign C" (sign account created ms[2]! #[utxo])
  let partialA ← need "sign A" (sign account created ms[0]! #[utxo])
  check "2of3: one signature" (partialA.inputs[0]!.tapScriptSignatures.size == 1)
  check "2of3: approvals A" ((← need "approvals" (account.approvals partialA #[utxo])) == #[0])
  let combined ← need "combine" (MultisigAccount.lift (·.name) (partialC.combined #[partialA]))
  check "2of3: approvals A+C" ((← need "approvals" (account.approvals combined #[utxo])) == #[0, 2])
  -- A hostile combiner appends an unrelated leaf.
  let some realLeaf := combined.inputs[0]!.tapLeafScripts[0]? | throw "no leaf"
  let bogus : PSBT.TapLeafScript :=
    { controlBlock := { leafVersion := realLeaf.leafVersion, outputKeyParity := false,
                        internalKey := ByteArray.mk (Array.replicate 32 0), path := #[] },
      script := realLeaf.script, leafVersion := realLeaf.leafVersion }
  let hostile := combined.modifyInput 0 (·.setTapLeafScripts #[bogus, realLeaf])
  refused "2of3: hostile leaf refused" (finalize account hostile #[utxo]) (account := true)
  let generic ← need "generic finalize" (MultisigAccount.lift (·.name) hostile.finalize)
  let genericTx ← need "extract" (MultisigAccount.lift (·.name) generic.extractedTransaction)
  check "2of3: generic finalizer picks the committing leaf" ((← verifiedSignatures genericTx utxo.spentOutput) == 2)
  let signed ← need "finalize" (finalize account combined #[utxo])
  check "2of3: two valid signatures" ((← verifiedSignatures signed utxo.spentOutput) == 2)
  let witness := signed.inputs[0]!.witness
  check "2of3: witness items" (witness.size == 5)
  let estimate ← need "witness bytes" (account.witnessBytesPerInput)
  check "2of3: estimate covers witness" (estimate ≥ (1 + witness.foldl (fun t x => t + 1 + x.size) 0 : Nat))

def everyPairCanSpend : TM Unit := do
  let (account, ms) ← accountWith
  let utxo ← funding account 100_000
  for (i, j) in [(0, 1), (0, 2), (1, 2)] do
    let psbt ← need "sign" (do sign account (← spend account utxo) ms[i]! #[utxo])
    refused s!"pairs: {i} alone cannot finalize" (finalize account psbt #[utxo])
    let both ← need "sign" (sign account psbt ms[j]! #[utxo])
    let tx ← need "finalize" (finalize account both #[utxo])
    check s!"pairs: {i}+{j}" ((← verifiedSignatures tx utxo.spentOutput) == 2)

def threeOfThree : TM Unit := do
  let (account, ms) ← accountWith 3
  let utxo ← funding account 100_000
  let mut psbt ← need "create" (spend account utxo)
  for m in ms.extract 0 2 do psbt ← need "sign" (sign account psbt m #[utxo])
  refused "3of3: two refused" (finalize account psbt #[utxo])
  psbt ← need "sign" (sign account psbt ms[2]! #[utxo])
  let tx ← need "finalize" (finalize account psbt #[utxo])
  check "3of3: three valid" ((← verifiedSignatures tx utxo.spentOutput) == 3)

def accountKeySigning : TM Unit := do
  let (account, ms) ← accountWith
  let accountKey ← accountKeyOf ms[1]!
  check "account key: hasSigner" (account.hasSigner accountKey)
  check "account key: includes" (account.includes accountKey.neutered)
  let stranger ← master 0x0D
  check "account key: stranger" (!account.hasSigner stranger)
  let utxo ← funding account 100_000 .change 7
  let psbt ← need "sign" (do sign account (← spend account utxo) accountKey #[utxo])
  check "account key: approvals" ((← need "approvals" (account.approvals psbt #[utxo])) == #[1])
  refusedWith "account key: stranger noSignerKey" (sign account psbt stranger #[utxo]) (.noSignerKey 0)

def forgedApprovalNotCounted : TM Unit := do
  let (account, ms) ← accountWith
  let utxo ← funding account 100_000
  let psbt ← need "sign" (do sign account (← spend account utxo) ms[0]! #[utxo])
  let leafHash := psbt.inputs[0]!.tapLeafScripts[0]!.leafHash
  let two ← need "pub" (MultisigAccount.lift (·.name) (Descriptor.publicKey account.signers[2]! 0 0))
  let forged := psbt.modifyInput 0 fun i =>
    i.setTapScriptSignatures (i.tapScriptSignatures.push
      ({ publicKey := two.extract 1 33, leafHash }, ByteArray.mk (Array.replicate 64 0x42)))
  check "forged: approvals" ((← need "approvals" (account.approvals forged #[utxo])) == #[0])
  refused "forged: finalize refused" (finalize account forged #[utxo])

def permutations : List (List Nat) := [[0, 1, 2], [0, 2, 1], [1, 0, 2], [1, 2, 0], [2, 0, 1], [2, 1, 0]]

def signerOrderDoesNotMatter : TM Unit := do
  let expressions ← (← masters).mapM keyExpression
  let built ← permutations.mapM fun order =>
    need "descriptor" (MultisigAccount.makeDescriptor 2 (order.toArray.map (expressions[·]!)) none .signet)
  let texts := built.map (·.serialized)
  check "order: one descriptor" (texts.all (· == texts.head!))
  let account ← need "account" (MultisigAccount.make built.head! .signet)
  let reversed := expressions.reverse
  let leaf := s!"sortedmulti_a(2,{",".intercalate reversed.toList})"
  let draft ← needE "draft" (·.name) (Descriptor.parse s!"tr({hex Taproot.unspendableInternalKey},{leaf})")
  let olderKey ← need "nums" (MultisigAccount.unspendableKeyExpression (draft.allKeys.extract 1 draft.allKeys.size) .signet)
  let older ← need "older" (MultisigAccount.parse s!"tr({olderKey},{leaf})" .signet)
  check "order: older descriptor differs" (older.descriptor.serialized != account.descriptor.serialized)
  check "order: older addresses differ" ((← need "a" (older.address 0)) != (← need "a" (account.address 0)))
  let reparsed ← need "reparse" (MultisigAccount.parse older.descriptor.serialized .signet)
  check "order: older keeps its addresses" ((← need "a" (reparsed.address 0)) == (← need "a" (older.address 0)))

def changeByScriptOnly : TM Unit := do
  let (account, _) ← accountWith
  let utxo ← funding account 100_000
  let psbt ← need "create" (spend account utxo)
  let review ← need "review" (account.reviewSpend psbt #[utxo] owned testChainTip)
  check "change: one owned" ((review.outputs.filter (·.isAccountOwned)).size == 1)
  check "change: fee" (review.fee == review.inputTotal - review.outputTotal)
  let unowned ← need "review" (account.reviewSpend psbt #[utxo] #[] testChainTip)
  check "change: none owned without coordinates" (unowned.outputs.all (!·.isAccountOwned))
  let changeScript ← need "spk" (account.scriptPubKey 0 1)
  let some changeIndex := psbt.outputs.findIdx? (·.script == some changeScript) | throw "no change"
  let paymentIndex := 1 - changeIndex
  let derivation := psbt.outputs[changeIndex]!.tapBIP32Derivation
  let relabelled := { psbt with outputs := psbt.outputs.modify paymentIndex (·.setTapBIP32Derivation derivation) }
  let review2 ← need "review" (account.reviewSpend relabelled #[utxo] owned testChainTip)
  check "change: a copied label is not ownership" (!review2.outputs[paymentIndex]!.isAccountOwned)

def reviewRefusals : TM Unit := do
  let (account, _) ← accountWith
  let utxo ← funding account 100_000
  let psbt ← need "create" (spend account utxo)
  refused "review: unknown coin" (account.reviewSpend psbt #[] owned testChainTip) (account := true)
  let none2 := psbt.modifyInput 0 (·.setSighashType (some 2))
  refused "review: SIGHASH_NONE" (account.reviewSpend none2 #[utxo] owned testChainTip) (account := true)
  let young := { utxo with isCoinbase := true, height := testChainTip - 10 }
  refused "review: immature coinbase" (account.reviewSpend psbt #[young] owned testChainTip) (account := true)
  let mature := { young with height := testChainTip - Wallet.coinbaseMaturity }
  check "review: mature coinbase" (account.reviewSpend psbt #[mature] owned testChainTip).toBool
  refused "review: creator refuses a big fee"
    (account.createSpend #[utxo] #[{ amount := 50_000, scriptPubKey := destination }] 0 100 testChainTip)

def realInternalKeyRefused : TM Unit := do
  let ms ← masters
  let signers ← ms.mapM keyExpression
  let internalKey := hex (← needE "key" (·.name) (ms[0]!.derived "m/86'/1'/0'/0/0")).publicKey
  refused "internal: a real key" (MultisigAccount.parse s!"tr({internalKey},sortedmulti_a(2,{",".intercalate signers.toList}))" .signet)
    (account := true)
  refused "internal: a signer" (MultisigAccount.parse s!"tr({signers[0]!},sortedmulti_a(2,{signers[1]!},{signers[2]!}))" .signet)
    (account := true)

def unspendableXpubInternalKey : TM Unit := do
  let (account, _) ← accountWith
  let .trTree internalKey _ := account.descriptor.expression | throw "expected a tree"
  let .extended xpub keyNetwork := internalKey.base | throw "expected an extended internal key"
  check "nums xpub: no origin" internalKey.origin.isNone
  check "nums xpub: suffix" (internalKey.derivation.elements == MultisigAccount.signerSuffix)
  check "nums xpub: testnet" (keyNetwork == .testnet)
  check "nums xpub: H" (xpub.publicKey == ByteArray.mk #[0x02] ++ Taproot.unspendableInternalKey)
  check "nums xpub: depth 0" (xpub.depth == 0 && xpub.parentFingerprint == 0 && xpub.childIndex == 0)
  let concatenated := account.signers.foldl (fun acc s => match s.base with
    | .extended k _ => acc ++ k.publicKey | _ => acc) ByteArray.empty
  check "nums xpub: chain code" (xpub.chainCode == sha256 concatenated)
  let (first, _) ← need "t" (MultisigAccount.lift (·.name) (account.descriptor.resolvedTaproot 0 0))
  let (second, _) ← need "t" (MultisigAccount.lift (·.name) (account.descriptor.resolvedTaproot 1 0))
  check "nums xpub: a child of H" (first != Taproot.unspendableInternalKey)
  check "nums xpub: children differ" (first != second)
  let reparsed ← need "reparse" (MultisigAccount.parse account.descriptor.serialized .signet)
  check "nums xpub: round trip" ((← need "a" (reparsed.address 3 1)) == (← need "a" (account.address 3 1)))

def unspendableXpubLookAlikesRefused : TM Unit := do
  let ms ← masters
  let signers ← ms.mapM keyExpression
  let leaf := s!"sortedmulti_a(2,{",".intercalate signers.toList})"
  let chainCode := ByteArray.mk (Array.replicate 32 0x42)
  let nums : HDKey := { depth := 0, parentFingerprint := 0, childIndex := 0, chainCode, privateKey := none,
                        publicKey := ByteArray.mk #[0x02] ++ Taproot.unspendableInternalKey }
  let held ← accountKeyOf ms[0]!
  let realKey : HDKey := { nums with publicKey := held.publicKey }
  check "look-alikes: any chain code on H" (MultisigAccount.parse s!"tr({nums.serialized .testnet}/<0;1>/*,{leaf})" .signet).toBool
  let refusedKeys := [s!"{realKey.serialized .testnet}/<0;1>/*", s!"[00000000]{nums.serialized .testnet}/<0;1>/*",
    s!"{nums.serialized .testnet}/0/*", nums.serialized .testnet, s!"{nums.serialized .mainnet}/<0;1>/*"]
  for (k, n) in refusedKeys.zipIdx do
    refused s!"look-alikes: refused {n}" (MultisigAccount.parse s!"tr({k},{leaf})" .signet) (account := true)

def repeatedSignerRefused : TM Unit := do
  let ms ← masters
  let first ← keyExpression ms[0]!
  let second ← keyExpression ms[1]!
  refused "repeat: same key twice" (MultisigAccount.makeDescriptor 2 #[first, first, second] none .signet) (account := true)
  let relabelled := "[00000001" ++ String.ofList (first.toList.dropWhile (· != '/'))
  refused "repeat: relabelled" (MultisigAccount.makeDescriptor 2 #[first, relabelled, second] none .signet) (account := true)
  check "repeat: distinct accepted" (MultisigAccount.makeDescriptor 2 (← ms.mapM keyExpression) none .signet).toBool

def suffixPinned : TM Unit := do
  let ms ← masters
  let bare ← ms.mapM bareKeyExpression
  for suffix in ["/0/*", "/<0;1>/0", "/*", "", "/<1;0>/*", "/<0;1>/*'"] do
    refused s!"suffix: {suffix}"
      (MultisigAccount.makeDescriptor 2 #[bare[0]! ++ "/<0;1>/*", bare[1]! ++ "/<0;1>/*", bare[2]! ++ suffix] none .signet)

def signerKeyShape : TM Unit := do
  let ms ← masters
  let m := ms[0]!
  let other ← keyExpression ms[1]!
  let account ← accountKeyOf m
  let fp := Descriptor.hex8 m.fingerprint
  let bad := [s!"[{fp}/86'/1'/0']{account.serialized .testnet}/<0;1>/*", s!"{account.neutered.serialized .testnet}/<0;1>/*",
    s!"[{fp}/86'/1']{account.neutered.serialized .testnet}/<0;1>/*"]
  for (b, n) in bad.zipIdx do
    refused s!"key shape: refused {n}" (MultisigAccount.makeDescriptor 1 #[b, other] none .signet)
  refused "key shape: other network" (MultisigAccount.makeDescriptor 1 #[← keyExpression m, other] none .mainnet) (account := true)

def shapeRefusals : TM Unit := do
  let signers ← (← masters).mapM keyExpression
  let nums := hex Taproot.unspendableInternalKey
  refused "shape: threshold 0" (MultisigAccount.makeDescriptor 0 signers none .signet)
  refused "shape: threshold 4" (MultisigAccount.makeDescriptor 4 signers none .signet)
  refused "shape: one signer" (MultisigAccount.makeDescriptor 1 #[signers[0]!] none .signet) (account := true)
  refused "shape: a pk leaf beside"
    (MultisigAccount.parse s!"tr({nums},\{sortedmulti_a(1,{signers[0]!},{signers[1]!}),pk({signers[2]!})})" .signet) (account := true)
  let unsorted ← need "unsorted" (MultisigAccount.parse s!"tr({nums},multi_a(2,{",".intercalate signers.toList}))" .signet)
  check "shape: multi_a accepted, unsorted" (!unsorted.isSorted)

def recordCoding : TM Unit := do
  let (account, _) ← accountWith
  let coin ← funding account 5_000
  let record : MultisigAccountRecord :=
    { id := account.id, name := "Household", descriptor := account.descriptor.serialized,
      createdAtHeight := 100, nextReceiveIndex := 3, allUtxos := #[coin] }
  let text := SwiftJSON.write record.toJV
  let keys : List String := match SwiftJSON.parse? text with
    | some (.obj kvs) => (kvs.map fun (kv : String × SwiftJSON.JV) => kv.1).toList
    | _ => []
  let expected := ["id", "name", "descriptor", "createdAtHeight", "nextReceiveIndex", "nextChangeIndex", "utxos"]
  check "record: JSON keys" (keys.length == expected.length && expected.all keys.contains) s!"{keys}"
  check "record: round trip" (match SwiftJSON.decodeText text MultisigAccountRecord.ofJV with | .ok r => r == record | .error _ => false)
  check "record: balance" (record.balance == 5_000)
  let registration : LedgerRegistration :=
    { policyName := "Household", policyID := ByteArray.mk (Array.replicate 32 1),
      hmac := ByteArray.mk (Array.replicate 32 2), masterFingerprint := 0xF5ACC2FD,
      keyPath := #[0x8000_0057, 0x8000_0001, 0x8000_0000] }
  let withLedger := { record with ledger := some registration }
  check "record: ledger round trip"
    (match SwiftJSON.decodeText (SwiftJSON.write withLedger.toJV) MultisigAccountRecord.ofJV with
     | .ok r => r == withLedger | .error _ => false)

def bundleAccounts : TM Unit := do
  let (account, ms) ← accountWith
  let coin ← funding account 5_000
  let record : MultisigAccountRecord :=
    { id := account.id, name := "Household", descriptor := account.descriptor.serialized,
      createdAtHeight := 90, nextReceiveIndex := 1, allUtxos := #[coin] }
  let bundle : ImportBundle := { network := "signet", lastKnownHeight := 200 }
  check "bundle: no vaults key without accounts" (!(bundle.serialized.splitOn "vaults").length > 1)
  let withAccount := { bundle with vaults := some #[record] }
  check "bundle: account restores"
    (match ImportBundle.decode withAccount.serialized with | .ok b => b.vaults == some #[record] | .error _ => false)
  let keys ← ms.mapM bareKeyExpression
  let muSig2 := { record with descriptor := s!"tr(musig({keys[0]!},{keys[1]!})/<0;1>/*)" }
  for (vs, n) in [(#[muSig2], 1), (#[record, muSig2], 2)] do
    check s!"bundle: MuSig2 refused {n}"
      (match ImportBundle.decode { bundle with vaults := some vs }.serialized with
       | .error e => e.name == "unsupportedWalletData" | .ok _ => false)
  check "bundle: mainnet refused"
    (match ImportBundle.decode { withAccount with network := "mainnet" }.serialized with
     | .error e => e.name == "unsupportedWalletData" | .ok _ => false)
  check "bundle: too many accounts"
    (match ImportBundle.decode { bundle with vaults := some (Array.replicate (ImportBundle.maximumVaults + 1) record) }.serialized with
     | .error (.wallet _) => true | _ => false)

/-! ## TimelockedMultisigTests -/

def coreVectors : TM Unit := do
  let text ← IO.FS.readFile "Vectors/core-timelocked-multisig.json"
  let json ← needE "json" id (Lean.Json.parse text)
  let cases ← needE "cases" id (json.getObjValAs? (Array Lean.Json) "cases")
  check "core: four cases" (cases.size == 4)
  for c in cases do
    let name ← needE "name" id (c.getObjValAs? String "name")
    let descriptor ← needE "descriptor" id (c.getObjValAs? String "descriptor")
    let checksum ← needE "checksum" id (c.getObjValAs? String "checksum")
    let d ← needE s!"{name} parse" (·.name) (Descriptor.parse descriptor)
    check s!"core {name}: checksum" (d.serialized == descriptor ++ "#" ++ checksum) d.serialized
    let addresses ← needE "addresses" id (c.getObjVal? "addresses")
    for choice in [0, 1] do
      let expected ← needE "choice" id (addresses.getObjValAs? (Array String) (toString choice))
      for (address, index) in expected.toList.zipIdx do
        let derived ← needE "derive" (·.name) (d.derived index.toUInt32 .regtest)
        check s!"core {name}: {choice}/{index}" (derived[choice]!.address == address)

def leafPolicies : TM Unit := do
  let keys := (List.range 3).toArray.map fun i => ByteArray.mk (Array.replicate 32 (i + 1).toUInt8)
  for blocks in ([1, 16, 17, 144, 4320, 65535, 0x7FFF_FFFF] : List UInt32) do
    let multi ← needE "multi" (·.name) (Multisig.timelockedMultiScript 2 keys blocks)
    check s!"policy: multi {blocks}" (Multisig.parsePolicy multi == some { threshold := 2, keys, relativeLock := some blocks })
    check s!"policy: multi {blocks} is not plain" (Multisig.parse multi).isNone
    let single ← needE "single" (·.name) (Multisig.timelockedKeyScript keys[0]! blocks)
    check s!"policy: pk {blocks}" (Multisig.parsePolicy single == some { threshold := 1, keys := #[keys[0]!], relativeLock := some blocks })
  check "policy: older(0) refused" (match Multisig.timelockedKeyScript keys[0]! 0 with | .error .invalidTimelock => true | _ => false)
  let five ← needE "five" (·.name) (Multisig.timelockedKeyScript keys[0]! 5)
  let nonMinimal := five.bytes.extract 0 34 ++ ByteArray.mk #[0x01, 0x05] ++ five.bytes.extract 35 five.bytes.size
  check "policy: non-minimal lock" (Multisig.parsePolicy ⟨nonMinimal⟩).isNone
  check "policy: trailing opcode" (Multisig.parsePolicy ⟨five.bytes.push Script.Op.checkSig⟩).isNone
  check "bip68: equal" (RelativeLock.isSatisfied 10 10 2)
  check "bip68: more" (RelativeLock.isSatisfied 10 11 2)
  check "bip68: fewer" (!RelativeLock.isSatisfied 10 9 2)
  check "bip68: version 1" (!RelativeLock.isSatisfied 10 10 1)
  check "bip68: disabled" (!RelativeLock.isSatisfied 10 0xFFFF_FFFD 2)
  check "bip68: time flag" (!RelativeLock.isSatisfied 10 (10 ||| 0x40_0000) 2)

def tfunding (a : MultisigAccount) (amount : Int64) (index : UInt32 := 0) (height : UInt32) : TM WalletUTXO :=
  funding a amount .receive index height (0x5B + index.toUInt8)

def tspend (a : MultisigAccount) (u : WalletUTXO) (tip : UInt32) (path : SpendPath) : MAM PSBT :=
  spend a u 40_000 tip path

def recoveryKeyOrderDoesNotMatter : TM Unit := do
  let signers ← (← masters).mapM keyExpression
  let others ← (#[0xD4, 0xD5, 0xD6] : Array UInt8).mapM fun b => do keyExpression (← master b)
  let separate ← [others, others.reverse, #[others[1]!, others[2]!, others[0]!]].mapM fun ks => do
    return (← need "d" (MultisigAccount.makeDescriptor 2 (signers.extract 0 2) (some (.separateKeys 2 ks 144)) .signet)).serialized
  check "recovery order: separate keys" (separate.all (· == separate.head!))
  let reused ← [signers, signers.reverse].mapM fun ss => do
    return (← need "d" (MultisigAccount.makeDescriptor 2 ss (some (.fewerSigners 1 10)) .signet)).serialized
  check "recovery order: reused signers" (reused.all (· == reused.head!))

def fewerSigners : TM Unit := do
  let unordered ← masters
  let d ← need "d" (MultisigAccount.makeDescriptor 2 (← unordered.mapM keyExpression) (some (.fewerSigners 1 10)) .signet)
  let account ← need "account" (MultisigAccount.make d .signet)
  let ms ← inSignerOrder unordered account
  let some recovery := account.recovery | throw "no recovery"
  check "fewer: recovery shape" (recovery.threshold == 1 && recovery.blocks == 10 && recovery.keys.size == 3)
  let reparsed ← need "reparse" (MultisigAccount.parse d.serialized .signet)
  check "fewer: round trip" ((← need "a" (reparsed.address 2)) == (← need "a" (account.address 2)))
  let coin ← tfunding account 100_000 0 100
  let now ← need "create" (tspend account coin 101 .signers)
  check "fewer: two leaves" (now.inputs[0]!.tapLeafScripts.size == 2)
  let some changeTree := now.outputs.findSome? (·.tapTree) | throw "no change tree"
  let changeLeaves := (← need "leaves" (account.leaves 1 0)).map (·.script)
  check "fewer: change tree right leaf first" (changeTree.map (·.2.2) == changeLeaves.reverse)
  check "fewer: change tree depth/version" (changeTree.all fun (d, v, _) => d == 1 && v == 0xC0)
  let now ← need "sign 0" (sign account now ms[0]! #[coin] 101)
  check "fewer: one signer cannot finalize" (!now.finalize.toBool)
  let now ← need "sign 2" (sign account now ms[2]! #[coin] 101)
  check "fewer: approvals" ((← need "ap" (account.approvals now #[coin])) == #[0, 2])
  check "fewer: no recovery approvals" ((← need "ap" (account.approvals now #[coin] .recovery)).isEmpty)
  let fast ← need "finalize" (finalize account now #[coin] 101)
  check "fewer: default sequence" (fast.inputs[0]!.sequence == TransactionBuilder.defaultSequence)
  check "fewer: five witness items" (fast.inputs[0]!.witness.size == 5)
  check "fewer: estimate covers signers' witness"
    ((witnessSize fast.inputs[0]!.witness : Int) ≤ (← need "w" (account.witnessBytesPerInput .signers)))
  check "fewer: unlock height 110" (account.recoveryUnlockHeight coin == some 110)
  check "fewer: unlock boundary" (!account.isUnlockedForRecovery coin 108 && account.isUnlockedForRecovery coin 109)
  refused "fewer: young coin refused" (tspend account coin 108 .recovery) (account := true)
  let later ← need "create recovery" (tspend account coin 109 .recovery)
  check "fewer: review path recovery"
    ((← need "review" (account.reviewSpend later #[coin] owned 109)).path == .recovery)
  refused "fewer: review at 108 refused" (account.reviewSpend later #[coin] owned 108) (account := true)
  let later ← need "sign 1" (sign account later ms[1]! #[coin] 109)
  check "fewer: recovery approvals" ((← need "ap" (account.approvals later #[coin] .recovery)) == #[1])
  let slow ← need "finalize slow" (finalize account later #[coin] 109)
  check "fewer: sequence 10" (slow.inputs[0]!.sequence == 10)
  let leaves ← need "leaves" (account.leaves 0 0)
  let some recoveryLeaf := leaves.find? (·.isRecovery) | throw "no recovery leaf"
  let w := slow.inputs[0]!.witness
  check "fewer: recovery leaf in witness" (w[w.size - 2]! == recoveryLeaf.script)
  check "fewer: estimate covers recovery witness"
    ((witnessSize w : Int) ≤ (← need "w" (account.witnessBytesPerInput .recovery)))

def separateKey : TM Unit := do
  let ms ← masters
  let recoveryMaster ← master 0xD4
  let d ← need "d" (MultisigAccount.makeDescriptor 2 (← (ms.extract 0 2).mapM keyExpression)
    (some (.separateKeys 1 #[← keyExpression recoveryMaster] 144)) .signet)
  check "separate: pk leaf" ((d.serialized.splitOn "and_v(v:pk(").length > 1)
  let account ← need "account" (MultisigAccount.make d .signet)
  check "separate: hasSigner" (account.hasSigner recoveryMaster)
  let coin ← tfunding account 80_000 0 500
  let now ← need "create" (tspend account coin 600 .signers)
  refused "separate: recovery key signs nothing on the signers' path" (sign account now recoveryMaster #[coin] 600)
  let later ← need "create" (tspend account coin 643 .recovery)
  let later ← need "sign" (sign account later recoveryMaster #[coin] 643)
  let tx ← need "finalize" (finalize account later #[coin] 643)
  check "separate: sequence 144" (tx.inputs[0]!.sequence == 144)
  check "separate: three witness items" (tx.inputs[0]!.witness.size == 3)

def surplusRecoverySignatureLeftOut : TM Unit := do
  let ms ← masters
  let exprs ← ms.mapM keyExpression
  let account ← need "account" (do
    MultisigAccount.make (← MultisigAccount.makeDescriptor 3 exprs (some (.fewerSigners 1 10)) .signet) .signet)
  let coin ← tfunding account 100_000 0 100
  let mut later ← need "create" (tspend account coin 109 .recovery)
  for m in ms.extract 0 2 do later ← need "sign" (sign account later m #[coin] 109)
  check "surplus: two recovery approvals" ((← need "ap" (account.approvals later #[coin] .recovery)) == #[0, 1])
  let tx ← need "finalize" (finalize account later #[coin] 109)
  let w := tx.inputs[0]!.witness
  let some recoveryLeaf := (← need "leaves" (account.leaves 0 0)).find? (·.isRecovery) | throw "no recovery leaf"
  check "surplus: recovery leaf" (w[w.size - 2]! == recoveryLeaf.script)
  check "surplus: exactly one signature" (((w.extract 0 3).filter (!·.isEmpty)).size == 1)

def bip326OldCoins : TM Unit := do
  let ms ← masters
  let recoveryMaster ← master 0xD4
  let exprs ← (ms.extract 0 2).mapM keyExpression
  let recoveryExpr ← keyExpression recoveryMaster
  let account ← need "account" (do
    MultisigAccount.make (← MultisigAccount.makeDescriptor 2 exprs (some (.separateKeys 1 #[recoveryExpr] 144)) .signet) .signet)
  let coins := #[← tfunding account 60_000 1 1, ← tfunding account 60_000 2 2]
  let mut psbt ← need "create" (account.createSpend coins #[{ amount := 100_000, scriptPubKey := destination }] 0 2 200 .signers (0.5, 0.5))
  let tx ← need "tx" (MultisigAccount.lift (·.name) psbt.unsignedTransaction)
  for h : k in [0:tx.inputs.size] do
    let some c := coins.find? (·.outpoint == tx.inputs[k].previousOutput) | throw "coin"
    psbt := psbt.modifyInput k (·.setSequence (some (200 - c.height + 1)))
  check "bip326: review path recovery" ((← need "review" (account.reviewSpend psbt coins owned 200)).path == .recovery)
  for m in ms.extract 0 2 do psbt ← need "sign" (sign account psbt m coins 200)
  let finished ← need "finalize" (finalize account psbt coins 200)
  for input in finished.inputs do
    let w := input.witness
    check "bip326: signers' leaf finishes" (((Multisig.parsePolicy ⟨w[w.size - 2]!⟩).bind (·.relativeLock)).isNone)

def timelockedReviewRefusals : TM Unit := do
  let ms ← masters
  let exprs ← ms.mapM keyExpression
  let account ← need "account" (do
    MultisigAccount.make (← MultisigAccount.makeDescriptor 2 exprs (some (.fewerSigners 1 10)) .signet) .signet)
  let first ← tfunding account 60_000 0 100
  let second ← tfunding account 60_000 1 100
  let mixed ← need "create" (account.createSpend #[first, second] #[{ amount := 100_000, scriptPubKey := destination }] 0 2 200
    .recovery (0.5, 0.5))
  let rebuilt := mixed.modifyInput 1 fun i =>
    ⟨(i.pairs.filter (·.type != PSBT.InType.sequence)).push (PSBT.KeyValue.make PSBT.InType.sequence .empty (ByteArray.mk #[0xFD, 0xFF, 0xFF, 0xFF]))⟩
  check "tl review: mixed is the signers' path"
    ((← need "review" (account.reviewSpend rebuilt #[first, second] owned 200)).path == .signers)
  let stripped ← need "create" (tspend account first 200 .signers)
  let stripped := stripped.modifyInput 0 fun i => i.setTapLeafScripts (i.tapLeafScripts.extract 0 1)
  refused "tl review: a missing leaf" (account.reviewSpend stripped #[first] owned 200) (account := true)

def topOfHeightRange : TM Unit := do
  let ms ← masters
  let exprs ← ms.mapM keyExpression
  let account ← need "account" (do
    MultisigAccount.make (← MultisigAccount.makeDescriptor 2 exprs (some (.fewerSigners 1 10)) .signet) .signet)
  let coin ← tfunding account 60_000 0 (0xFFFF_FFFF - 4)
  check "top: no unlock height" (account.recoveryUnlockHeight coin).isNone
  let psbt ← need "create" (tspend account coin 200 .signers)
  let psbt := psbt.modifyInput 0 (·.setSequence (some 10))
  refusedWith "top: past the last block height" (account.reviewSpend psbt #[coin] owned 0xFFFF_FFFF)
    (.invalidSpend "input 1 unlocks for recovery only past the last block height")
  let coinbase := { coin with isCoinbase := true }
  let psbt := psbt.modifyInput 0 (·.setSequence (some TransactionBuilder.defaultSequence))
  refusedWith "top: coinbase maturity" (account.reviewSpend psbt #[coinbase] owned 0xFFFF_FFFF)
    (.invalidSpend "input 1 spends a coinbase that matures in 95 blocks")

def admissionRefusals : TM Unit := do
  let ms ← masters
  let signers ← ms.mapM keyExpression
  let bare ← ms.mapM bareKeyExpression
  let other ← keyExpression (← master 0xD4)
  let primary := s!"sortedmulti_a(2,{",".intercalate signers.toList})"
  let nums := hex Taproot.unspendableInternalKey
  let otherBare := String.ofList (other.toList.take (other.length - 8))
  let bare0 := bare[0]!
  let refusedLeaves := [
    s!"and_v(v:pk({other}),older(65536))",
    s!"and_v(v:pk({other}),older(4194314))",
    s!"and_v(v:pk({signers[0]!}),older(10))",
    s!"and_v(v:pk({otherBare}/<2;3>/*),older(10))",
    s!"and_v(v:multi_a(1,{bare0}/<2;3>/*,{bare0}/<2;3>/*),older(10))",
    s!"and_v(v:pk([deadbeef{String.ofList (bare0.toList.drop 9)}/<2;3>/*),older(10))",
    s!"and_v(v:pk({bare0.replace "/86'/" "/87'/"}/<2;3>/*),older(10))",
    s!"multi_a(1,{other})"]
  check "admission: positive control"
    (MultisigAccount.parse s!"tr({nums},\{{primary},and_v(v:pk({other}),older(10))})" .signet).toBool
  for (leaf, n) in refusedLeaves.zipIdx do
    refused s!"admission: refused {n}" (MultisigAccount.parse s!"tr({nums},\{{primary},{leaf}})" .signet)
  refusedWith "admission: bare recovery key"
    (MultisigAccount.parse s!"tr({nums},\{{primary},and_v(v:pk({nums}),older(10))})" .signet)
    (.invalidDescriptor "every recovery key must be an extended public key")
  refused "admission: a timelocked leaf alone" (MultisigAccount.parse s!"tr({nums},and_v(v:pk({other}),older(10)))" .signet)
  check "admission: older(0) is invalidTimelock"
    (match Descriptor.parse s!"tr({nums},\{{primary},and_v(v:pk({other}),older(0))})" with
     | .error .invalidTimelock => true | _ => false)
  refused "admission: recovery threshold 4" (MultisigAccount.makeDescriptor 2 signers (some (.fewerSigners 4 10)) .signet)

/-! ## BIP341 script-path vectors (`SighashBIP341Tests`, script-path half) -/

def scriptPathVectors : TM Unit := do
  let json ← needE "json" id (Lean.Json.parse (← IO.FS.readFile "Vectors/bip341-scriptpath-test-vectors.json"))
  let given ← needE "given" id (json.getObjVal? "given")
  let tx ← needE "tx" (·.name) (Transaction.decode (← hexOf (← needE "raw" id (given.getObjValAs? String "rawUnsignedTx"))))
  let utxos ← needE "utxos" id (given.getObjValAs? (Array Lean.Json) "utxosSpent")
  let spent ← utxos.mapM fun u => do
    return ({ amount := Int64.ofInt (← needE "amount" id (u.getObjValAs? Int "amountSats")),
              scriptPubKey := ← hexOf (← needE "spk" id (u.getObjValAs? String "scriptPubKey")) } : SighashBIP341.SpentOutput)
  let internalKey ← hexOf (← needE "ik" id (given.getObjValAs? String "internalKey"))
  let leafKeys ← (← needE "lk" id (given.getObjValAs? (Array String) "leafKeys")).mapM hexOf
  let threshold ← needE "t" id (given.getObjValAs? Int "threshold")
  check "vectors: NUMS internal key" (internalKey == Taproot.unspendableInternalKey)
  let inputs ← needE "inputs" id (json.getObjValAs? (Array Lean.Json) "inputSpending")
  for entry in inputs do
    let g ← needE "g" id (entry.getObjVal? "given")
    let inter ← needE "i" id (entry.getObjVal? "intermediary")
    let expected ← needE "e" id (entry.getObjVal? "expected")
    let index ← needE "index" id (g.getObjValAs? Nat "txinIndex")
    let leafScript ← hexOf (← needE "leaf" id (g.getObjValAs? String "leafScript"))
    let cbBytes ← hexOf (← needE "cb" id (g.getObjValAs? String "controlBlock"))
    let some cb := Tx.Taproot.ControlBlock.parse? cbBytes | throw "control block"
    let hashType : SighashBIP341.HashType := ⟨(← needE "ht" id (g.getObjValAs? Nat "hashType")).toUInt8⟩
    let annex ← match g.getObjValAs? String "annex" with
      | .ok s => some <$> hexOf s
      | .error _ => pure none
    let secrets ← (← needE "secrets" id (g.getObjValAs? (Array String) "signingSecrets")).mapM hexOf
    let sigMsg ← hexOf (← needE "sigMsg" id (inter.getObjValAs? String "sigMsg"))
    let sigHash ← hexOf (← needE "sigHash" id (inter.getObjValAs? String "sigHash"))
    let sigObj ← needE "sigs" id (expected.getObjVal? "signatures")
    let sigPairs ← match sigObj with
      | .obj kvs => kvs.toArray.mapM fun ⟨k, v⟩ => do return (← hexOf k, ← hexOf (← needE "sig" id v.getStr?))
      | _ => throw "signatures"
    let witness ← (← needE "w" id (expected.getObjValAs? (Array String) "witness")).mapM fun s =>
      pure ((Wire.dataOfHex? s).getD .empty)
    let label := s!"input {index} hashType {hashType.rawValue}"
    let some (t, ks) := Multisig.parse ⟨leafScript⟩ | throw s!"{label}: leaf does not parse"
    check s!"vectors {label}: leaf shape" (t == threshold && ks == leafKeys && cb.internalKey == internalKey)
    let committed := Tx.Taproot.tweakedOutputKey internalKey (some (Tx.Taproot.leafHash Tx.Taproot.leafVersion ⟨leafScript⟩))
    check s!"vectors {label}: commitment"
      (committed == some (suffixBytes spent[index]!.scriptPubKey 32, cb.outputKeyParity))
    let sp := some (SighashBIP341.ScriptPath.ofLeaf ⟨leafScript⟩)
    check s!"vectors {label}: sigMsg" ((SighashBIP341.signatureMessage tx index spent hashType sp annex).toOption == some sigMsg)
    check s!"vectors {label}: sigHash" ((SighashBIP341.sighash tx index spent hashType sp annex).toOption == some sigHash)
    for secret in secrets do
      let xonly ← needE "x" (fun _ => "key") (do pure (xonlyBytes (← pointOfSecret (← secretOf secret))))
      let some (_, expectedSig) := sigPairs.find? (·.1 == xonly) | throw "missing signature"
      check s!"vectors {label}: signature verifies"
        ((schnorrVerify xonly sigHash (expectedSig.extract 0 64)).toOption.getD false)
      let mine := Signer.scriptPathSignature tx index spent ⟨leafScript⟩ Tx.Taproot.leafVersion hashType annex secret aux0
      check s!"vectors {label}: signature reproduced" (mine.toOption == some expectedSig)
    match Signer.multisigWitness sigPairs ⟨leafScript⟩ cb with
    | .ok w =>
      check s!"vectors {label}: witness" (w == witness)
      check s!"vectors {label}: layout" (w.size == leafKeys.size + 2 && w[leafKeys.size]! == leafScript &&
        w.back? == some cb.serialized && w[1]! == .empty)
    | .error e => check s!"vectors {label}: witness" false e.name


/-! ## HistoryOutputTests (wallet sends record their outputs) -/

def p2trDestination : ByteArray := ByteArray.mk (#[0x51, 0x20] ++ Array.replicate 32 0x99)

def wmT {α} (name : String) (x : WM α) : TM α := do
  match ← x.run with
  | .ok a => pure a
  | .error e => throw s!"{name}: {e.name}"

def fakeMatch (height : UInt32) (txs : Array Transaction) : Net.BlockMatch :=
  let header := Net.BlockHeader.mk' 2 (ByteArray.mk (Array.replicate 32 0)) (ByteArray.mk (Array.replicate 32 0xAA))
    (1_700_000_000 + height) 0x207F_FFFF 0
  let block : Net.Block := { header, transactions := txs }
  { height, blockHash := block.hash, block }

def coinbaseInput : Transaction.Input :=
  { previousOutput := ⟨ByteArray.mk (Array.replicate 32 0), 0xFFFF_FFFF⟩, scriptSig := ByteArray.mk #[0x01], sequence := 0xFFFF_FFFF }

/-- Deterministic draws: the locktime draw 0.5 (`randomness: { 0.5 }`), change last, zero aux. -/
def pinned : Randomness :=
  { entropy := pure (ByteArray.mk (Array.replicate 16 0)), draw := pure 0.5, changePosition := fun n => pure n,
    auxRand := pure aux0 }

def newKeyStore : IO (KeyStore IO) := do return inMemoryKeyStore (← IO.mkRef {})

/-- `fundedWallet(coins: [(.receive, 0, 150_000, 100)])`: the test mnemonic, creation height 100, one coin,
matured. -/
def fundedWallet (keyStore : KeyStore IO) (storagePath : Option System.FilePath := none) : TM Wallet := do
  let w ← wmT "create" (Wallet.create .signet keyStore storagePath (some (ByteArray.mk (Array.replicate 16 0))) 100 0 pinned)
  let script ← wmT "spk" (w.scriptPubKey .receive 0)
  let funding : Transaction := { version := 2, inputs := #[coinbaseInput], outputs := #[{ value := 150_000, scriptPubKey := script }], locktime := 0 }
  discard (wmT "fund" (w.apply (fakeMatch 100 #[funding])))
  wmT "mature" (w.recordScanHeight (100 + Wallet.coinbaseMaturity))
  return w

def makeFakeSegwitTx (value : Int64 := 50_000) : Transaction :=
  { version := 2,
    inputs := #[{ previousOutput := ⟨ByteArray.mk (Array.replicate 32 0x11), 0⟩, scriptSig := .empty, sequence := 0xFFFF_FFFD,
                  witness := #[ByteArray.mk #[0x30, 0x44, 0x02, 0x20], ByteArray.mk (Array.replicate 33 0x02)] }],
    outputs := #[{ value, scriptPubKey := ByteArray.mk (#[0x51, 0x20] ++ Array.replicate 32 0x77) }], locktime := 0 }

def tempPath (name : String) : IO System.FilePath := do
  let dir : System.FilePath := s!"/tmp/winnow-multisig-test-{← IO.monoNanosNow}"
  IO.FS.createDirAll dir
  return dir / name

/-! ## SilentPaymentSendTests (BIP352 sends from the wallet) -/

/-- The wallet funded with one matured coin of `amount` at receive 0, and that coin's txid. -/
def fundedWalletWith (amount : Int64) : TM (Wallet × ByteArray) := do
  let w ← wmT "create" (Wallet.create .signet (← newKeyStore) none (some (ByteArray.mk (Array.replicate 16 0))) 100 0 pinned)
  let script ← wmT "spk" (w.scriptPubKey .receive 0)
  let funding : Transaction := { version := 2, inputs := #[coinbaseInput], outputs := #[{ value := amount, scriptPubKey := script }], locktime := 0 }
  discard (wmT "fund" (w.apply (fakeMatch 100 #[funding])))
  wmT "mature" (w.recordScanHeight (100 + Wallet.coinbaseMaturity))
  return (w, funding.txid)

/-- m/86'/1'/0'/0/0 of the test mnemonic, BIP86-tweaked: derived here, not by the wallet. -/
def tweakedReceiveKey0 : TM ByteArray := do
  let words ← needE "mnemonic" (fun _ => "bip39") (BIP39.mnemonic (ByteArray.mk (Array.replicate 16 0)))
  let key ← needE "derive" (·.name) (do (← HDKey.ofSeed (BIP39.seed words)).derived "m/86'/1'/0'/0/0")
  needE "tweak" (·.name) (BIP86.tweakedPrivateKey key.privateKey.get!)

/-- A throwaway code (valid keys, secrets thrown away). -/
def spRecipient (mainnet : Bool := false) : TM SilentPaymentAddress := do
  let key : TM ByteArray := do
    let mut s ← IO.getRandomBytes 32
    while !isValidSecret s do s ← IO.getRandomBytes 32
    needE "pub" (·.name) (publicKeyOf s)
  needE "code" (·.name) (SilentPaymentAddress.make (← key) (← key) (SilentPayment.hrp mainnet))

def expectedSPScripts (w : Wallet) (funding : ByteArray) (recipients : List SilentPaymentAddress) : TM (List ByteArray) := do
  let input : SilentPaymentSending.Input :=
    { txid := funding, vout := 0, prevoutScriptPubKey := ← wmT "spk" (w.scriptPubKey .receive 0), privateKey := ← tweakedReceiveKey0 }
  needE "derive" (·.name) (SilentPaymentSending.outputScripts [input] recipients)

def silentPaymentSend : TM Unit := do
  let (w, funding) ← fundedWalletWith 150_000
  let address ← spRecipient
  let prepared ← wmT "send" (w.buildSend #[] 2 testChainTip (silentPayments := #[{ amount := 100_000, address }]))
  let tx := prepared.built.transaction
  check "sp send: one signed input" (tx.inputs.size == 1 && tx.inputs[0]!.witness.size == 1)
  check "sp send: change" prepared.built.changeAmount.isSome
  let expected ← expectedSPScripts w funding [address]
  check "sp send: pays the independently derived script" (tx.outputs.any fun o => o.value == 100_000 && o.scriptPubKey == expected[0]!)
  check "sp send: a P2TR script, not the change" (expected[0]!.size == 34 && expected[0]! != (← wmT "spk" (w.scriptPubKey .change 0)))
  check "sp send: the review gate gets the same script"
    (prepared.resolvedSilentPayments.map (fun p => (p.amount, p.scriptPubKey)) == #[((100_000 : Int64), expected[0]!)])
  wmT "commit" (w.commit prepared)
  let some outputs := ((← w.history).back?).bind (·.outputs) | throw "no outputs"
  check "sp send: the history names the code"
    (outputs.external.size == 1 && outputs.external[0]!.scriptPubKey == expected[0]! &&
     outputs.external[0]!.silentPaymentAddress == address.encoded.toOption)

def silentPaymentSameCodeTwice : TM Unit := do
  let (w, funding) ← fundedWalletWith 250_000
  let address ← spRecipient
  let tx := (← wmT "send" (w.buildSend #[] 2 testChainTip
    (silentPayments := #[{ amount := 100_000, address }, { amount := 50_000, address }]))).built.transaction
  let expected ← expectedSPScripts w funding [address, address]
  check "sp twice: distinct scripts" (expected[0]! != expected[1]!)
  check "sp twice: both paid" (tx.outputs.any (fun o => o.value == 100_000 && o.scriptPubKey == expected[0]!) &&
    tx.outputs.any (fun o => o.value == 50_000 && o.scriptPubKey == expected[1]!))

def silentPaymentMixed : TM Unit := do
  let (w, _) ← fundedWalletWith 250_000
  let address ← spRecipient
  let tx := (← wmT "send" (w.buildSend #[{ amount := 40_000, scriptPubKey := p2trDestination }] 2 testChainTip
    (silentPayments := #[{ amount := 100_000, address }]))).built.transaction
  check "sp mixed: the ordinary payment" (tx.outputs.any fun o => o.value == 40_000 && o.scriptPubKey == p2trDestination)
  check "sp mixed: the silent payment" (tx.outputs.any fun o => o.value == 100_000 && o.scriptPubKey != p2trDestination)
  check "sp mixed: every input signed" (tx.inputs.all (·.witness.size == 1))

def silentPaymentValidation : TM Unit := do
  let (w, _) ← fundedWalletWith 150_000
  let mainnet ← spRecipient (mainnet := true)
  let code := mainnet.encoded.toOption.getD ""
  check "sp validation: a mainnet code is refused on signet"
    (match SilentPayment.ofCode 1_000 code .signet with | .error (.wrongHRP "tsp" "sp") => true | _ => false)
  let signet ← spRecipient
  check "sp validation: a signet code is accepted" (SilentPayment.ofCode 1_000 (signet.encoded.toOption.getD "") .signet).toBool
  check "sp validation: an empty send is refused"
    (match ← (w.buildSend #[] 2 testChainTip (silentPayments := #[])).run with
     | .error (.wallet .noPayments) => true | _ => false)

def sendRecordsItsOutputs : TM Unit := do
  let w ← fundedWallet (← newKeyStore)
  let prepared ← wmT "send" (w.buildSend #[{ amount := 100_000, scriptPubKey := p2trDestination }] 2 testChainTip)
  wmT "commit" (w.commit prepared)
  let signed := prepared.built.transaction
  let some paid := signed.outputs.findIdx? (·.scriptPubKey == p2trDestination) | throw "no payment"
  let some change := signed.outputs.findIdx? (·.scriptPubKey != p2trDestination) | throw "no change"
  let some outputs := ((← w.history).find? (·.txid == signed.txid)).bind (·.outputs) | throw "no outputs"
  check "history: external" (outputs.external == #[{ vout := paid.toUInt32, amount := 100_000, scriptPubKey := p2trDestination }])
  check "history: change" (outputs.change == #[change.toUInt32])
  discard (wmT "confirm" (w.apply (fakeMatch 150 #[signed])))
  let some confirmed := (← w.history).find? (·.txid == signed.txid) | throw "no entry"
  check "history: confirmed height" (confirmed.height == 150)
  check "history: no longer bumpable" (← w.feeBumpableTxids).isEmpty
  check "history: outputs kept" (confirmed.outputs == some outputs)

def sendToOwnAddressIsNotExternal : TM Unit := do
  let w ← fundedWallet (← newKeyStore)
  let ours ← wmT "spk" (w.scriptPubKey .receive 1)
  let prepared ← wmT "send" (w.buildSend #[{ amount := 100_000, scriptPubKey := ours }] 2 testChainTip)
  wmT "commit" (w.commit prepared)
  let signed := prepared.built.transaction
  check "own: two outputs" (signed.outputs.size == 2)
  let some outputs := ((← w.history).find? (·.txid == signed.txid)).bind (·.outputs) | throw "no outputs"
  check "own: no external" outputs.external.isEmpty
  check "own: one change" (outputs.change.size == 1)

def feeBumpRecordsItsOutputs : TM Unit := do
  let w ← fundedWallet (← newKeyStore)
  let original ← wmT "send" (w.buildSend #[{ amount := 100_000, scriptPubKey := p2trDestination }] 2 testChainTip)
  wmT "commit" (w.commit original)
  let txid := original.built.transaction.txid
  let rate ← wmT "rate" (w.pendingFeeRate txid)
  let replacement ← wmT "bump" (w.buildFeeBump txid (rate + 1))
  wmT "commit bump" (w.commitFeeBump replacement)
  let signed := replacement.built.transaction
  let some outputs := ((← w.history).find? (·.txid == signed.txid)).bind (·.outputs) | throw "no outputs"
  check "bump: external amount" (outputs.external.map (·.amount) == #[100_000])
  check "bump: external script" ((outputs.external[0]?.map (·.scriptPubKey)) == some p2trDestination)
  check "bump: change" (outputs.change.size == 1)

def recordedOutputsRoundTrip : TM Unit := do
  let path ← tempPath "history-outputs-wallet.json"
  let keyStore ← newKeyStore
  let w ← fundedWallet keyStore (some path)
  let prepared ← wmT "send" (w.buildSend #[{ amount := 100_000, scriptPubKey := p2trDestination }] 2 testChainTip)
  wmT "commit" (w.commit prepared)
  let text ← IO.FS.readFile path
  let scriptHex : Option String := do
    let .obj top ← SwiftJSON.parse? text | none
    let (_, .arr entries) ← top.find? (·.1 == "history") | none
    let .obj last ← entries.back? | none
    let (_, .obj recorded) ← last.find? (·.1 == "outputs") | none
    let (_, .arr external) ← recorded.find? (·.1 == "external") | none
    let .obj first ← external[0]? | none
    let (_, .str s) ← first.find? (·.1 == "scriptPubKey") | none
    some s
  check "file: script as hex" (scriptHex == some (hex p2trDestination))
  let reopened ← wmT "open" (Wallet.open path keyStore pinned)
  let some entry := (← reopened.history).find? (·.txid == prepared.built.transaction.txid) | throw "no entry"
  check "file: outputs reopen" (entry.outputs == ((← w.history).back?.bind (·.outputs)))
  check "file: amount" ((entry.outputs.bind (·.external[0]?)).map (·.amount) == some 100_000)

def backupCompatibility : TM Unit := do
  let w ← fundedWallet (← newKeyStore)
  let send ← wmT "send" (w.buildSend #[{ amount := 100_000, scriptPubKey := p2trDestination }] 2 testChainTip)
  wmT "commit" (w.commit send)
  discard (wmT "confirm" (w.apply (fakeMatch 150 #[send.built.transaction])))
  let backup ← wmT "export" w.exportBundle
  let decoded ← needE "decode" (·.name) (ImportBundle.decode backup.serialized)
  let restored ← wmT "import" (Wallet.importing decoded (← newKeyStore) none pinned)
  let some entry := (← restored.history).find? (·.txid == send.built.transaction.txid) | throw "no entry"
  check "backup: recipient script" ((entry.outputs.bind (·.external[0]?)).map (·.scriptPubKey) == some p2trDestination)
  check "backup: block hash" entry.blockHash.isSome
  let legacy := { entry with outputs := none }
  match SwiftJSON.decodeText (SwiftJSON.write legacy.toJV) HistoryEntry.ofJV with
  | .ok old =>
    check "backup: legacy outputs absent" old.outputs.isNone
    check "backup: legacy raw transaction" (old.rawTransaction == entry.rawTransaction)
  | .error e => check "backup: legacy decodes" false e

def invalidMetadata : TM Unit := do
  let recipient : HistoryEntry.ExternalOutput := { vout := 0, amount := 50_000, scriptPubKey := p2trDestination }
  let invalid : List HistoryEntry.Outputs := [
    { external := #[recipient, recipient] }, { external := #[recipient], change := #[0] },
    { change := #[2, 1] }, { change := #[1, 1] },
    { external := #[{ recipient with amount := -1 }] }, { external := #[{ recipient with scriptPubKey := .empty }] },
    { external := #[{ recipient with amount := bitcoinAmountMaximum }, { recipient with vout := 1, amount := 1 }] },
    { external := #[{ recipient with silentPaymentAddress := some "sp1qnotacode" }] }]
  for (outputs, n) in invalid.zipIdx do
    let entry : HistoryEntry := { txid := ByteArray.mk (Array.replicate 32 0x11), height := 1, received := 0, spent := 50_000,
                                  outputs := some outputs }
    check s!"invalid metadata {n} refused" (SwiftJSON.decodeText (SwiftJSON.write entry.toJV) HistoryEntry.ofJV).toOption.isNone
  let tx := makeFakeSegwitTx
  let entry : HistoryEntry := { txid := tx.txid, height := 1, received := 0, spent := 50_000,
                                rawTransaction := some (tx.serialized false), outputs := some { external := #[recipient] } }
  check "invalid metadata: contradicts the bytes" entry.transaction.toOption.isNone

def contradictedImportedMetadataIsDropped : TM Unit := do
  let path ← tempPath "contradicted-outputs-wallet.json"
  let keyStore ← newKeyStore
  let tx := makeFakeSegwitTx
  let source ← wmT "source" (Wallet.create .signet (← newKeyStore) none (some (ByteArray.mk (Array.replicate 16 0))) 400 0 pinned)
  let wrongClaim : HistoryEntry.Outputs :=
    { external := #[{ vout := 0, amount := tx.outputs[0]!.value + 1, scriptPubKey := tx.outputs[0]!.scriptPubKey }] }
  let claimed : ImportBundle.KnownTransaction :=
    { txid := displayHex tx.txid, height := 0, received := 0, spent := 0, outputs := some wrongClaim }
  let bundle : ImportBundle :=
    { network := "signet", descriptor := some source.descriptor.serialized,
      mnemonic := some "abandon abandon abandon abandon abandon abandon abandon abandon abandon abandon abandon about",
      lastKnownHeight := 500, transactions := #[claimed] }
  let w ← wmT "import" (Wallet.importing bundle keyStore (some path) pinned)
  check "imported: metadata without bytes accepted" (((← w.history)[0]?.bind (·.outputs)).isSome)
  discard (wmT "confirm" (w.apply (fakeMatch 600 #[tx])))
  let some confirmed := (← w.history).find? (·.txid == tx.txid) | throw "no entry"
  check "imported: confirmed" (confirmed.height == 600)
  check "imported: bytes" confirmed.rawTransaction.isSome
  check "imported: contradicted breakdown dropped" confirmed.outputs.isNone
  let reopened ← wmT "open" (Wallet.open path keyStore pinned)
  let some entry := (← reopened.history).find? (·.txid == tx.txid) | throw "no entry"
  check "imported: reopened without outputs" entry.outputs.isNone
  check "imported: transaction" ((entry.transaction.toOption.bind id).map (·.txid) == some tx.txid)

/-! ## KeyStoreTests.accountSerialization and the account-key wallet (AccountKeyCustodyTests, signing) -/

def parsesTo (b : ByteArray) (expected : Except KeyStoreError WalletSecret) : Bool :=
  match WalletSecret.parse b, expected with
  | .ok a, .ok b => a == b
  | .error a, .error b => a == b
  | _, _ => false

def accountSecrets : TM Unit := do
  let words := "abandon abandon abandon abandon abandon abandon abandon abandon abandon abandon abandon about"
  let m ← needE "master" (·.name) (HDKey.ofSeed (BIP39.seed words))
  let key := (← needE "account" (·.name) (BIP86.accountKey m 1 0)).serialized .testnet
  let secret := WalletSecret.accountKey key 0x73c5da0a
  check "secret: account bytes" (secret.serialized == s!"account/1\n73c5da0a\n{key}".toUTF8)
  check "secret: account round trip" (parsesTo secret.serialized (.ok secret))
  check "secret: mnemonic bytes" ((WalletSecret.mnemonic words).serialized == s!"mnemonic\n{words}".toUTF8)
  check "secret: xprv bytes" ((WalletSecret.masterKey key).serialized == s!"xprv\n{key}".toUTF8)
  for (bad, n) in ["account/1", "account/1\n73c5da0a", s!"account/1\n73C5DA0A\n{key}", s!"account/1\n73c5da0\n{key}",
      s!"account/1\n73c5da0a\n{key}\nextra", s!"account/1x\n73c5da0a\n{key}", s!"account/\n73c5da0a\n{key}",
      s!"account/1 \n73c5da0a\n{key}"].zipIdx do
    check s!"secret: malformed {n}" (parsesTo bad.toUTF8 (.error .malformedSecret))
  check "secret: version 2" (parsesTo s!"account/2\n73c5da0a\n{key}".toUTF8 (.error (.unsupportedSecretVersion "account/2")))
  check "secret: version 2, payload not echoed" (parsesTo s!"account/2{key}".toUTF8 (.error (.unsupportedSecretVersion "account/2")))

/-- An account-key wallet signs its own sends and, as a multisig signer, an account's spend. -/
def accountKeyWallet : TM Unit := do
  let ms ← masters
  let accountKey ← accountKeyOf ms[0]!
  let keyStore ← newKeyStore
  let w ← wmT "create" (Wallet.createFromAccountKey accountKey ms[0]!.fingerprint .signet keyStore none 100 0 pinned)
  let words ← needE "mnemonic" (fun _ => "bip39") (BIP39.mnemonic (ByteArray.mk (Array.replicate 16 0xA1)))
  let fromSeed ← wmT "create" (Wallet.create .signet (← newKeyStore) none (some (ByteArray.mk (Array.replicate 16 0xA1))) 100 0 pinned)
  check "account wallet: same descriptor as the seed wallet" (w.descriptor.serialized == fromSeed.descriptor.serialized) words
  let signing ← wmT "signing key" w.multisigSigningKey
  check "account wallet: signing key" (signing.publicKey == accountKey.publicKey && signing.isPrivate)
  let (account, _) ← accountWith
  check "account wallet: signs as a signer" (account.hasSigner signing)
  let wrong ← accountKeyOf ms[1]!
  match ← (Wallet.createFromAccountKey wrong.neutered 0 .signet (← newKeyStore) none 100 0 pinned).run with
  | .error (.wallet .accountKeyMismatch) => check "account wallet: public key refused" true
  | _ => check "account wallet: public key refused" false

/-! ## FeeResolutionTests (the pure parts; `livePoolMajority` needs the pool's floor aggregation, not ported) -/

def feeResolution : TM Unit := do
  let r := FeePolicy.resolution (estimated := some 10) (observed := #[5]) (floor := some 200) (peerFloorCap := some 120)
  check "fee: capped floor rate" (r.rate == 120 && r.clampedFloor == some 200)
  let o := FeePolicy.resolution (override := some 250) (floor := some 200) (peerFloorCap := some 120)
  check "fee: override above floor" (o.rate == 250 && o.clampedFloor.isNone)
  let ob := FeePolicy.resolution (observed := #[300]) (floor := some 200) (peerFloorCap := some 120)
  check "fee: observed above floor" (ob.rate == 300 && ob.clampedFloor.isNone)
  check "fee: estimate cannot undercut median" ((FeePolicy.resolution (estimated := some 1) (observed := #[10, 30])).rate == 20)
  check "fee: higher estimate" ((FeePolicy.resolution (estimated := some 40) (observed := #[10, 30])).rate == 40)
  check "fee: override wins" ((FeePolicy.resolution (override := some 1) (estimated := some 40) (observed := #[30])).rate == 1)
  check "fee: preset" ((FeePolicy.resolution .high).rate == 12)
  let nan : Float := 0.0 / 0.0
  let inf : Float := 1.0 / 0.0
  for (rate, n) in [nan, inf, -inf, -1, 0, 10_001].zipIdx do
    let q := FeePolicy.resolution (override := some rate) (estimated := some rate) (observed := #[rate, 7])
      (floor := some rate) (peerFloorCap := some 120)
    check s!"fee: invalid rate {n} falls through" (q.rate == 7 && q.clampedFloor.isNone)
    check s!"fee: invalid rate {n} not accepted" (!FeePolicy.acceptsRate rate)
  let none0 := FeePolicy.resolution .low (floor := some 2_000) (peerFloorCap := some 0)
  check "fee: cap zero" (none0.rate == 2 && none0.clampedFloor == some 2_000)
  check "fee: negative cap is zero" (FeePolicy.resolution .low (floor := some 2_000) (peerFloorCap := some (-5)) == none0)
  let huge := FeePolicy.resolution .low (floor := some 2_000) (peerFloorCap := some 1e9)
  check "fee: huge cap" (huge.rate == 2_000 && huge.clampedFloor.isNone)
  check "fee: uncapped" ((FeePolicy.resolution .low (floor := some 2_000) (peerFloorCap := none)).rate == 2_000)
  check "fee: accepts 1 and 10000" (FeePolicy.acceptsRate 1 && FeePolicy.acceptsRate 10_000)
  let d := FeePolicy.resolution (floor := some 200)
  check "fee: default cap" (d.rate == 120 && d.clampedFloor == some 200)
  check "fee: default uncapped" ((FeePolicy.resolution (floor := some 200) (peerFloorCap := none)).rate == 200)
  check "fee: resolve is uncapped" (FeePolicy.resolve (floor := some 200) == 200)
  check "fee: resolve override" (FeePolicy.resolve (override := some 300) (floor := some 200) == 300)
  check "fee: seat majority, lone peer" (FeePolicy.seatMajorityFloor #[200] 3 == none)
  check "fee: seat majority 2" (FeePolicy.seatMajorityFloor #[2, 200] 3 == some 2)
  check "fee: seat majority 3" (FeePolicy.seatMajorityFloor #[2, 3, 200] 3 == some 3)
  check "fee: one seat" (FeePolicy.seatMajorityFloor #[200] 1 == some 200)
  check "fee: no seats" (FeePolicy.seatMajorityFloor #[] 0 == none)
  check "fee: NaN counts as zero" (FeePolicy.seatMajorityFloor #[nan, 200] 3 == none)

/-! ## NestedMultisigTests (upstream d2ca878, #256; the three Ledger cases are in `ledger-test`) -/

def hasText (s t : String) : Bool := (s.splitOn t).length > 1
def sortedNats (xs : Array Nat) : List Nat := xs.toList.mergeSort
def sortedInts (xs : Array Int) : List Int := xs.toList.mergeSort

/-- Members of a nested test account: the masters, the members' key expressions, the account. -/
structure Family where
  masters : Array HDKey
  members : Array (Array String)
  account : MultisigAccount

/-- The signers' leaf whose keys are exactly these masters', by position. -/
def Family.leafOf (f : Family) (holders : List Nat) : TM SpendPath := do
  let wanted := MultisigAccount.asSet (← holders.toArray.mapM fun h => return (← accountKeyOf f.masters[h]!).publicKey)
  let some position := f.account.signersLeaves.findIdx? fun leaf =>
      MultisigAccount.asSet (leaf.keys.map MultisigAccount.identity) == wanted
    | throw s!"no leaf of {holders}"
  return .signers position

/-- The pairs `holder`'s key takes in the leaves it sits in, signers' or recovery, in tree order. -/
def Family.appearances (f : Family) (holder : Nat) : TM (Array Nat) := do
  let id := (← accountKeyOf f.masters[holder]!).publicKey
  return (f.account.allKeys.filter (MultisigAccount.identity · == id)).filterMap
    (MultisigAccount.appearance? ·.derivation.elements)

/-- Member A holds two keys (a phone and its Ledger, both software here), B and C one each. -/
def nestedFamily (threshold : Int := 2) (recovery : Option RecoveryPlan := none) : TM Family := do
  let ms ← #[0xA1, 0xB2, 0xC3, 0xD4].mapM master
  let keys ← ms.mapM keyExpression
  let members := #[#[keys[0]!, keys[1]!], #[keys[2]!], #[keys[3]!]]
  let d ← need "nested descriptor" (MultisigAccount.makeNestedDescriptor (members.map .all) threshold recovery .signet)
  return { masters := ms, members, account := ← need "nested account" (MultisigAccount.make d .signet) }

/-- Member A is a 2-of-3 account (masters 0, 1 and 2), B and C one key each (3 and 4). -/
def estate (threshold : Int := 2) (recovery : Option RecoveryPlan := none) : TM Family := do
  let ms ← #[0xA1, 0xB2, 0xC3, 0xD4, 0xE5].mapM master
  let keys ← ms.mapM keyExpression
  let members : Array MultisigAccount.Member :=
    #[{ keys := keys.extract 0 3, threshold := 2 }, .all #[keys[3]!], .all #[keys[4]!]]
  let d ← need "estate descriptor" (MultisigAccount.makeNestedDescriptor members threshold recovery .signet)
  return { masters := ms, members := members.map (·.keys), account := ← need "estate account" (MultisigAccount.make d .signet) }

def nfunding (a : MultisigAccount) : TM WalletUTXO := funding a 100_000 .receive 0 100 0x6E

def nspend (a : MultisigAccount) (coin : WalletUTXO) (path : SpendPath := .signers) (tip : UInt32 := 101) : MAM PSBT :=
  a.createSpend #[coin] #[{ amount := 40_000, scriptPubKey := destination }] 0 2 tip path (0.5, 0.5)

/-- The paths among `paths` with their threshold of verified signatures. -/
def finished (a : MultisigAccount) (p : PSBT) (coin : WalletUTXO) (paths : Array SpendPath) : TM (Array SpendPath) :=
  paths.filterM fun path => do return ((← need "ap" (a.approvals p #[coin] path)).size : Int) ≥ a.thresholdOn path

def nestedBuilder : TM Unit := do
  let f ← nestedFamily
  let a := f.account
  check "nested builder: nested" a.isNested
  check "nested builder: three leaves" (a.signersLeaves.size == 3)
  check "nested builder: leaf sizes" (sortedNats (a.signersLeaves.map (·.keys.size)) == [2, 3, 3])
  check "nested builder: each leaf needs every key, sorted" (a.signersLeaves.all fun l => l.threshold == l.keys.size && l.isSorted)
  check "nested builder: four signers, no recovery" (a.signers.size == 4 && a.recovery.isNone)
  check "nested builder: summary" (a.policySummary == "2 of 3 members") a.policySummary
  let some members := a.members | throw "no members"
  check "nested builder: members" (members.threshold == 2 && sortedNats (members.groups.map (·.size)) == [1, 1, 2])
  -- Each key sits in two leaves: on /<0;1>/* first, /<2;3>/* after.
  let mut appearances : Array (ByteArray × Array Nat) := #[]
  for leaf in a.signersLeaves do
    for key in leaf.keys do
      let some n := MultisigAccount.appearance? key.derivation.elements | throw "a key on no pair"
      let id := MultisigAccount.identity key
      appearances := match appearances.findIdx? (·.1 == id) with
        | some j => appearances.modify j fun (k, ns) => (k, ns.push n)
        | none => appearances.push (id, #[n])
  check "nested builder: pairs in turn" (appearances.size == 4 && appearances.all (·.2 == #[0, 1]))
  let text := a.descriptor.serialized
  check "nested builder: text" (text.startsWith "tr(tpub" && hasText text "{{sortedmulti_a(" && hasText text "/<2;3>/*") text
  let again ← need "reparse" (MultisigAccount.parse text .signet)
  check "nested builder: round trip" (again.signersLeaves == a.signersLeaves)
  check "nested builder: same addresses" ((← need "a" (again.address 3 1)) == (← need "a" (a.address 3 1)))
  check "nested builder: includes" (a.includes (← accountKeyOf f.masters[3]!).neutered)
  check "nested builder: hasSigner" (a.hasSigner f.masters[1]!)

def nestedOrderDoesNotMatter : TM Unit := do
  let f ← nestedFamily
  let keys := f.members
  let shuffled := #[keys[2]!, #[keys[0]![1]!, keys[0]![0]!], keys[1]!]
  let other ← need "other" (MultisigAccount.makeNestedDescriptor (shuffled.map .all) 2 none .signet)
  check "nested order: one descriptor" (other.serialized == f.account.descriptor.serialized)
  let flat ← need "flat" (MultisigAccount.makeNestedDescriptor (#[#[keys[0]![0]!], keys[1]!, keys[2]!].map .all) 2 none .signet)
  let plain ← need "plain" (MultisigAccount.makeDescriptor 2 #[keys[0]![0]!, keys[1]![0]!, keys[2]![0]!] none .signet)
  check "nested order: single-key members are the ordinary account" (flat.serialized == plain.serialized)
  check "nested order: not nested" (!(← need "flat account" (MultisigAccount.make flat .signet)).isNested)

def thresholdMember : TM Unit := do
  let e ← estate
  let a := e.account
  check "threshold member: nested, seven leaves" (a.isNested && a.signersLeaves.size == 7)
  check "threshold member: leaf sizes" (sortedNats (a.signersLeaves.map (·.keys.size)) == [2, 3, 3, 3, 3, 3, 3])
  check "threshold member: each leaf needs every key" (a.signersLeaves.all fun l => l.threshold == l.keys.size && l.isSorted)
  check "threshold member: five signers" (a.signers.size == 5 && a.recovery.isNone)
  check "threshold member: summary" (a.policySummary == "2 of 3 members, one of them 2 of 3") a.policySummary
  let some members := a.members | throw "no members"
  check "threshold member: members" (members.threshold == 2 && sortedNats (members.groups.map (·.size)) == [1, 1, 3])
  check "threshold member: thresholds" (sortedNats members.thresholds == [1, 1, 2])
  let some family := members.thresholdGroups[0]? | throw "no threshold group"
  check "threshold member: one threshold group of three" (members.thresholdGroups.size == 1 && members.groups[family]!.size == 3)
  let familyKeys ← (e.masters.extract 0 3).mapM fun m => return (← accountKeyOf m).publicKey
  check "threshold member: the family's keys"
    (MultisigAccount.asSet (members.groups[family]!.map MultisigAccount.identity) == MultisigAccount.asSet familyKeys)
  for pair in [[0, 1], [0, 2], [1, 2]] do
    discard (e.leafOf (pair ++ [3]))
    discard (e.leafOf (pair ++ [4]))
  discard (e.leafOf [3, 4])
  for holder in [0:5] do
    check s!"threshold member: holder {holder} takes four pairs" ((← e.appearances holder) == #[0, 1, 2, 3])
  let again ← need "reparse" (MultisigAccount.parse a.descriptor.serialized .signet)
  check "threshold member: round trip" (again.signersLeaves == a.signersLeaves && again.members == some members)
  check "threshold member: same addresses" ((← need "a" (again.address 2 1)) == (← need "a" (a.address 2 1)))
  check "threshold member: control block depths"
    (sortedNats ((← need "leaves" (a.leaves 0 0)).map (·.controlBlock.path.size)) == [2, 3, 3, 3, 3, 3, 3])

def thresholdOrderDoesNotMatter : TM Unit := do
  let e ← estate
  let keys := e.members
  let shuffled : Array MultisigAccount.Member :=
    #[.all keys[2]!, { keys := #[keys[0]![2]!, keys[0]![0]!, keys[0]![1]!], threshold := 2 }, .all keys[1]!]
  let other ← need "other" (MultisigAccount.makeNestedDescriptor shuffled 2 none .signet)
  check "threshold order: one descriptor" (other.serialized == e.account.descriptor.serialized)
  let whole ← need "whole" (MultisigAccount.makeNestedDescriptor #[{ keys := keys[0]!, threshold := 3 }, .all keys[1]!, .all keys[2]!] 2 none .signet)
  let plainNested ← need "plain nested" (MultisigAccount.makeNestedDescriptor (keys.map .all) 2 none .signet)
  check "threshold order: a member needing every key is the plain nested account" (whole.serialized == plainNested.serialized)
  check "threshold order: three leaves" ((← need "whole account" (MultisigAccount.make whole .signet)).signersLeaves.size == 3)
  let both ← need "both" (do
    MultisigAccount.make (← MultisigAccount.makeNestedDescriptor #[{ keys := keys[0]!, threshold := 2 }, .all keys[1]!] 2 none .signet) .signet)
  check "threshold order: the family and B" (both.signersLeaves.size == 3 && both.policySummary == "2 of 2 members, one of them 2 of 3")
    both.policySummary
  check "threshold order: thresholds" ((both.members.map (·.thresholds)) == some #[2, 1] || (both.members.map (·.thresholds)) == some #[1, 2])

def nestedBuilderRefusals : TM Unit := do
  let pairs ← (Array.range 15).mapM fun i => do keyExpression (← master (0x10 + i.toUInt8))
  let members := (Array.range 7).map fun i => #[pairs[2 * i]!, pairs[2 * i + 1]!]
  refusedWith "nested refusals: 35 leaves" (MultisigAccount.makeNestedDescriptor (members.map .all) 4 none .signet)
    (.invalidDescriptor "these members would make 35 leaves, and an account has at most 32")
  let six ← need "six" (do MultisigAccount.make (← MultisigAccount.makeNestedDescriptor ((members.extract 0 6).map .all) 3 none .signet) .signet)
  check "nested refusals: 3 of 6 pairs, 20 leaves" (six.signersLeaves.size == 20 && (six.members.map (·.threshold)) == some 3)
  let triples : Array MultisigAccount.Member := (Array.range 5).map fun i => { keys := pairs.extract (3 * i) (3 * i + 3), threshold := 2 }
  let threeFamilies ← need "three families" (do
    MultisigAccount.make (← MultisigAccount.makeNestedDescriptor (triples.extract 0 3) 2 none .signet) .signet)
  check "nested refusals: three families, 27 leaves"
    (threeFamilies.signersLeaves.size == 27 && threeFamilies.policySummary == "2 of 3 members, three of them 2 of 3")
    threeFamilies.policySummary
  check "nested refusals: three groups of three" ((threeFamilies.members.map (·.groups.map (·.size))) == some #[3, 3, 3])
  refusedWith "nested refusals: 36 leaves"
    (MultisigAccount.makeNestedDescriptor (triples.extract 0 3) 2 (some (.fewerSigners 1 10)) .signet)
    (.invalidDescriptor "these members would make 36 leaves, and an account has at most 32")
  refusedWith "nested refusals: 270 leaves" (MultisigAccount.makeNestedDescriptor triples 3 none .signet)
    (.invalidDescriptor "these members would make 270 leaves, and an account has at most 32")
  check "nested refusals: leafCount saturates" (MultisigAccount.leafCount (Array.replicate 15 6_435) 8 == MultisigAccount.intMax)
  refusedWith "nested refusals: member threshold above its keys"
    (MultisigAccount.makeNestedDescriptor #[{ keys := pairs.extract 0 3, threshold := 4 }, .all #[pairs[3]!]] 2 none .signet)
    (.invalidDescriptor "a member's threshold must be between one and its number of keys")
  refused "nested refusals: one member alone, one key signing"
    (MultisigAccount.makeNestedDescriptor #[{ keys := pairs.extract 0 3, threshold := 1 }, .all #[pairs[3]!, pairs[4]!]] 1 none .signet)
    (account := true)
  let anyFamily ← need "any family" (do
    MultisigAccount.make (← MultisigAccount.makeNestedDescriptor #[{ keys := pairs.extract 0 3, threshold := 2 }, .all #[pairs[3]!, pairs[4]!]] 1 none .signet) .signet)
  check "nested refusals: one of two members" (anyFamily.signersLeaves.size == 4 && anyFamily.policySummary == "1 of 2 members, one of them 2 of 3")
    anyFamily.policySummary
  let separate ← nestedFamily (recovery := some (.separateKeys 1 #[← keyExpression (← master 0xE5)] 10))
  check "nested refusals: a separate recovery key" ((separate.account.recovery.map (·.keys.size)) == some 1 && separate.account.signersLeaves.size == 3)
  check "nested refusals: four leaves" ((← need "leaves" (separate.account.leaves 0 0)).size == 4)
  let f ← nestedFamily
  refused "nested refusals: a member's key as the separate recovery key"
    (MultisigAccount.makeNestedDescriptor (f.members.map .all) 2 (some (.separateKeys 1 #[f.members[1]![0]!] 10)) .signet) (account := true)
  refused "nested refusals: a key in two members"
    (MultisigAccount.makeNestedDescriptor (#[#[pairs[0]!, pairs[1]!], #[pairs[1]!]].map .all) 1 none .signet) (account := true)
  refused "nested refusals: one member"
    (MultisigAccount.makeNestedDescriptor (#[#[pairs[0]!, pairs[1]!]].map .all) 1 none .signet) (account := true)
  refused "nested refusals: one of three, one-key members"
    (MultisigAccount.makeNestedDescriptor (#[#[pairs[0]!, pairs[1]!], #[pairs[2]!], #[pairs[3]!]].map .all) 1 none .signet) (account := true)
  let anyPair ← need "any pair" (do MultisigAccount.make (← MultisigAccount.makeNestedDescriptor ((members.extract 0 3).map .all) 1 none .signet) .signet)
  check "nested refusals: any one of three pairs" (anyPair.signersLeaves.size == 3 && (anyPair.members.map (·.threshold)) == some 1)
  let everyone ← need "everyone" (do MultisigAccount.make (← MultisigAccount.makeNestedDescriptor ((members.extract 0 2).map .all) 2 none .signet) .signet)
  check "nested refusals: every member is the ordinary account"
    (!everyone.isNested && everyone.threshold == 4 && everyone.signers.size == 4)
  let flat ← need "flat" (MultisigAccount.makeDescriptor 4 (pairs.extract 0 4) none .signet)
  check "nested refusals: the same descriptor" (everyone.descriptor.serialized == flat.serialized)

def nestedAdmissionRefusals : TM Unit := do
  let ms ← #[0xA1, 0xB2, 0xC3].mapM master
  let keys ← ms.mapM bareKeyExpression
  let nums := hex Taproot.unspendableInternalKey
  let k0 := keys[0]!
  let k1 := keys[1]!
  let k2 := keys[2]!
  let good := s!"tr({nums},\{sortedmulti_a(2,{k0}/<0;1>/*,{k1}/<0;1>/*),sortedmulti_a(2,{k0}/<2;3>/*,{k2}/<0;1>/*)})"
  let a ← need "good" (MultisigAccount.parse good .signet)
  check "nested admission: summary" (a.isNested && a.policySummary == "2 of 2 members, one of them 1 of 2") a.policySummary
  check "nested admission: members"
    ((a.members.map (·.groups.map (·.size))) == some #[1, 2] && (a.members.map (·.thresholds)) == some #[1, 1])
  let shapeless := s!"tr({nums},\{sortedmulti_a(2,{k0}/<0;1>/*,{k1}/<0;1>/*),sortedmulti_a(3,{k0}/<2;3>/*,{k1}/<2;3>/*,{k2}/<0;1>/*)})"
  let odd ← need "shapeless" (MultisigAccount.parse shapeless .signet)
  check "nested admission: not a tree of members" (odd.isNested && odd.members.isNone && odd.policySummary == "2 signing groups")
    odd.policySummary
  let relabelled := "[deadbeef" ++ String.ofList (k0.toList.drop 9)
  let refusedTrees := [
    s!"\{sortedmulti_a(2,{k0}/<0;1>/*,{k1}/<0;1>/*),sortedmulti_a(2,{k0}/<0;1>/*,{k2}/<0;1>/*)}",
    s!"\{sortedmulti_a(2,{k0}/<0;1>/*,{k1}/<0;1>/*),sortedmulti_a(2,{k0}/<4;5>/*,{k2}/<0;1>/*)}",
    s!"\{sortedmulti_a(2,{k0}/<0;1>/*,{k1}/<0;1>/*),sortedmulti_a(2,{k0}/<2;3>/*,{k1}/<2;3>/*)}",
    s!"\{sortedmulti_a(2,{k0}/<0;1>/*,{k1}/<0;1>/*),multi_a(1,{k2}/<0;1>/*)}",
    s!"\{sortedmulti_a(2,{k0}/<0;1>/*,{k1}/<0;1>/*),sortedmulti_a(2,{relabelled}/<2;3>/*,{k2}/<0;1>/*)}",
    s!"\{\{sortedmulti_a(2,{k0}/<0;1>/*,{k1}/<0;1>/*),and_v(v:pk({k2}/<0;1>/*),older(10))},and_v(v:pk({k2}/<2;3>/*),older(20))}",
    s!"\{\{sortedmulti_a(2,{k0}/<0;1>/*,{k1}/<0;1>/*),and_v(v:pk({k2}/<0;1>/*),older(10))},and_v(v:pk({k2}/<2;3>/*),older(10))}",
    s!"\{\{sortedmulti_a(2,{k0}/<0;1>/*,{k1}/<0;1>/*),and_v(v:pk({k2}/<0;1>/*),older(10))},and_v(v:pk({k0}/<4;5>/*),older(10))}"]
  for (tree, n) in refusedTrees.zipIdx do
    refused s!"nested admission: refused {n}" (MultisigAccount.parse s!"tr({nums},{tree})" .signet) (account := true)
  let withRecovery := s!"tr({nums},\{\{sortedmulti_a(2,{k0}/<0;1>/*,{k1}/<0;1>/*),sortedmulti_a(2,{k0}/<2;3>/*,{k2}/<0;1>/*)},and_v(v:pk({k0}/<4;5>/*),older(10))})"
  let recovering ← need "with recovery" (MultisigAccount.parse withRecovery .signet)
  check "nested admission: a recovery leaf beside two signers' leaves"
    ((recovering.recovery.map (·.blocks)) == some 10 && recovering.signersLeaves.size == 2)
  check "nested admission: leaf kinds" ((← need "leaves" (recovering.leaves 0 0)).map (·.isRecovery) == #[false, false, true])
  let twoLeaves := s!"tr({nums},\{\{sortedmulti_a(2,{k0}/<0;1>/*,{k1}/<0;1>/*),sortedmulti_a(2,{k0}/<2;3>/*,{k2}/<0;1>/*)},\{and_v(v:pk({k0}/<4;5>/*),older(10)),and_v(v:multi_a(2,{k1}/<2;3>/*,{k2}/<2;3>/*),older(10))}})"
  let twice ← need "two recovery leaves" (MultisigAccount.parse twoLeaves .signet)
  check "nested admission: two recovery leaves" (twice.recoveryLeaves.size == 2 && twice.recoveryPaths == #[.recovery, .recovery 1])
  check "nested admission: the second recovery leaf" ((twice.keysOn (.recovery 1)).size == 2 && twice.thresholdOn (.recovery 1) == 2)
  check "nested admission: recovery members"
    ((twice.recoveryMembers.map (·.threshold)) == some 1 && (twice.recoveryMembers.map (·.groups.map (·.size))) == some #[1, 2])
  check "nested admission: every key, no third recovery leaf" (twice.allKeys.size == 7 && (twice.keysOn (.recovery 2)).isEmpty)
  check "nested admission: path text" ((SpendPath.recovery 1).description == "recovery(1)" && (SpendPath.recovery).isRecovery)

def nestedSpends : TM Unit := do
  let f ← nestedFamily
  let a := f.account
  let coin ← nfunding a
  let mut psbt ← need "create" (nspend a coin)
  check "nested spends: three leaves on the input" (psbt.inputs[0]!.tapLeafScripts.size == 3)
  let some changeTree := psbt.outputs.findSome? (·.tapTree) | throw "no change tree"
  let leaves ← need "leaves" (a.leaves 1 0)
  check "nested spends: change tree scripts" (changeTree.map (·.2.2) == (leaves.map (·.script)).reverse)
  check "nested spends: change tree depths" (changeTree.map (·.1.toNat) == (leaves.map (·.controlBlock.path.size)).reverse)
  check "nested spends: depths" (sortedNats (changeTree.map (·.1.toNat)) == [1, 2, 2])
  let ab ← f.leafOf [0, 1, 2]
  let ac ← f.leafOf [0, 1, 3]
  let bc ← f.leafOf [2, 3]
  let ap (p : PSBT) (path : SpendPath) : TM (Array Nat) := need "ap" (a.approvals p #[coin] path)
  psbt ← need "sign 0" (sign a psbt f.masters[0]! #[coin] 101)
  check "nested spends: A's phone on both of A's leaves"
    ((← ap psbt ab).size == 1 && (← ap psbt ac).size == 1 && (← ap psbt bc).isEmpty)
  check "nested spends: nothing finishes" (!psbt.finalize.toBool)
  psbt ← need "sign 1" (sign a psbt f.masters[1]! #[coin] 101)
  check "nested spends: one whole member is one member" ((← ap psbt ab).size == 2 && !psbt.finalize.toBool)
  psbt ← need "sign 2" (sign a psbt f.masters[2]! #[coin] 101)
  check "nested spends: B completes A and B" ((← ap psbt ab).size == 3 && (← ap psbt bc).size == 1)
  let tx ← need "finalize" (finalize a psbt #[coin] 101)
  let w := tx.inputs[0]!.witness
  check "nested spends: three signatures" (w.size == 5 && (w.extract 0 3).all (·.size == 64))
  let receiveLeaves ← need "leaves" (a.leaves 0 0)
  let some abLeaf := receiveLeaves.find? (·.path == ab) | throw "no ab leaf"
  check "nested spends: the A-and-B leaf" (w[3]! == abLeaf.script)
  check "nested spends: its control block" (w[4]!.size == 33 + 32 * abLeaf.controlBlock.path.size)
  check "nested spends: estimate covers it" ((witnessSize w : Int) ≤ (← need "w" (a.witnessBytesPerInput .signers)))
  let mut other ← need "create" (nspend a coin)
  for holder in [2, 3] do other ← need "sign" (sign a other f.masters[holder]! #[coin] 101)
  check "nested spends: B and C" ((← ap other bc) == #[0, 1])
  let second ← need "finalize" (finalize a other #[coin] 101)
  let some bcLeaf := receiveLeaves.find? (·.path == bc) | throw "no bc leaf"
  check "nested spends: B and C's witness" (second.inputs[0]!.witness.size == 4 && second.inputs[0]!.witness[2]! == bcLeaf.script)

def thresholdMemberSpends : TM Unit := do
  let e ← estate
  let a := e.account
  let coin ← nfunding a
  let mut psbt ← need "create" (nspend a coin)
  check "threshold spends: seven leaves on the input" (psbt.inputs[0]!.tapLeafScripts.size == 7)
  let signAs (holder : Nat) (p : PSBT) : TM PSBT := need s!"sign {holder}" (sign a p e.masters[holder]! #[coin] 101)
  psbt ← signAs 0 psbt
  psbt ← signAs 3 psbt
  check "threshold spends: one family key and B finish nothing" ((← finished a psbt coin a.signersPaths).isEmpty && !psbt.finalize.toBool)
  let mut familyOnly ← need "create" (nspend a coin)
  for holder in [0, 1, 2] do familyOnly ← signAs holder familyOnly
  check "threshold spends: the whole family alone finishes nothing"
    ((← finished a familyOnly coin a.signersPaths).isEmpty && !familyOnly.finalize.toBool)
  psbt ← signAs 1 psbt
  let complete ← finished a psbt coin a.signersPaths
  check "threshold spends: exactly the leaf of those keys and B" (complete == #[← e.leafOf [0, 1, 3]])
  let tx ← need "finalize" (finalize a psbt #[coin] 101)
  let w := tx.inputs[0]!.witness
  check "threshold spends: three signatures" (w.size == 5 && (w.extract 0 3).all (·.size == 64))
  let some leaf := (← need "leaves" (a.leaves 0 0)).find? (·.path == complete[0]!) | throw "no leaf"
  check "threshold spends: that leaf's script" (w[3]! == leaf.script)
  check "threshold spends: estimate covers it" ((witnessSize w : Int) ≤ (← need "w" (a.witnessBytesPerInput .signers)))
  let mut generous ← need "create" (nspend a coin)
  for holder in [0, 1, 2, 4] do generous ← signAs holder generous
  check "threshold spends: three leaves could finish" ((← finished a generous coin a.signersPaths).size == 3)
  check "threshold spends: one leaf's three signatures" ((← need "finalize" (finalize a generous #[coin] 101)).inputs[0]!.witness.size == 5)

def fewerMembersRecovery : TM Unit := do
  let e ← estate (recovery := some (.fewerSigners 1 10))
  let a := e.account
  check "fewer members: 7 and 5 leaves" (a.signersLeaves.size == 7 && a.recoveryLeaves.size == 5)
  check "fewer members: every recovery leaf after 10, every key" (a.recoveryLeaves.all fun r => r.blocks == 10 && r.threshold == r.keys.size)
  check "fewer members: recovery leaf sizes" (sortedNats (a.recoveryLeaves.map (·.keys.size)) == [1, 1, 2, 2, 2])
  check "fewer members: leaf kinds"
    ((← need "leaves" (a.leaves 0 0)).map (·.isRecovery) == Array.replicate 7 false ++ Array.replicate 5 true)
  let some members := a.recoveryMembers | throw "no recovery members"
  check "fewer members: recovery members"
    (members.threshold == 1 && members.groups.size == 3 && sortedNats members.thresholds == [1, 1, 2])
  check "fewer members: summary" (a.policySummary == "2 of 3 members, one of them 2 of 3") a.policySummary
  check "fewer members: a family key's pairs" ((← e.appearances 0) == #[0, 1, 2, 3, 4, 5])
  check "fewer members: B's pairs" ((← e.appearances 3) == #[0, 1, 2, 3, 4])
  let again ← need "reparse" (MultisigAccount.parse a.descriptor.serialized .signet)
  check "fewer members: round trip" (again.recoveryLeaves == a.recoveryLeaves && again.recoveryMembers == some members)
  let text := a.descriptor.serialized
  check "fewer members: text" (hasText text "and_v(v:multi_a(2," && hasText text "/<10;11>/*")
  let coin ← nfunding a
  refused "fewer members: no recovery yet" (nspend a coin .recovery) (account := true)
  let recoverySpend : TM PSBT := need "create recovery" (nspend a coin .recovery 109)
  let signAs (holder : Nat) (p : PSBT) : TM PSBT := need s!"sign {holder}" (sign a p e.masters[holder]! #[coin] 109)
  let mut later ← recoverySpend
  check "fewer members: review path" ((← need "review" (a.reviewSpend later #[coin] owned 109)).path == .recovery)
  check "fewer members: twelve leaves on the input" (later.inputs[0]!.tapLeafScripts.size == 12)
  later ← signAs 2 later
  let holding ← a.recoveryPaths.filterM fun path => return !(← need "ap" (a.approvals later #[coin] path)).isEmpty
  check "fewer members: one family key on its two recovery leaves" (holding.size == 2)
  check "fewer members: neither complete" ((← finished a later coin a.recoveryPaths).isEmpty && !later.finalize.toBool)
  later ← signAs 1 later
  let complete ← finished a later coin a.recoveryPaths
  check "fewer members: exactly one recovery leaf" (complete.size == 1 && (a.keysOn complete[0]!).size == 2)
  check "fewer members: no signers' leaf" (← finished a later coin a.signersPaths).isEmpty
  let tx ← need "finalize" (finalize a later #[coin] 109)
  check "fewer members: sequence and witness" (tx.inputs[0]!.sequence == 10 && tx.inputs[0]!.witness.size == 4)
  check "fewer members: estimate covers it"
    ((witnessSize tx.inputs[0]!.witness : Int) ≤ (← need "w" (a.witnessBytesPerInput .recovery)))
  let mut bob ← recoverySpend
  bob ← signAs 3 bob
  let bobFingerprint := e.masters[3]!.fingerprint
  let some bobLeaf := a.recoveryPaths.find? fun path =>
      (a.keysOn path).size == 1 && ((a.keysOn path)[0]!.origin.map (·.fingerprint)) == some bobFingerprint
    | throw "no leaf of B's"
  check "fewer members: B alone recovers" ((← finished a bob coin a.recoveryPaths) == #[bobLeaf])
  check "fewer members: B's witness" ((← need "finalize" (finalize a bob #[coin] 109)).inputs[0]!.witness.size == 3)
  let mut twoMembers ← recoverySpend
  for holder in [3, 4] do twoMembers ← signAs holder twoMembers
  check "fewer members: two members after the delay" ((← finished a twoMembers coin a.signersPaths).size == 1)
  let pair ← estate (recovery := some (.fewerSigners 2 10))
  check "fewer members: two-member recovery"
    (pair.account.recoveryLeaves.size == 7 && (pair.account.recoveryMembers.map (·.threshold)) == some 2)

def nestedSeparateRecovery : TM Unit := do
  let recoveryMaster ← master 0xE5
  let f ← nestedFamily (recovery := some (.separateKeys 1 #[← keyExpression recoveryMaster] 10))
  let a := f.account
  let coin ← nfunding a
  refused "nested recovery: not yet" (nspend a coin .recovery) (account := true)
  let later ← need "create" (nspend a coin .recovery 109)
  check "nested recovery: review path" ((← need "review" (a.reviewSpend later #[coin] owned 109)).path == .recovery)
  let later ← need "sign" (sign a later recoveryMaster #[coin] 109)
  check "nested recovery: approvals" ((← need "ap" (a.approvals later #[coin] .recovery)) == #[0])
  let tx ← need "finalize" (finalize a later #[coin] 109)
  check "nested recovery: sequence and witness" (tx.inputs[0]!.sequence == 10 && tx.inputs[0]!.witness.size == 3)

/-! ## HistoryLedgerTests (upstream d2ca878, #259) -/

def hlTransaction (outpoints : Array Transaction.Outpoint := #[]) (values : Array Int64) : Transaction :=
  { version := 2,
    inputs := outpoints.map fun o => { previousOutput := o, scriptSig := .empty, sequence := 0xFFFF_FFFD },
    outputs := values.zipIdx.map fun (value, position) =>
      { value, scriptPubKey := ByteArray.mk (#[0x51, 0x20] ++ Array.replicate 32 (position + 1).toUInt8) },
    locktime := 0 }

def historyExactFee : TM Unit := do
  let tx := hlTransaction (values := #[40_000, 9_000])
  check "history fee: exact" (HistoryLedger.exactFee 50_000 tx true == some 1_000)
  check "history fee: not every input ours" (HistoryLedger.exactFee 50_000 tx false).isNone
  check "history fee: nothing spent" (HistoryLedger.exactFee 0 tx true).isNone
  check "history fee: inputs below outputs" (HistoryLedger.exactFee 49_000 tx true).isNone

def historyRecord : TM Unit := do
  let tx := hlTransaction #[⟨ByteArray.mk (Array.replicate 32 1), 0⟩] #[40_000, 9_000]
  let block := ByteArray.mk (Array.replicate 32 0xbb)
  let (history, known) := HistoryLedger.record #[] tx tx.txid 500 block 40_000 0 none
  check "history record: appended, not known" (!known && history.size == 1)
  check "history record: height, block, no breakdown"
    (history[0]!.height == 500 && history[0]!.blockHash == some block && history[0]!.outputs.isNone)
  check "history record: bytes" (history[0]!.rawTransaction == some (tx.serialized false))
  check "history record: funding scripts" (history[0]!.fundingScripts == FundingSources.fundingScripts tx)
  let agreeing : HistoryEntry.Outputs :=
    { external := #[{ vout := 0, amount := 40_000, scriptPubKey := tx.outputs[0]!.scriptPubKey }], change := #[1] }
  let (pending, known) := HistoryLedger.record
    #[{ txid := tx.txid, height := 0, received := 9_000, spent := 50_000, fee := some 1_000, outputs := some agreeing }]
    tx tx.txid 501 block 0 50_000 (some 1_000)
  check "history record: a pending entry confirms in place" (known && pending.size == 1)
  check "history record: keeps an agreeing breakdown"
    (pending[0]!.height == 501 && pending[0]!.blockHash == some block && pending[0]!.outputs == some agreeing)
  check "history record: keeps its amounts"
    (pending[0]!.received == 9_000 && pending[0]!.spent == 50_000 && pending[0]!.fee == some 1_000)
  let contradicting : HistoryEntry.Outputs :=
    { external := #[{ vout := 0, amount := 1, scriptPubKey := tx.outputs[0]!.scriptPubKey }] }
  let (imported, _) := HistoryLedger.record
    #[{ txid := tx.txid, height := 0, received := 0, spent := 50_000, outputs := some contradicting }]
    tx tx.txid 501 block 0 50_000 none
  check "history record: contradicted metadata dropped" imported[0]!.outputs.isNone

def historyClassifyOutputs : TM Unit := do
  let tx := hlTransaction (values := #[40_000, 9_000, 0, 5_000])
  let outputs := HistoryLedger.classifyOutputs tx fun script =>
    if script == tx.outputs[1]!.scriptPubKey then some .change
    else if script == tx.outputs[3]!.scriptPubKey then some .receive
    else none
  check "history classify: change" (outputs.change == #[1])
  check "history classify: external, zero-value nobody's"
    (outputs.external == #[{ vout := 0, amount := 40_000, scriptPubKey := tx.outputs[0]!.scriptPubKey }])

def historyRewind : TM Unit := do
  let kept : HistoryEntry := { txid := ByteArray.mk (Array.replicate 32 1), height := 600, received := 1_000, spent := 0,
                               blockHash := some (ByteArray.mk (Array.replicate 32 6)) }
  let spender : HistoryEntry := { txid := ByteArray.mk (Array.replicate 32 2), height := 601, received := 0, spent := 1_000,
                                  blockHash := some (ByteArray.mk (Array.replicate 32 7)) }
  let receive : HistoryEntry := { txid := ByteArray.mk (Array.replicate 32 3), height := 602, received := 2_000, spent := 0 }
  let (history, repended) := HistoryLedger.rewind #[kept, spender, receive] 600
  check "history rewind: the spender re-pends" (repended == #[spender.txid])
  check "history rewind: the receive drops" (history.map (·.txid) == #[kept.txid, spender.txid])
  check "history rewind: below the fork untouched" (history[0]! == kept)
  check "history rewind: pending again"
    (history[1]!.height == 0 && history[1]!.blockHash.isNone && history[1]!.spent == 1_000)
  let (again, repended) := HistoryLedger.rewind history 600
  check "history rewind: a repeat changes nothing" (repended.isEmpty && again == history)

/-! ## Spend records on the account record (upstream d2ca878, #259) -/

def recordWithoutSpendsEncodesAsBefore : TM Unit := do
  let (account, _) ← accountWith
  let coin ← funding account 5_000
  let registration : LedgerRegistration :=
    { policyName := "Household", policyID := ByteArray.mk (Array.replicate 32 1),
      hmac := ByteArray.mk (Array.replicate 32 2), masterFingerprint := 0xF5ACC2FD,
      keyPath := #[0x8000_0057, 0x8000_0001, 0x8000_0000] }
  for (ledger, n) in [(none, "no Ledger"), (some registration, "a Ledger")] do
    let record : MultisigAccountRecord :=
      { id := account.id, name := "Household", descriptor := account.descriptor.serialized,
        createdAtHeight := 100, nextReceiveIndex := 3, nextChangeIndex := 1, allUtxos := #[coin], ledger }
    -- multisig.json as 1cf93fb wrote it: these keys and no others.
    let legacy := obj [("id", some (.str record.id)), ("name", some (.str record.name)),
      ("descriptor", some (.str record.descriptor)), ("createdAtHeight", some (SwiftJSON.ofInt 100)),
      ("nextReceiveIndex", some (SwiftJSON.ofInt 3)), ("nextChangeIndex", some (SwiftJSON.ofInt 1)),
      ("utxos", some (.arr #[coin.toJV])), ("ledger", ledger.map LedgerRegistration.toJV)]
    let old := SwiftJSON.write (.arr #[legacy])
    check s!"spend records: an old record encodes byte for byte ({n})" (SwiftJSON.write (.arr #[record.toJV]) == old)
    check s!"spend records: pretty form too ({n})" (SwiftJSON.writePretty "" record.toJV == SwiftJSON.writePretty "" legacy)
    match SwiftJSON.decodeText old (SwiftJSON.asArray MultisigAccountRecord.ofJV) with
    | .ok #[r] =>
      check s!"spend records: an old file reads with none of them ({n})" (r.history.isEmpty && r.draft.isNone && r.inFlight.isEmpty && r == record)
      check s!"spend records: and writes back the same bytes ({n})" (SwiftJSON.write (.arr #[r.toJV]) == old)
    | _ => check s!"spend records: an old file reads ({n})" false

def spendRecordsRoundTrip : TM Unit := do
  let (account, ms) ← accountWith
  let coin ← funding account 100_000
  let psbt ← need "create" (spend account coin)
  let draft ← needE "draft" (·.name) (MultisigSpendDraft.ofPSBT psbt 100 (some "carol") (some 4))
  let raw ← needE "base64" (fun _ => "base64") (match Base64.decode? draft.psbtBase64 with | some b => .ok b | none => .error ())
  -- Fixed upstream bug: the draft, which the app shares, is BIP174 v0 (PSBT_GLOBAL_UNSIGNED_TX first), not v2.
  check "draft: BIP174 v0 text" (raw.size > 7 && raw.extract 0 5 == ByteArray.mk #[0x70, 0x73, 0x62, 0x74, 0xFF]
    && raw[5]! == 0x01 && raw[6]! == 0x00)
  check "draft: not the v2 text" (draft.psbtBase64 != psbt.base64)
  let tx ← needE "unsigned" (·.name) psbt.unsignedTransaction
  check "draft: txid" (draft.txid.toOption == some tx.txid)
  check "draft: inputs" (draft.inputs.toOption == some #[coin.outpoint])
  check "draft: reads back as the same spend"
    (match draft.psbt with | .ok p => (p.unsignedTransaction.toOption.map (·.txid)) == some tx.txid | .error _ => false)
  let signed ← need "sign" (sign account psbt ms[0]! #[coin])
  let signedDraft ← needE "draft" (·.name) (MultisigSpendDraft.ofPSBT signed 100)
  check "draft: a signed copy keeps its signature in v0"
    (match signedDraft.psbt with
     | .ok p => (account.approvals p #[coin]).toOption == some #[0]
     | .error _ => false)
  let plain : MultisigSpendDraft := { psbtBase64 := "cHNidP8=", createdAtHeight := 7 }
  check "draft: optionals omitted" (SwiftJSON.write plain.toJV == "{\"createdAtHeight\":7,\"psbtBase64\":\"cHNidP8=\"}")
    (SwiftJSON.write plain.toJV)
  let huge : MultisigSpendDraft := { plain with psbtBase64 := String.ofList (List.replicate (MultisigSpendDraft.maximumBytes + 1) 'A') }
  check "draft: too large" (match huge.psbt with | .error (.inl (.invalidBundle _)) => true | _ => false)
  let sent := makeFakeSegwitTx
  let inFlight := InFlightSpend.ofTransaction sent 120
  check "in flight: bytes with the witness" (inFlight.rawTransaction == sent.serialized true && inFlight.txid == sent.txid)
  check "in flight: display-hex txid"
    (match inFlight.toJV with | .obj kvs => SwiftJSON.lookup kvs "txid" == some (.str (displayHex sent.txid)) | _ => false)
  let entry : HistoryEntry := { txid := sent.txid, height := 0, received := 0, spent := 50_000 }
  let record : MultisigAccountRecord :=
    { id := account.id, name := "Household", descriptor := account.descriptor.serialized, createdAtHeight := 100,
      allUtxos := #[coin], history := #[entry], draft := some draft, inFlight := #[inFlight] }
  let text := SwiftJSON.write record.toJV
  check "spend records: keys" (hasText text "\"history\":" && hasText text "\"draft\":" && hasText text "\"inFlight\":")
  check "spend records: round trip" ((SwiftJSON.decodeText text MultisigAccountRecord.ofJV).toOption == some record)
  let mismatched := { inFlight with txid := ByteArray.mk (Array.replicate 32 9) }
  let decodeOne (s : InFlightSpend) := SwiftJSON.decodeText (SwiftJSON.write s.toJV) InFlightSpend.ofJV
  check "in flight: refused unless the bytes are the transaction named"
    (match decodeOne mismatched with | .error e => e == "invalidBundle" | .ok _ => false)
  check "in flight: a short txid is refused"
    (match SwiftJSON.decodeText "{\"txid\":\"abcd\",\"rawTransaction\":\"\",\"broadcastHeight\":1}" InFlightSpend.ofJV with
     | .error e => e == "dataCorrupted" | .ok _ => false)
  check "in flight: too large"
    (match ({ inFlight with rawTransaction := ByteArray.mk (Array.replicate (InFlightSpend.maximumBytes + 1) 0) }).transaction with
     | .error (.inl (.invalidBundle _)) => true | _ => false)
  check "spend records: a record with a bad in-flight spend is refused"
    (match SwiftJSON.decodeText (SwiftJSON.write { record with inFlight := #[mismatched] }.toJV) MultisigAccountRecord.ofJV with
     | .error e => e == "invalidBundle" | .ok _ => false)

/-! ## ImportBundleTests.signers (upstream d2ca878) and the new bundle bounds -/

def bundleSigners : TM Unit := do
  let base : ImportBundle :=
    { network := "signet", lastKnownHeight := 500,
      transactions := #[{ txid := displayHex (ByteArray.mk (Array.replicate 32 0x50)), height := 490, received := 100_000, spent := 0 }] }
  let key ← keyExpression (← master 0xE5)
  let carol : SignerRecord :=
    { id := "carol", kind := .keys, name := "Carol", keys := #[key], addedAt := 1_700_000_000 - SignerRecord.unixEpochOffset }
  let bundle := { base with signers := some #[carol] }
  let text := bundle.serialized
  check "signers: carried" (hasText text "\"signers\"")
  check "signers: addedAt as Date's seconds since 2001" (hasText text "721692800") text
  check "signers: kind as its raw value, no fingerprint" (hasText text "\"keys\"" && !hasText text "masterFingerprint")
  check "signers: decoded" (match ImportBundle.decode text with | .ok b => b.signers == some #[carol] | .error _ => false)
  check "signers: absent from an older file"
    (match ImportBundle.decode base.serialized with | .ok b => b.signers.isNone | .error _ => false)
  let ledger : SignerRecord := { carol with id := "ledger", kind := .ledger, masterFingerprint := some 0xF5ACC2FD }
  check "signers: a Ledger's record round-trips"
    (match ImportBundle.decode { base with signers := some #[ledger] }.serialized with
     | .ok b => b.signers == some #[ledger] | .error _ => false)
  let brokenKeys : List (Array String) :=
    [#[], Array.replicate (SignerRecord.maximumKeysPerSigner + 1) key, #["tpubnonsense"], #[s!"sortedmulti_a(1,{key})"]]
  for (keys, n) in brokenKeys.zipIdx do
    let broken := { base with signers := some #[{ id := "x", kind := .keys, name := "X", keys, addedAt := 0 }] }
    check s!"signers: refused {n}" (match ImportBundle.decode broken.serialized with | .error (.wallet _) => true | _ => false)
  let crowd := { base with signers := some ((Array.range (SignerRecord.maximumSigners + 1)).map fun i =>
    { id := s!"s{i}", kind := .keys, name := s!"S{i}", keys := #[key], addedAt := 0 }) }
  check "signers: a list over the ceiling" (match ImportBundle.decode crowd.serialized with | .error (.wallet _) => true | _ => false)
  check "signers: an unknown network"
    (match ImportBundle.decode { bundle with network := "testnet4" }.serialized with
     | .error (.wallet (.invalidBundle r)) => r == "signers for an unknown network testnet4" | _ => false)
  check "signers: another network's keys" (match ImportBundle.decode { bundle with network := "mainnet" }.serialized with
     | .error (.wallet (.invalidBundle r)) => r == "a signer key does not parse for mainnet" | _ => false)
  check "signers: an empty list is fine anywhere"
    (match ImportBundle.decode { base with network := "testnet4", signers := some #[] }.serialized with | .ok _ => true | _ => false)
  check "signerKey: trims, and refuses a policy or whitespace inside"
    ((MultisigAccount.signerKey s!"  {key}\n" .signet).toBool && !(MultisigAccount.signerKey s!"{key} x" .signet).toBool)
  -- The account bounds: history entries, and a draft's size.
  let (account, _) ← accountWith
  let record : MultisigAccountRecord :=
    { id := account.id, name := "Household", descriptor := account.descriptor.serialized, createdAtHeight := 90 }
  let bigDraft : MultisigSpendDraft := { psbtBase64 := String.ofList (List.replicate (MultisigSpendDraft.maximumBytes + 1) 'A'), createdAtHeight := 1 }
  check "bundle: a draft too large"
    (match ImportBundle.decode { base with vaults := some #[{ record with draft := some bigDraft }] }.serialized with
     | .error (.wallet (.invalidBundle r)) => r == "too many multisig account transactions, or a draft too large" | _ => false)
  let entry : HistoryEntry := { txid := ByteArray.mk (Array.replicate 32 0x44), height := 3, received := 1, spent := 0 }
  let many := Array.replicate (ImportBundle.maximumEntries / 2 + 1) entry
  -- Compact JSON, so that 50,001 entries stay under the 8 MiB byte ceiling, which is checked first.
  let crowded := { base with vaults := some #[{ record with history := many }, { record with history := many }] }
  check "bundle: too many account transactions"
    (match ImportBundle.decode (SwiftJSON.write crowded.toJV) with
     | .error (.wallet (.invalidBundle r)) => r == "too many multisig account transactions, or a draft too large" | _ => false)
  check "bundle: within the bounds"
    (match ImportBundle.decode { base with vaults := some #[{ record with history := #[entry] }] }.serialized with
     | .ok b => (b.vaults.map (·.map (·.history.size))) == some #[1] | _ => false)

/-! ## WalletCursorTests (upstream d2ca878: wallet cursor reservations) -/

def testWallet (storagePath : Option System.FilePath := none) (keyStore : Option (KeyStore IO) := none) : TM Wallet := do
  let ks ← match keyStore with | some k => pure k | none => newKeyStore
  wmT "create" (Wallet.create .signet ks storagePath (some (ByteArray.mk (Array.replicate 16 0))) 100 0 pinned)

def failed {α} (x : WM α) : IO (Option String) := do
  match ← x.run with | .ok _ => return none | .error e => return some e.name

/-- Replaces the wallet file by a directory, so that every write of it fails. -/
def blockWrites (file : System.FilePath) : IO Unit := do
  IO.FS.removeFile file
  IO.FS.createDir file

def durableReservations : TM Unit := do
  let file ← tempPath "wallet.json"
  let store ← newKeyStore
  let w ← testWallet (some file) (some store)
  wmT "scan height" (w.recordScanHeight 500)
  wmT "advance" (w.advanceCursors (some 12) (some 8))
  let scripts ← wmT "watch" w.watchScripts
  for (chain, cursor) in [(AddressChain.receive, (12 : UInt32)), (.change, 8)] do
    let mut all := true
    for i in [0:(cursor + Wallet.gapLimit).toNat] do
      all := all && scripts.contains (← wmT "spk" (w.scriptPubKey chain i.toUInt32))
    check s!"cursors: every reserved {repr chain} address and its lookahead is watched" all
  let reopened ← wmT "open" (Wallet.open file store)
  check "cursors: reopened keeps both cursors and the scan height"
    ((← reopened.nextReceiveIndex) == 12 && (← reopened.nextChangeIndex) == 8 && (← reopened.nextScanHeight) == 500)
  check "cursors: the next fresh address is past the reservation"
    ((← wmT "fresh" reopened.freshReceiveAddress) == (← wmT "address" (w.address .receive 12)))
  let bundle ← wmT "export" reopened.exportBundle
  let restored ← wmT "import" (Wallet.importing bundle (← newKeyStore))
  check "cursors: a restored backup reissues no reserved address"
    ((← restored.nextReceiveIndex) == 13 && (← restored.nextChangeIndex) == 8 && (← restored.nextScanHeight) == 500)

def monotonicNoOp : TM Unit := do
  let file ← tempPath "wallet.json"
  let w ← testWallet (some file)
  wmT "advance" (w.advanceCursors (some 4) (some 9))
  blockWrites file
  -- a no-op works even when writing would fail
  check "cursors: omitted cursors write nothing" (← failed (w.advanceCursors)).isNone
  check "cursors: equal and lower cursors write nothing" (← failed (w.advanceCursors (some 4) (some 2))).isNone
  check "cursors: neither chain rewinds" ((← w.nextReceiveIndex) == 4 && (← w.nextChangeIndex) == 9)

def atomicFailure : TM Unit := do
  let file ← tempPath "wallet.json"
  let store ← newKeyStore
  let w ← testWallet (some file) (some store)
  let previous ← IO.FS.readBinFile file
  blockWrites file
  check "cursors: a failed write throws" (← failed (w.advanceCursors (some 12) (some 8))).isSome
  check "cursors: a failed write moves neither cursor" ((← w.nextReceiveIndex) == 0 && (← w.nextChangeIndex) == 0)
  IO.FS.removeDir file
  IO.FS.writeBinFile file previous
  let reopened ← wmT "open" (Wallet.open file store)
  check "cursors: the file kept the old cursors" ((← reopened.nextReceiveIndex) == 0 && (← reopened.nextChangeIndex) == 0)
  wmT "retry" (w.advanceCursors (some 12) (some 8))
  let retried ← wmT "open" (Wallet.open file store)
  check "cursors: the reservation can be retried" ((← retried.nextReceiveIndex) == 12 && (← retried.nextChangeIndex) == 8)

def invalidCursor : TM Unit := do
  for cursor in [HDKey.hardenedOffset - Wallet.gapLimit + 1, HDKey.hardenedOffset, (0xFFFF_FFFF : UInt32)] do
    let w ← testWallet
    let r1 ← failed (w.advanceCursors (some 3) (some cursor))
    check s!"cursors: change cursor {cursor} is invalidPath" (r1 == some "invalidPath") s!"{r1}"
    check s!"cursors: change cursor {cursor} changes nothing" ((← w.nextReceiveIndex) == 0 && (← w.nextChangeIndex) == 0)
    let r2 ← failed (w.advanceCursors (some cursor) (some 3))
    check s!"cursors: receive cursor {cursor} is invalidPath" (r2 == some "invalidPath") s!"{r2}"
    check s!"cursors: receive cursor {cursor} changes nothing" ((← w.nextReceiveIndex) == 0 && (← w.nextChangeIndex) == 0)

def concurrentReservations : TM Unit := do
  let w ← testWallet
  let tasks ← (List.range 20).mapM fun i =>
    let index : UInt32 := (i + 1).toUInt32
    IO.asTask (prio := .dedicated) (failed (w.advanceCursors (some index) (some (21 - index))))
  let results ← (tasks.mapM fun t => IO.ofExcept t.get : IO (List (Option String)))
  check "cursors: every concurrent reservation succeeds" (results.all (·.isNone))
  check "cursors: concurrent reservations keep each chain's highest cursor"
    ((← w.nextReceiveIndex) == 20 && (← w.nextChangeIndex) == 20)

def cursorPastTheWindowIsDamage : TM Unit := do
  let file ← tempPath "wallet.json"
  let store ← newKeyStore
  let w ← testWallet (some file) (some store)
  wmT "advance" (w.advanceCursors (some 3))
  let json : Lean.Json ← match Lean.Json.parse (← IO.FS.readFile file) with
    | .ok j => pure j | .error e => throw s!"wallet.json: {e}"
  IO.FS.writeFile file (json.setObjVal! "nextReceiveIndex" (0xFFFF_FFFF : Nat)).compress
  check "cursors: a state file past the gap-limit window does not open" (← failed (Wallet.open file store)).isSome
  let edge := HDKey.hardenedOffset - Wallet.gapLimit
  IO.FS.writeFile file (json.setObjVal! "nextReceiveIndex" edge.toNat).compress
  let reopened ← wmT "open" (Wallet.open file store)
  check "cursors: the window's last cursor opens" ((← reopened.nextReceiveIndex) == edge)

def main : IO UInt32 := do
  runTest "feeResolution" feeResolution
  runTest "twoOfThree" twoOfThree
  runTest "everyPairCanSpend" everyPairCanSpend
  runTest "threeOfThree" threeOfThree
  runTest "accountKeySigning" accountKeySigning
  runTest "forgedApprovalNotCounted" forgedApprovalNotCounted
  runTest "signerOrderDoesNotMatter" signerOrderDoesNotMatter
  runTest "changeByScriptOnly" changeByScriptOnly
  runTest "reviewRefusals" reviewRefusals
  runTest "realInternalKeyRefused" realInternalKeyRefused
  runTest "unspendableXpubInternalKey" unspendableXpubInternalKey
  runTest "unspendableXpubLookAlikesRefused" unspendableXpubLookAlikesRefused
  runTest "repeatedSignerRefused" repeatedSignerRefused
  runTest "suffixPinned" suffixPinned
  runTest "signerKeyShape" signerKeyShape
  runTest "shapeRefusals" shapeRefusals
  runTest "recordCoding" recordCoding
  runTest "bundleAccounts" bundleAccounts
  runTest "coreVectors" coreVectors
  runTest "leafPolicies" leafPolicies
  runTest "recoveryKeyOrderDoesNotMatter" recoveryKeyOrderDoesNotMatter
  runTest "fewerSigners" fewerSigners
  runTest "separateKey" separateKey
  runTest "surplusRecoverySignatureLeftOut" surplusRecoverySignatureLeftOut
  runTest "bip326OldCoins" bip326OldCoins
  runTest "timelockedReviewRefusals" timelockedReviewRefusals
  runTest "topOfHeightRange" topOfHeightRange
  runTest "admissionRefusals" admissionRefusals
  runTest "scriptPathVectors" scriptPathVectors
  runTest "sendRecordsItsOutputs" sendRecordsItsOutputs
  runTest "silentPaymentSend" silentPaymentSend
  runTest "silentPaymentSameCodeTwice" silentPaymentSameCodeTwice
  runTest "silentPaymentMixed" silentPaymentMixed
  runTest "silentPaymentValidation" silentPaymentValidation
  runTest "sendToOwnAddressIsNotExternal" sendToOwnAddressIsNotExternal
  runTest "feeBumpRecordsItsOutputs" feeBumpRecordsItsOutputs
  runTest "recordedOutputsRoundTrip" recordedOutputsRoundTrip
  runTest "backupCompatibility" backupCompatibility
  runTest "invalidMetadata" invalidMetadata
  runTest "contradictedImportedMetadataIsDropped" contradictedImportedMetadataIsDropped
  runTest "accountSecrets" accountSecrets
  runTest "accountKeyWallet" accountKeyWallet
  runTest "nestedBuilder" nestedBuilder
  runTest "nestedOrderDoesNotMatter" nestedOrderDoesNotMatter
  runTest "thresholdMember" thresholdMember
  runTest "thresholdOrderDoesNotMatter" thresholdOrderDoesNotMatter
  runTest "nestedBuilderRefusals" nestedBuilderRefusals
  runTest "nestedAdmissionRefusals" nestedAdmissionRefusals
  runTest "nestedSpends" nestedSpends
  runTest "thresholdMemberSpends" thresholdMemberSpends
  runTest "fewerMembersRecovery" fewerMembersRecovery
  runTest "nestedSeparateRecovery" nestedSeparateRecovery
  runTest "historyExactFee" historyExactFee
  runTest "historyRecord" historyRecord
  runTest "historyClassifyOutputs" historyClassifyOutputs
  runTest "historyRewind" historyRewind
  runTest "recordWithoutSpendsEncodesAsBefore" recordWithoutSpendsEncodesAsBefore
  runTest "spendRecordsRoundTrip" spendRecordsRoundTrip
  runTest "bundleSigners" bundleSigners
  runTest "durableReservations" durableReservations
  runTest "monotonicNoOp" monotonicNoOp
  runTest "atomicFailure" atomicFailure
  runTest "invalidCursor" invalidCursor
  runTest "concurrentReservations" concurrentReservations
  runTest "cursorPastTheWindowIsDamage" cursorPastTheWindowIsDamage
  let f ← failures.get
  IO.println s!"multisig-test: {← passed.get} passed, {f.size} failed"
  return if f.isEmpty then 0 else 1
