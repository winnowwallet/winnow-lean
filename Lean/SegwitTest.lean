import Winnow
import Lean.Data.Json
import TestKit.Check
import TestKit.Fixtures
import Secp.Curve.Spec

/-! # SegWit v0 multisig accounts: `wsh(sortedmulti(k, KEY, …))` and the ECDSA under them

What Bitcoin Core makes of all this is `segwit-regtest`; here it is the published vectors, an independent
implementation's signatures, and the refusals.

* `Vectors/openssl-ecdsa-secp256k1.json`: 64 signatures OpenSSL made (`scripts/ecdsa-vectors`). The DER
  reader takes each and writes it back byte for byte; the verifier accepts each whose `s` is in the lower
  half, refuses each whose `s` is in the upper half and accepts it with `s` replaced by N − s; a changed
  digest, a changed `r` and another key are refused. (One vector signs the digest of all zeros, where ECDSA
  itself cannot tell a key from its negation; no transaction's digest is that.)
* `Vectors/segwit-v0-vectors.json`: BIP143's own multisig example (the digest for SIGHASH_ALL, and the
  signature the BIP prints, which must verify under the key it names; the BIP's private key signs it again
  here, in constant time, and that verifies too), and BIP67's four vectors of keys and the script they sort
  into. BIP173's example of a P2WSH address.
* The descriptor: what is read, written back and refused.
* Addresses, the review's refusals, and a spend signed by two members and finalized: the fixed key (as a key
  service would sign: a signature made elsewhere and written into the PSBT) and an extended key (as this
  wallet signs).

Run from `Lean/`. Exits 1 on any failure. -/

open Winnow Winnow.Keys Lean TestKit
open Tx (BitcoinNetwork)
open MultisigAccount (OutputCoordinate)

def field (j : Json) (k : String) : String := (j.getObjValAs? String k).toOption.getD ""
def bytesOf (j : Json) (k : String) : ByteArray := ofHex! (field j k)
def listOf (j : Json) (k : String) : Array Json := (j.getObjValAs? (Array Json) k).toOption.getD #[]

def readJson (path : String) : IO Json := do IO.ofExcept (Json.parse (← IO.FS.readFile path))

def accepts (verified : Bool) : Bool := verified
def rejects (verified : Bool) : Bool := !verified

/-- Whether a failure is the account's own, with `reason` somewhere in its text. -/
def says (reason : String) : MultisigFailure → Bool
  | .account (.invalidDescriptor r) | .account (.invalidSpend r) => (r.splitOn reason).length > 1
  | _ => false

/-! ## ECDSA against OpenSSL -/

def opensslSignatures : TM Unit := do
  let file ← readJson "Vectors/openssl-ecdsa-secp256k1.json"
  let vectors := listOf file "vectors"
  check "64 OpenSSL signatures" (vectors.size == 64) s!"{vectors.size}"
  let n := Secp.Spec.N
  let mut high := 0
  for h : i in [0:vectors.size] do
    let v := vectors[i]
    let (key, digest, der) := (bytesOf v "publicKey", bytesOf v "digest", bytesOf v "der")
    let some signature := Secp.Ecdsa.parseDer der | check s!"OpenSSL {i}: its DER is read" false; continue
    check s!"OpenSSL {i}: DER written back is OpenSSL's" (Secp.Ecdsa.der signature == der)
    let s := Secp.fromBE (signature.extract 32 64)
    let lower := signature.extract 0 32 ++ Secp.toBE32 (if s > n / 2 then n - s else s)
    if s > n / 2 then
      high := high + 1
      check s!"OpenSSL {i}: s in the upper half is refused" (rejects (SecpCt.Ecdsa.verify signature digest key))
    check s!"OpenSSL {i}: verifies with s in the lower half" (accepts (SecpCt.Ecdsa.verify lower digest key))
    check s!"OpenSSL {i}: not of another digest"
      (rejects (SecpCt.Ecdsa.verify lower (digest.set! 0 (digest[0]! ^^^ 0x80)) key))
    check s!"OpenSSL {i}: not with r changed" (rejects (SecpCt.Ecdsa.verify (lower.set! 31 (lower[31]! ^^^ 1)) digest key))
    -- The same key with the other y is another key, unless the digest is zero: ECDSA's equation then has
    -- only (r/s)·Q in it, whose x is the same for Q and for −Q. The first vector is that digest, on purpose.
    let negated := SecpCt.Ecdsa.verify lower digest (key.set! 0 (key[0]! ^^^ 1))
    check s!"OpenSSL {i}: not under the key's negation, but for the zero digest"
      (if digest.toList.all (· == 0) then accepts negated else rejects negated)
    -- every proper prefix, and the whole with a byte after it, is not a signature in DER
    check s!"OpenSSL {i}: DER cut short or run on is refused"
      ((List.range der.size).all (fun cut => (Secp.Ecdsa.parseDer (der.extract 0 cut)).isNone) &&
        (Secp.Ecdsa.parseDer (der.push 0)).isNone)
  check "the vectors have signatures in both halves" (high > 8 && high < 56) s!"{high} of 64 in the upper half"

/-! ## The published vectors -/

def publishedVectors : TM Unit := do
  let file ← readJson "Vectors/segwit-v0-vectors.json"
  let b := (file.getObjVal? "bip143").toOption.getD Json.null
  let tx ← needE "BIP143's transaction" (·.name) (Transaction.decode (bytesOf b "unsignedTransaction"))
  let script := bytesOf b "witnessScript"
  let digest := SighashBIP143.sighashAll tx 0 script 987654321
  check "BIP143: what a multisig signature commits to" (digest == some (bytesOf b "sighashAll"))
    (digest.map hex |>.getD "none")
  check "BIP143: no digest for an input the transaction does not have" ((SighashBIP143.sighashAll tx 1 script 987654321).isNone)
  check "BIP143: another amount is another digest"
    (SighashBIP143.sighashAll tx 0 script 987654320 != some (bytesOf b "sighashAll"))
  let theirs := SegwitMultisigAccount.countedSignature? (bytesOf b "signature")
  check "BIP143: the signature it prints is DER and SIGHASH_ALL" theirs.isSome
  check "BIP143: the signature it prints verifies under the key it names"
    (accepts (SecpCt.Ecdsa.verify (theirs.getD .empty) (bytesOf b "sighashAll") (bytesOf b "publicKey")))
  -- the BIP's private key, signing here: the public key is the BIP's, and the signature verifies
  check "BIP143: its private key is its public key" ((publicKeyOf (bytesOf b "privateKey")).toOption == some (bytesOf b "publicKey"))
  let ours ← need "BIP143: signing with its key"
    (SegwitMultisigAccount.partialSignature (bytesOf b "privateKey") (bytesOf b "publicKey") (bytesOf b "sighashAll") aux0)
  check "BIP143: a signature made here with its key is counted and verifies"
    (match SegwitMultisigAccount.countedSignature? ours with
      | some signature => accepts (SecpCt.Ecdsa.verify signature (bytesOf b "sighashAll") (bytesOf b "publicKey"))
      | none => false)
  let vectors := listOf file "bip67"
  check "BIP67 has four vectors" (vectors.size == 4)
  for h : i in [0:vectors.size] do
    let keys := (listOf vectors[i] "keys").map fun k => ofHex! (k.getStr?.toOption.getD "")
    check s!"BIP67 vector {i + 1}: the script of the keys sorted"
      (SegwitMultisigAccount.witnessScript 2 keys == bytesOf vectors[i] "script")
    check s!"BIP67 vector {i + 1}: whatever order they are given in"
      (SegwitMultisigAccount.witnessScript 2 keys.reverse == bytesOf vectors[i] "script")
  -- BIP173's example: the P2WSH address of `<key> OP_CHECKSIG`, on mainnet
  let theirScript := ofHex! "210279be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798ac"
  check "BIP173: the address of a witness script"
    ((SegwitAddress.encode "bc" 0 (sha256 theirScript)).toOption == some "bc1qrp33g0q5c5txsp9arysrx4k6zdkfs4nce4xj0gdcccefvpysxf3qccfmv3")
  check "BIP173: and what locks a coin to it"
    ((AddressDecoder.segwitScriptPubKey "bc1qrp33g0q5c5txsp9arysrx4k6zdkfs4nce4xj0gdcccefvpysxf3qccfmv3" .mainnet).toOption
      == some (SegwitMultisigAccount.scriptPubKeyOf theirScript))

/-! ## The account the rest of the tests use -/

/-- The fixed key's private half: a test key, written here on purpose. In the wallet this is for, that half
is in a key service and never anywhere else. -/
def fixedSecret : ByteArray := sha256 "winnow segwit-test fixed key".toUTF8

structure World where
  account : SegwitMultisigAccount
  descriptor : String
  fixedPublic : ByteArray
  /-- The two extended-key members' masters: this wallet's, and another member's. -/
  ours : HDKey
  other : HDKey
  /-- A transaction that pays the account: 100,000 sats to receive address 0 at output 1, 50,000 to receive
  address 3 at output 2. -/
  funding : Transaction
  coins : Array WalletUTXO

def descriptorOf (threshold : Nat) (keys : Array String) : String :=
  s!"wsh(sortedmulti({threshold},{",".intercalate keys.toList}))"

def world : TM World := do
  let ours ← master 0xA1
  let other ← master 0xB2
  let fixedPublic ← needE "the fixed key" (·.name) (publicKeyOf fixedSecret)
  let descriptor := descriptorOf 2 #[hex fixedPublic, ← keyExpression ours, ← keyExpression other]
  let account ← need "the account" (SegwitMultisigAccount.parse descriptor .regtest)
  let script0 ← need "receive 0" (account.scriptPubKey 0 0)
  let script3 ← need "receive 3" (account.scriptPubKey 3 0)
  let paid : Array Transaction.Output := #[{ value := 7_000, scriptPubKey := destination },
    { value := 100_000, scriptPubKey := script0 }, { value := 50_000, scriptPubKey := script3 }]
  let spent : Transaction.Input :=
    { previousOutput := ⟨ByteArray.mk (Array.replicate 32 0x11), 0⟩, scriptSig := .empty, sequence := 0xFFFF_FFFD }
  let funding : Transaction := { version := 2, locktime := 0, inputs := #[spent], outputs := paid }
  let coin (vout : UInt32) (amount : Int64) (script : ByteArray) (index : UInt32) : WalletUTXO :=
    { txid := funding.txid, vout, amount, scriptPubKey := script, chain := .receive, index, height := 100 }
  return { account, descriptor, fixedPublic, ours, other, funding,
           coins := #[coin 1 100_000 script0 0, coin 2 50_000 script3 3] }

/-- A PSBT field: its type, what follows the type in its key, and its value. -/
abbrev Field := UInt8 × ByteArray × ByteArray

def pairs (fields : List Field) : Array PSBT.KeyValue :=
  PSBT.sortPairs (fields.map fun (type, keyData, value) => PSBT.KeyValue.make type keyData value).toArray

def statedCoin (amount : Int64) (script : ByteArray) : Field :=
  (PSBT.InType.witnessUTXO, .empty, Wire.appendVarData (i64LE amount) script)

/-- A PSBT (version 2) spending `coins`, each as BIP174 describes a SegWit v0 coin (its amount and script, and
the whole transaction it came from) unless `describe` says otherwise, to `outputs`. -/
def spend (w : World) (coins : Array WalletUTXO) (outputs : Array Transaction.Output)
    (describe : WalletUTXO → List Field := fun coin =>
      [statedCoin coin.amount coin.scriptPubKey, (PSBT.InType.nonWitnessUTXO, .empty, w.funding.serialized false)])
    (version : Int32 := 2) : PSBT :=
  let globals := pairs [(PSBT.GlobalType.version, .empty, u32LE 2), (PSBT.GlobalType.txVersion, .empty, i32LE version),
    (PSBT.GlobalType.fallbackLocktime, .empty, u32LE 0),
    (PSBT.GlobalType.inputCount, .empty, compactSize coins.size.toUInt64),
    (PSBT.GlobalType.outputCount, .empty, compactSize outputs.size.toUInt64)]
  { globals,
    inputs := coins.map fun coin => ⟨pairs ([(PSBT.InType.previousTxid, .empty, coin.txid),
      (PSBT.InType.outputIndex, .empty, u32LE coin.vout), (PSBT.InType.sequence, .empty, u32LE 0xFFFF_FFFD)] ++ describe coin)⟩,
    outputs := outputs.map fun o => ⟨pairs [(PSBT.OutType.amount, .empty, i64LE o.value), (PSBT.OutType.script, .empty, o.scriptPubKey)]⟩ }

def changeCoordinate : OutputCoordinate := { choice := 1, index := 0 }

/-- The ordinary spend: both coins, 60,000 out, 89,000 back to change address 0, 1,000 to the miner. -/
def ordinary (w : World) : TM PSBT := do
  let change ← need "change 0" (w.account.scriptPubKey 0 1)
  return spend w w.coins #[{ value := 60_000, scriptPubKey := destination }, { value := 89_000, scriptPubKey := change }]

/-! ## The descriptor -/

def descriptors : TM Unit := do
  let w ← world
  let (fixed, a, b) := (hex w.fixedPublic, ← keyExpression w.ours, ← keyExpression w.other)
  let read (text : String) := SegwitMultisigAccount.parse text .regtest
  check "the account: two of three" (w.account.threshold == 2 && w.account.keys.size == 3 && w.account.policySummary == "2 of 3")
  let canonical := w.account.serialized
  check "written back with its checksum, and read again as the same account"
    (canonical.startsWith (w.descriptor ++ "#") && (read canonical).toOption.map (·.serialized) == some canonical) canonical
  check "its identifier is the checksum" (canonical.endsWith ("#" ++ w.account.id) && w.account.id.length == 8)
  check "a descriptor of this kind is told from a Taproot one by how it opens"
    (SegwitMultisigAccount.isDescriptor w.descriptor && !SegwitMultisigAccount.isDescriptor "tr(abc)")
  refused "a wrong checksum" (read (w.descriptor ++ "#qqqqqqqq")) "invalidChecksum"
  refused "a checksum cut short" (read (w.descriptor ++ "#" ++ String.ofList (w.account.id.toList.take 7))) "invalidChecksum"
  refused "something after its end" (read (w.descriptor ++ ")")) "unexpectedCharacter"
  refused "a Taproot descriptor" (read s!"tr({a})") "unknownExpression"
  refused "multi in place of sortedmulti" (read s!"wsh(multi(2,{fixed},{a},{b}))") "unknownExpression"
  refused "wpkh" (read s!"wpkh({fixed})") "unknownExpression"
  refused "one key" (read (descriptorOf 1 #[a])) "invalidDescriptor" (says "at least two signers")
  refused "a threshold of none" (read (descriptorOf 0 #[fixed, a])) "invalidThreshold"
  refused "a threshold past the keys" (read (descriptorOf 3 #[fixed, a])) "invalidThreshold"
  refused "the fixed key twice" (read (descriptorOf 2 #[fixed, fixed, a])) "invalidDescriptor" (says "more than once")
  refused "an extended key twice" (read (descriptorOf 2 #[fixed, a, a])) "invalidDescriptor" (says "more than once")
  refused "fixed keys alone" (read (descriptorOf 2 #[fixed, hex (← needE "key" (·.name) (publicKeyOf (sha256 fixedSecret)))]))
    "invalidDescriptor" (says "at least one signer must be an extended public key")
  -- seventeen keys: the fixed one and sixteen made from it
  let many ← (Array.range 16).mapM fun i =>
    needE "key" (·.name) (publicKeyOf (sha256 (fixedSecret.push i.toUInt8)))
  refused "seventeen keys" (read (descriptorOf 2 (#[a] ++ many.map hex))) "invalidDescriptor" (says "at most 16")
  check "sixteen keys" (read (descriptorOf 2 (#[a] ++ (many.extract 0 15).map hex))).isOk
  let wif := Base58Check.encode ((ByteArray.mk #[0xEF] ++ fixedSecret).push 0x01)
  refused "a private key in place of the fixed key" (read (descriptorOf 2 #[wif, a, b])) "invalidDescriptor" (says "private key")
  let account ← accountKey w.ours
  refused "an extended private key"
    (read (descriptorOf 2 #[fixed, s!"[{Descriptor.hex8 w.ours.fingerprint}/86'/1'/0']{account.serialized .testnet}/<0;1>/*", b]))
    "invalidDescriptor" (says "private key")
  refused "an extended key that does not say where it comes from"
    (read (descriptorOf 2 #[fixed, account.neutered.serialized .testnet ++ "/<0;1>/*", b])) "invalidDescriptor" (says "carrying its origin")
  refused "an extended key that derives nothing" (read (descriptorOf 2 #[fixed, ← bareKeyExpression w.ours, b]))
    "invalidDescriptor" (says "/<0;1>/*")
  refused "an extended key on another pair" (read (descriptorOf 2 #[fixed, (← bareKeyExpression w.ours) ++ "/<2;3>/*", b]))
    "invalidDescriptor" (says "/<0;1>/*")
  refused "an extended key of another network" (SegwitMultisigAccount.parse w.descriptor .mainnet) "invalidDescriptor"
    (says "different network")
  refused "a fixed key that is not compressed"
    (read (descriptorOf 2 #[hex (← needE "key" (·.name) (publicKeyOf fixedSecret (compressed := false))), a, b]))
    "invalidDescriptor" (says "compressed")
  -- x = 5 is no point's: 5³ + 7 = 132 is not a square modulo P
  refused "a fixed key that is not a point of the curve"
    (read (descriptorOf 2 #["02" ++ hex (Secp.toBE32 5), a, b])) "invalidDescriptor" (says "not a point")
  refused "a fixed key with a path after it" (read (descriptorOf 2 #[fixed ++ "/0", a, b])) "invalidPath"
  -- read as whichever kind the text is
  let either := (AnyMultisigAccount.parse canonical .regtest).toOption
  check "a record's descriptor reads as this kind by how it opens, with the same identifier and text"
    ((either.map fun any => any.isSegwit && any.taproot?.isNone && any.id == w.account.id && any.serialized == canonical &&
      any.policySummary == "2 of 3" && any.threshold == 2 && any.signers.size == 3 && !any.isNested && any.recovery.isNone)
      == some true)
  check "and a Taproot one as the other kind"
    (((AnyMultisigAccount.parse s!"tr({Taproot.unspendableInternalKey |> hex},sortedmulti_a(2,{a},{b}))" .regtest).toOption.map
      fun any => !any.isSegwit && any.taproot?.isSome) == some true)
  check "this wallet's key is one of the account's, another's is not"
    (w.account.includes account && !w.account.includes (← accountKey (← master 0xC3)))
  check "the master holds a signer, and so does its account key; a stranger's does not"
    (w.account.hasSigner w.ours && w.account.hasSigner account && !w.account.hasSigner (← master 0xC3))

/-! ## Addresses -/

def addresses : TM Unit := do
  let w ← world
  let at0 ← need "receive 0" (w.account.resolved 0 0)
  let change0 ← need "change 0" (w.account.resolved 1 0)
  check "a P2WSH output: version 0 and a 32-byte hash" (at0.output.scriptPubKey.size == 34 &&
    at0.output.scriptPubKey.extract 0 2 == ByteArray.mk #[0x00, 0x20] &&
    at0.output.scriptPubKey.extract 2 34 == sha256 at0.witnessScript)
  check "a regtest bech32 address" (at0.output.address.startsWith "bcrt1q" && at0.output.address.length == 64) at0.output.address
  check "the address decodes to the script"
    ((AddressDecoder.segwitScriptPubKey at0.output.address .regtest).toOption == some at0.output.scriptPubKey)
  check "the fixed key is the same key at every address" (at0.keys[0]! == w.fixedPublic && change0.keys[0]! == w.fixedPublic)
  check "the extended keys are different keys at every address"
    (at0.keys[1]! != change0.keys[1]! && at0.keys[2]! != change0.keys[2]! && at0.keys[1]! != at0.keys[2]!)
  let derived ← needE "ours at 0/0" (·.name) ((← accountKey w.ours).derivedPath #[0, 0])
  check "this wallet's key there is its account key's child 0/0" (at0.keys[1]! == derived.publicKey)
  -- 2 KEY KEY KEY 3 OP_CHECKMULTISIG, the keys in byte order
  let sorted := sortBytes (fun key => key) at0.keys
  check "the witness script: 2, the three keys in byte order, 3, OP_CHECKMULTISIG"
    (at0.witnessScript == ByteArray.mk #[0x52] ++ sorted.foldl (fun s k => s ++ ByteArray.mk #[0x21] ++ k) .empty ++ ByteArray.mk #[0x53, 0xae])
  let watched ← need "watch scripts" (w.account.watchScripts 5)
  check "ten scripts to watch for five indices, all different"
    (watched.size == 10 && SegwitMultisigAccount.allDifferent watched && watched[0]! == at0.output.scriptPubKey &&
      watched[1]! == change0.output.scriptPubKey)
  refused "a third choice" (w.account.resolved 2 0) "indexOutOfRange"
  refused "a hardened index" (w.account.resolved 0 0x8000_0000) "invalidPath"

/-! ## Review -/

def review : TM Unit := do
  let w ← world
  let psbt ← ordinary w
  let tip : UInt32 := 200
  let look (p : PSBT) (coins := w.coins) (owned := #[changeCoordinate]) := w.account.reviewSpend p coins owned tip
  let reviewed ← need "the ordinary spend" (look psbt)
  check "what the spend takes, pays and leaves the miner"
    (reviewed.inputTotal == 150_000 && reviewed.outputTotal == 149_000 && reviewed.fee == 1_000)
  check "what leaves and what returns" (reviewed.outputs.size == 2 && !reviewed.outputs[0]!.isAccountOwned &&
    reviewed.outputs[0]!.amount == 60_000 && reviewed.outputs[1]!.isAccountOwned && reviewed.outputs[1]!.amount == 89_000)
  let unowned ← need "without the change coordinate" (look psbt (owned := #[]))
  check "an output is the account's only at a coordinate the caller gives" (!unowned.outputs[1]!.isAccountOwned)
  let bare := spend w w.coins #[{ value := 149_000, scriptPubKey := destination }] (describe := fun _ => [])
  check "a PSBT that says nothing of its coins is reviewed from the wallet's record" (look bare).isOk
  let reread : Option PSBT := (PSBT.parse psbt.serialized).toOption
  let rereadV0 : Option PSBT := psbt.base64V0.toOption.bind fun text => (PSBT.ofBase64 text).toOption
  check "it survives being written and read, in either envelope"
    ((reread.map fun p => (look p).isOk) == some true && (rereadV0.map fun p => (look p).isOk) == some true)
  let outputs := #[({ value := 149_000, scriptPubKey := destination } : Transaction.Output)]
  let describing (describe : WalletUTXO → List Field) := spend w w.coins outputs describe
  let honest (coin : WalletUTXO) : List Field := [statedCoin coin.amount coin.scriptPubKey]
  refused "a coin the wallet does not know" (look psbt (coins := w.coins.extract 0 1)) "invalidSpend" (says "not an available coin")
  refused "the same coin twice" (look (spend w #[w.coins[0]!, w.coins[0]!] outputs)) "invalidSpend" (says "repeats an earlier outpoint")
  refused "a PSBT that states a smaller amount for a coin"
    (look (describing fun coin => [statedCoin (coin.amount - 1) coin.scriptPubKey])) "invalidSpend" (says "wrong amount")
  refused "a PSBT that states another script for a coin"
    (look (describing fun coin => [statedCoin coin.amount destination])) "invalidSpend" (says "wrong amount or locking script")
  refused "a stated coin that cannot be read"
    (look (describing fun _ => [(PSBT.InType.witnessUTXO, .empty, ByteArray.mk #[1, 2, 3])])) "invalidSpend" (says "wrong amount")
  -- the same transaction with one output's amount changed has another identifier
  let richer := { w.funding with outputs := w.funding.outputs.set! 1 { w.funding.outputs[1]! with value := 100_001 } }
  refused "a previous transaction that is not the coin's"
    (look (describing fun coin => honest coin ++ [(PSBT.InType.nonWitnessUTXO, .empty, richer.serialized false)]))
    "invalidSpend" (says "not the one its coin is from")
  refused "a previous transaction that cannot be read"
    (look (describing fun coin => honest coin ++ [(PSBT.InType.nonWitnessUTXO, .empty, ByteArray.mk #[0, 1])]))
    "invalidSpend" (says "not the one its coin is from")
  let moved := w.coins.set! 0 { w.coins[0]! with index := 1 }
  refused "a coin recorded at an address it is not at" (look psbt (coins := moved)) "invalidSpend" (says "does not belong to this descriptor")
  let lied := w.coins.set! 0 { w.coins[0]! with amount := 0 }
  refused "a coin recorded with no amount" (look bare (coins := lied)) "invalidSpend" (says "wrong amount")
  for (name, hashType) in [("NONE", (2 : UInt32)), ("SINGLE", 3), ("ALL|ANYONECANPAY", 0x81), ("Taproot's default", 0)] do
    refused s!"a signature asked for with SIGHASH_{name}"
      (look (describing fun coin => honest coin ++ [(PSBT.InType.sighashType, .empty, u32LE hashType)]))
      "invalidSpend" (says "does not commit to every output")
  check "SIGHASH_ALL said outright" (look (describing fun coin => honest coin ++ [(PSBT.InType.sighashType, .empty, u32LE 1)])).isOk
  let another ← need "receive 1" (w.account.resolved 0 1)
  refused "another address's witness script on a coin"
    (look (describing fun coin => honest coin ++ [(PSBT.InType.witnessScript, .empty, another.witnessScript)]))
    "invalidSpend" (says "changes the spending policy")
  let own ← need "receive 0" (w.account.resolved 0 0)
  check "the coin's own witness script"
    (look (spend w (w.coins.extract 0 1) #[{ value := 99_000, scriptPubKey := destination }]
      (fun coin => honest coin ++ [(PSBT.InType.witnessScript, .empty, own.witnessScript)]))).isOk
  refused "a fee past a tenth" (look (spend w w.coins #[{ value := 134_999, scriptPubKey := destination }]))
    "invalidSpend" (says "10% safety limit")
  check "a fee of exactly a tenth" (look (spend w w.coins #[{ value := 135_000, scriptPubKey := destination }])).isOk
  refused "outputs past the inputs" (look (spend w w.coins #[{ value := 150_001, scriptPubKey := destination }]))
    "invalidSpend" (says "outputs exceed its known inputs")
  refused "no outputs" (look (spend w w.coins #[])) "invalidSpend" (says "no outputs")
  refused "no inputs" (look (spend w #[] outputs)) "invalidSpend" (says "no inputs")
  refused "an output of nothing" (look (spend w w.coins #[{ value := 0, scriptPubKey := destination }])) "invalidSpend" (says "invalid amount")
  refused "transaction version 3" (look (spend w w.coins outputs (version := 3))) "invalidSpend" (says "version 3")
  let coinbase := w.coins.map fun coin => { coin with isCoinbase := true, height := 150 }
  refused "a coinbase not yet a hundred blocks old" (look psbt (coins := coinbase)) "invalidSpend" (says "coinbase that matures")
  check "a coinbase a hundred blocks old"
    (w.account.reviewSpend psbt (coinbase.map fun coin => { coin with height := 101 }) #[changeCoordinate] tip).isOk

/-! ## Signing and finalizing -/

/-- The fixed key's signature on input `k`, made as a key service makes it: from the digest alone, by code
that knows nothing of the PSBT, and written in under the fixed public key. -/
def fixedKeySigns (w : World) (psbt : PSBT) (k : Nat) (secret : ByteArray := fixedSecret)
    (alter : ByteArray → ByteArray := id) : TM PSBT := do
  let tx ← needE "the transaction" (·.name) psbt.unsignedTransaction
  let coin ← need "the coin" (MultisigAccount.coin psbt k w.coins)
  let (_, digest) ← need "the digest" (w.account.signingContext tx k coin)
  let made ← needE "the signature" (·.name) (publicKeyOf secret)
  let signature ← need "the signature" (SegwitMultisigAccount.partialSignature secret made digest aux0)
  return psbt.modifyInput k (·.setPartialSignature w.fixedPublic (alter signature))

def signing : TM Unit := do
  let w ← world
  let psbt ← ordinary w
  let tip : UInt32 := 200
  let owned := #[changeCoordinate]
  let approvals (p : PSBT) := w.account.approvals p w.coins
  check "nobody has signed" ((approvals psbt).toOption == some #[])
  let ours ← need "this wallet signs" (w.account.sign psbt w.ours w.coins owned tip aux0)
  check "this wallet's key has signed every input" ((approvals ours).toOption == some #[1])
  let own0 ← need "receive 0" (w.account.resolved 0 0)
  check "its signature is filed under its key at each coin, with the witness script beside it"
    (ours.inputs[0]!.partialSignatures.map (·.1) == #[own0.keys[1]!] && ours.inputs[0]!.witnessScript == some own0.witnessScript &&
      ours.inputs[1]!.partialSignatures.size == 1)
  check "a signature is DER and the SIGHASH_ALL byte, at most 73 bytes"
    (ours.inputs.all fun input => input.partialSignatures.all fun (_, s) =>
      s.size ≤ 73 && (SegwitMultisigAccount.countedSignature? s).isSome)
  let account ← accountKey w.ours
  let byAccountKey ← need "its account key signs" (w.account.sign psbt account w.coins owned tip aux0)
  check "the account key by itself signs the same" (byAccountKey.serialized == ours.serialized)
  let fresh ← need "with other randomness" (w.account.sign psbt w.ours w.coins owned tip (sha256 aux0))
  check "fresh randomness makes another signature, as good" (fresh.serialized != ours.serialized && (approvals fresh).toOption == some #[1])
  refused "a wallet that holds none of the keys" (w.account.sign psbt (← master 0xC3) w.coins owned tip aux0) "noSignerKey"
  refused "a public key alone cannot sign" (w.account.sign psbt account.neutered w.coins owned tip aux0) "noSignerKey"
  refused "a spend the review refuses is not signed"
    (w.account.sign (spend w w.coins #[{ value := 100_000, scriptPubKey := destination }]) w.ours w.coins owned tip aux0)
    "invalidSpend" (says "10% safety limit")
  refused "one signature does not finalize" (w.account.finalizeSpend ours w.coins owned tip) "missingField"
  -- the fixed key, on one input and then both
  let half ← fixedKeySigns w ours 0
  check "the fixed key on one input of two has not signed the spend" ((approvals half).toOption == some #[1])
  refused "and it does not finalize" (w.account.finalizeSpend half w.coins owned tip) "missingField"
  let both ← fixedKeySigns w half 1
  check "the fixed key and this wallet have signed" ((approvals both).toOption == some #[0, 1])
  let (finalized, tx) ← need "two signatures finalize" (w.account.finalizeSpend both w.coins owned tip)
  let unsigned ← needE "the unsigned transaction" (·.name) psbt.unsignedTransaction
  check "the transaction is the one reviewed, with witnesses" (tx.txid == unsigned.txid && tx.isSegwit && tx.inputs.all (·.scriptSig.isEmpty))
  for k in [0:2] do
    let coin := w.coins[k]!
    let (resolved, digest) ← need "the context" (w.account.signingContext unsigned k coin)
    let witness := tx.inputs[k]!.witness
    check s!"input {k + 1}: an empty item, two signatures, the witness script"
      (witness.size == 4 && witness[0]!.isEmpty && witness[3]! == resolved.witnessScript)
    -- in the script's key order: each signature verifies under the next key of the sorted list that it can
    let sorted := sortBytes (fun key => key) resolved.keys
    let signer (signature : ByteArray) : Option Nat :=
      (SegwitMultisigAccount.countedSignature? signature).bind fun rs =>
        (List.range sorted.size).find? fun position => accepts (SecpCt.Ecdsa.verify rs digest sorted[position]!)
    check s!"input {k + 1}: the signatures verify, in the order of their keys in the script"
      (match signer witness[1]!, signer witness[2]! with | some first, some second => first < second | _, _ => false)
    check s!"input {k + 1}: nothing of the signing is left in the finalized PSBT"
      (finalized.inputs[k]!.partialSignatures.isEmpty && finalized.inputs[k]!.witnessScript.isNone &&
        finalized.inputs[k]!.finalScriptWitness == some witness)
  -- all three sign: the witness still carries two
  let other ← need "the other member signs" (w.account.sign both w.other w.coins owned tip aux0)
  check "all three have signed" ((approvals other).toOption == some #[0, 1, 2])
  let (_, three) ← need "three signatures finalize" (w.account.finalizeSpend other w.coins owned tip)
  check "the witness carries the threshold and no more" (three.inputs.all (·.witness.size == 4) && three.txid == unsigned.txid)
  -- the two extended keys, without the fixed key
  let pair ← need "the other member signs" (w.account.sign ours w.other w.coins owned tip aux0)
  check "the two extended keys finalize without the fixed key"
    ((approvals pair).toOption == some #[1, 2] && (w.account.finalizeSpend pair w.coins owned tip).isOk)
  -- signatures that are not counted
  let n := Secp.Spec.N
  let upper (signature : ByteArray) : ByteArray :=
    match SegwitMultisigAccount.countedSignature? signature with
    | some rs => (Secp.Ecdsa.der (rs.extract 0 32 ++ Secp.toBE32 (n - Secp.fromBE (rs.extract 32 64)))).push 0x01
    | none => signature
  let uncounted (name : String) (secret : ByteArray) (alter : ByteArray → ByteArray) : TM Unit := do
    let p ← fixedKeySigns w (← fixedKeySigns w ours 0 secret alter) 1 secret alter
    check s!"not counted: {name}" ((approvals p).toOption == some #[1] && !(w.account.finalizeSpend p w.coins owned tip).isOk)
  uncounted "a signature with s in the upper half" fixedSecret upper
  uncounted "a signature marked SIGHASH_NONE" fixedSecret (fun s => s.set! (s.size - 1) 0x02)
  uncounted "a signature with no hash type byte" fixedSecret (fun s => s.extract 0 (s.size - 1))
  uncounted "a signature by another key, filed under the fixed key" (sha256 fixedSecret) id
  uncounted "a signature with a byte changed" fixedSecret (fun s => s.set! 10 (s[10]! ^^^ 1))
  -- a signature under a key that is not the account's at that coin is ignored, not counted
  let stranger ← needE "a stranger's key" (·.name) (publicKeyOf (sha256 fixedSecret))
  let extra := both.modifyInput 0 (·.setPartialSignature stranger both.inputs[0]!.partialSignatures[0]!.2)
  check "a signature filed under a key that is not the account's changes nothing"
    ((approvals extra).toOption == some #[0, 1] && (w.account.finalizeSpend extra w.coins owned tip).isOk)
  -- the PSBT travels: signed here, written, read, in either envelope
  let travelled := (PSBT.parse both.serialized).toOption.bind fun p => (approvals p).toOption
  let asV0 := (both.base64V0.toOption.bind (PSBT.ofBase64 · |>.toOption)).bind fun p => (approvals p).toOption
  check "a signed PSBT written and read keeps its signatures, as version 2 and as version 0"
    (travelled == some #[0, 1] && asV0 == some #[0, 1])
  -- BIP174 key origins, written and read
  let origin : PSBT.KeyOrigin := { masterFingerprint := w.ours.fingerprint, path := #[0x8000_0056, 0x8000_0001, 0x8000_0000, 0, 7] }
  let carrying := (psbt.inputs[0]!.setBIP32Derivation #[(own0.keys[1]!, origin)]).bip32Derivation
  check "a key's origin on an input reads back: fingerprint and path"
    (carrying.size == 1 && carrying[0]!.1 == own0.keys[1]! && carrying[0]!.2.masterFingerprint == w.ours.fingerprint &&
      carrying[0]!.2.path == origin.path)

def main : IO UInt32 := runMain "segwit-test" do
  runTest "opensslSignatures" opensslSignatures
  runTest "publishedVectors" publishedVectors
  runTest "descriptors" descriptors
  runTest "addresses" addresses
  runTest "review" review
  runTest "signing" signing
