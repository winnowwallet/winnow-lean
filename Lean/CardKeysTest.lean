import Lean.Data.Json
import Winnow.Keys
import TestKit.Check

/-! `card-keys-test`: a shared secret and a spend key for one person (`Winnow/Keys/SilentPaymentPairing.lean`,
issue #94) against `Vectors/card-keys-vectors.json`, which `scripts/card-keys-vectors` computes without the
wallet's code: from a BIP32 seed to BIP352's scan and spend keys, a person's tweak, label and code, and each
payment's tweak, output key, script and spending secret, both for the code a person is handed and for the
card 0.9.12 wrote. The label is also held to BIP352's own vectors. Then what the vectors cannot say: that each script is
BIP352's own output for the pairing's shared secret and is not what a standard silent payment to the same
address pays, that the spending secret signs for the output and nothing the payer holds does, that another
tweak, address or index pays another script, and what is refused. Run from `Lean/`. -/

open Lean Winnow Winnow.Keys Winnow.Keys.SilentPaymentPairing TestKit

def hx (s : String) : ByteArray := (ofHex? s).getD .empty

structure PaymentCase where
  index : UInt32
  outputTweak : String
  outputKey : String
  oddY : Bool
  script : String
  spendSecret : String

structure LabelledCase where
  label : String
  spendKey : String
  code : String
  payments : List PaymentCase

structure CardCase where
  plainCode : String
  labelled : Option LabelledCase
  seed : String
  coinType : UInt32
  hrp : String
  card : UInt32
  scanSecret : String
  spendSecret : String
  scanKey : String
  spendKey : String
  address : String
  tweak : String
  sharedSecret : String
  payments : List PaymentCase

def str (j : Json) (k : String) : String := (j.getObjValAs? String k).toOption.getD ""
def num (j : Json) (k : String) : UInt32 := ((j.getObjValAs? Nat k).toOption.getD 0).toUInt32

def cases : IO (List CardCase) := do
  let j ← IO.ofExcept (Json.parse (← IO.FS.readFile "Vectors/card-keys-vectors.json"))
  let mut out := #[]
  let paymentsOf (c : Json) : IO (List PaymentCase) := do
    let mut payments := #[]
    for p in (← IO.ofExcept ((c.getObjValD "payments").getArr?)) do
      payments := payments.push {
        index := num p "index", outputTweak := str p "outputTweak", outputKey := str p "outputKey",
        oddY := (p.getObjValAs? Bool "oddY").toOption.getD false, script := str p "script",
        spendSecret := str p "spendSecret" }
    return payments.toList
  for c in (← IO.ofExcept ((j.getObjValD "cases").getArr?)) do
    let payments ← paymentsOf c
    let l := c.getObjValD "labelled"
    let labelled ← if l.isNull then pure none else
      pure (some { label := str l "label", spendKey := str l "spendKey", code := str l "code", payments := ← paymentsOf l })
    out := out.push {
      plainCode := str c "plainCode", labelled,
      seed := str c "seed", coinType := num c "coinType", hrp := str c "hrp", card := num c "card",
      scanSecret := str c "scanSecret", spendSecret := str c "spendSecret", scanKey := str c "scanKey",
      spendKey := str c "spendKey", address := str c "address", tweak := str c "tweak",
      sharedSecret := str c "sharedSecret", payments }
  return out.toList

def refusedWith {α} (r : PP α) (e : Error) : Bool :=
  match r with | .error got => got == e | .ok _ => false

def message : ByteArray := ByteArray.mk (Array.replicate 32 0x94)
def aux : ByteArray := ByteArray.mk (Array.replicate 32 0)

/-- Whether a BIP340 signature by `secret` over `message` verifies under the x-only key `xonly`. -/
def signsFor (secret xonly : ByteArray) : Bool :=
  match secretOf secret >>= fun d => schnorrSign d message aux with
  | .ok sig => (schnorrVerify xonly message sig).toOption == some true
  | .error _ => false

/-- BIP352's own vectors: every labelled address a receiver expects is `B_scan` with `B_spend + L_m·G`, for
the label this module computes. How many labels were checked. -/
def officialLabels : IO (Nat × Bool) := do
  let j ← IO.ofExcept (Json.parse (← IO.FS.readFile "Vectors/bip352-send-receive-vectors.json"))
  let mut count := 0
  let mut ok := true
  for case in (← IO.ofExcept j.getArr?) do
    for r in (← IO.ofExcept ((case.getObjValD "receiving").getArr?)) do
      let given := r.getObjValD "given"
      let labels := ((given.getObjValD "labels").getArr?).toOption.getD #[]
      if labels.isEmpty then continue
      let material := given.getObjValD "key_material"
      let scan := hx (str material "scan_priv_key")
      let spend := hx (str material "spend_priv_key")
      let expected := (((r.getObjValD "expected").getObjValD "addresses").getArr?).toOption.getD #[]
        |>.filterMap (·.getStr?.toOption)
      for m in labels do
        let some m := m.getNat?.toOption | ok := false
        count := count + 1
        let found : Option String := do
          let own ← (address scan spend "sp").toOption
          let key ← (labelledSpendKey own.spendKey (← (labelAt scan m.toUInt32).toOption)).toOption
          (← (SilentPaymentAddress.make own.scanKey key "sp").toOption).encoded.toOption
        unless found.any expected.contains do ok := false
  return (count, ok)

def main : IO UInt32 := runMain "card-keys-test" do
  let all ← cases
  check "4 cards" (all.length == 4)
  check "18 payments" ((all.map (·.payments.length)).foldl (· + ·) 0 == 18)
  check "output keys of both parities" (all.any (·.payments.any (·.oddY)) && all.any (·.payments.any (!·.oddY)))
  for c in all do
    let n := s!"{c.hrp} card {c.card}"
    let some master := (HDKey.ofSeed (hx c.seed)).toOption | throw (IO.userError s!"{n}: master")
    match keys master c.coinType with
    | .error e => check s!"{n}: keys ({e.name})" false
    | .ok (scan, spend) =>
      check s!"{n}: the scan and spend keys are BIP352's paths" (hex scan == c.scanSecret && hex spend == c.spendSecret)
      check s!"{n}: the address" (((address scan spend c.hrp).toOption.bind (·.encoded.toOption)) == some c.address)
      check s!"{n}: the person's tweak" ((tweakFor scan c.card).toOption.map hex == some c.tweak)
      check s!"{n}: the master's public key derives neither" (refusedWith (keys master.neutered c.coinType) .derivation)
    match issue master c.coinType c.hrp c.card with
    | .error e => check s!"{n}: issued ({e.name})" false
    | .ok card =>
      check s!"{n}: the card is the address and the tweak"
        (card.address.encoded.toOption == some c.address && hex card.tweak == c.tweak &&
         hex card.address.scanKey == c.scanKey && hex card.address.spendKey == c.spendKey)
      check s!"{n}: the shared secret is the tweak times the scan key" ((sharedSecret card).toOption.map hex == some c.sharedSecret)
      for p in c.payments do
        let m := s!"{n} payment {p.index}"
        check s!"{m}: output tweak" ((outputTweak card p.index).toOption.map hex == some p.outputTweak)
        check s!"{m}: script" ((scriptPubKey card p.index).toOption.map hex == some p.script)
        check s!"{m}: the script is BIP352's own output for that shared secret"
          ((SilentPaymentSending.outputScript (hx c.sharedSecret) card.address.spendKey p.index).toOption.map hex == some p.script)
        match spendSecret (hx c.spendSecret) card p.index with
        | .error e => check s!"{m}: spending secret ({e.name})" false
        | .ok secret =>
          check s!"{m}: spending secret" (hex secret == p.spendSecret)
          check s!"{m}: the spending secret's point is the output key"
            ((publicKeyOf secret).toOption.map (·.extract 1 33) == some (hx p.outputKey) &&
             (publicKeyOf secret).toOption.map (·[0]! == 0x03) == some p.oddY)
          check s!"{m}: the recipient signs for the output" (signsFor secret (hx p.outputKey))
          -- what the payer holds: the person's tweak, and so the output's tweak
          check s!"{m}: the person's tweak does not sign for the output" (!signsFor card.tweak (hx p.outputKey))
          check s!"{m}: the output's tweak does not sign for the output" (!signsFor (hx p.outputTweak) (hx p.outputKey))
          check s!"{m}: the spend key alone does not sign for the output" (!signsFor (hx c.spendSecret) (hx p.outputKey))
    -- the 0.9.12 card as a code: the same scripts, with the wallet's own spend key
    match issue master c.coinType c.hrp c.card >>= codeOf with
    | .error e => check s!"{n}: its code ({e.name})" false
    | .ok plain =>
      check s!"{n}: a 0.9.12 card as a code" (plain.encoded.toOption == some c.plainCode &&
        hex plain.sharedSecret == c.sharedSecret && hex plain.spendKey == c.spendKey)
      check s!"{n}: that code pays what the card pays"
        (c.payments.all fun p => (codeScript plain p.index).toOption.map hex == some p.script)
    -- the code a person is handed: their shared secret and a spend key of their own
    match c.labelled, issueCode master c.coinType c.hrp c.card with
    | none, r => check s!"{n}: the last index has no label, so no code" (refusedWith r .invalidIndex)
    | some _, .error e => check s!"{n}: code ({e.name})" false
    | some l, .ok code =>
      check s!"{n}: the label is BIP352's label {c.card + 1}"
        ((labelFor (hx c.scanSecret) c.card).toOption.map hex == some l.label &&
         (labelAt (hx c.scanSecret) (c.card + 1)).toOption.map hex == some l.label)
      check s!"{n}: the code is the shared secret and the labelled spend key"
        (code.encoded.toOption == some l.code && hex code.sharedSecret == c.sharedSecret && hex code.spendKey == l.spendKey)
      check s!"{n}: the code holds neither of the wallet's keys"
        (hex code.sharedSecret != c.scanKey && hex code.spendKey != c.spendKey && hex code.sharedSecret != c.spendKey)
      check s!"{n}: the code reads back" ((CardCode.decode l.code (some c.hrp)).toOption == some code)
      for p in l.payments do
        let m := s!"{n} labelled payment {p.index}"
        check s!"{m}: script" ((codeScript code p.index).toOption.map hex == some p.script)
        check s!"{m}: not the script a 0.9.12 card pays"
          ((c.payments.find? (·.index == p.index)).map (·.script) != some p.script)
        match codeSpendSecret (hx c.spendSecret) (some (hx l.label)) code p.index with
        | .error e => check s!"{m}: spending secret ({e.name})" false
        | .ok secret =>
          check s!"{m}: spending secret" (hex secret == p.spendSecret)
          check s!"{m}: the recipient signs for the output" (signsFor secret (hx p.outputKey))
          check s!"{m}: the spend key alone does not sign for the output" (!signsFor (hx c.spendSecret) (hx p.outputKey))
          check s!"{m}: the label does not sign for the output" (!signsFor (hx l.label) (hx p.outputKey))
        check s!"{m}: without its label the spend key is refused"
          (refusedWith (codeSpendSecret (hx c.spendSecret) none code p.index) .keyMismatch)
      check s!"{n}: another person's label is refused"
        (refusedWith (codeSpendSecret (hx c.spendSecret) ((labelFor (hx c.scanSecret) (c.card + 1)).toOption) code 0) .keyMismatch)
  let (officialCount, officialOK) ← officialLabels
  check s!"BIP352's vectors: {officialCount} labelled addresses are B_scan with B_spend + L·G" (officialOK && officialCount ≥ 8)
  -- one card, read back from its vector
  let some first := all.head? | throw (IO.userError "a first card")
  let some second := all[1]? | throw (IO.userError "a second card")
  let some third := all[2]? | throw (IO.userError "a third card")
  let some firstAddress := (SilentPaymentAddress.decode first.address (some (SilentPaymentPairing.hrp true))).toOption
    | throw (IO.userError "the first address")
  let card : PairingCard := { address := firstAddress, tweak := hx first.tweak }
  let some script := (scriptPubKey card 0).toOption | throw (IO.userError "the first script")
  let scriptOf (c : PairingCard) (i : UInt32) : Option ByteArray := (scriptPubKey c i).toOption
  -- what a payment's address depends on
  check "two people of one wallet have the same address and different tweaks"
    (first.address == second.address && first.tweak != second.tweak)
  check "another index pays another script" (scriptOf card 1 != some script && (scriptOf card 1).isSome)
  check "another person's tweak pays another script" (scriptOf { card with tweak := hx second.tweak } 0 != some script)
  let some testAddress := (SilentPaymentAddress.decode third.address (some (SilentPaymentPairing.hrp false))).toOption
    | throw (IO.userError "the third address")
  check "the same tweak with another wallet's address pays another script" (scriptOf { card with address := testAddress } 0 != some script)
  -- the form a card's address is written in: the keys of a silent payment address under a prefix that is not one's
  check "a card's address is written with the card's prefix"
    (first.address.startsWith "winnowcard1" && third.address.startsWith "twinnowcard1" &&
     SilentPaymentPairing.looksLikeCardAddress first.address && SilentPaymentPairing.looksLikeCardAddress third.address.toUpper)
  check "a card's address does not look like a silent payment address"
    (!SilentPaymentAddress.looksLikeCode first.address && !SilentPaymentAddress.looksLikeCode third.address)
  check "a reader of silent payment addresses refuses a card's address, on either kind of network"
    ((match SilentPaymentAddress.decode first.address (some (SilentPayment.hrp true)) with
      | .error (.wrongHRP "sp" "winnowcard") => true | _ => false) &&
     (match SilentPaymentAddress.decode third.address (some (SilentPayment.hrp false)) with
      | .error (.wrongHRP "tsp" "twinnowcard") => true | _ => false))
  check "a silent payment address does not look like a card's"
    (match ({ firstAddress with hrp := "sp" } : SilentPaymentAddress).encoded with
     | .ok plain => plain.startsWith "sp1" && !SilentPaymentPairing.looksLikeCardAddress plain && plain != first.address
     | .error _ => false)
  check "the prefix is in no payment: the same keys under another prefix pay the same script"
    (scriptOf { card with address := { firstAddress with hrp := "sp" } } 0 == some script)
  check "500 payments of one person are 500 scripts" (Id.run do
    let mut seen : Std.HashSet ByteArray := {}
    for i in [0:500] do
      match scriptOf card i.toUInt32 with
      | some s => seen := seen.insert s
      | none => return false
    return seen.size == 500)
  -- the code's form: version 1 under the card's prefix, which is neither the wallet's two keys nor an address
  let some firstCode := first.labelled | throw (IO.userError "the first code")
  let some secondCode := second.labelled | throw (IO.userError "the second code")
  let some thirdCode := third.labelled | throw (IO.userError "the third code")
  check "a code is written with the card's prefix, as version 1"
    (firstCode.code.startsWith "winnowcard1p" && thirdCode.code.startsWith "twinnowcard1p" &&
     looksLikeCardCode firstCode.code && looksLikeCardCode thirdCode.code.toUpper && !looksLikeCardKeys firstCode.code)
  check "the wallet's two keys are version 0, and are not a code"
    (first.address.startsWith "winnowcard1q" && looksLikeCardKeys first.address && !looksLikeCardCode first.address)
  check "a code is not read as the two keys, nor the two keys as a code"
    ((match SilentPaymentAddress.decode firstCode.code (some (SilentPaymentPairing.hrp true)) with
      | .error (.unsupportedVersion 1) => true | _ => false) &&
     (match CardCode.decode first.address (some (SilentPaymentPairing.hrp true)) with
      | .error (.unsupportedVersion 0) => true | _ => false))
  check "a code of another kind of network is refused"
    (match CardCode.decode thirdCode.code (some (SilentPaymentPairing.hrp true)) with
     | .error (.wrongHRP "winnowcard" "twinnowcard") => true | _ => false)
  check "a code does not look like a silent payment address" (!SilentPaymentAddress.looksLikeCode firstCode.code)
  check "two people of one wallet are handed codes with no key in common"
    (firstCode.spendKey != secondCode.spendKey && first.sharedSecret != second.sharedSecret &&
     firstCode.code.drop 14 != secondCode.code.drop 14)
  check "a code with a point off the curve is not made"
    ((CardCode.make (ByteArray.mk #[0x02] ++ ByteArray.mk (Array.replicate 32 0xFF)) (hx firstCode.spendKey) "winnowcard").toOption.isNone &&
     (CardCode.make (hx first.sharedSecret) (ByteArray.mk (Array.replicate 33 0)) "winnowcard").toOption.isNone)
  check "a damaged code is refused"
    ((CardCode.decode (firstCode.code ++ "q") none).toOption.isNone && (CardCode.decode ("x" ++ firstCode.code) none).toOption.isNone)
  -- it is not a standard silent payment: one made by spending a coin pays another script
  let payerKey := ByteArray.mk (Array.replicate 31 0) ++ ByteArray.mk #[7]
  let some payerPoint := (publicKeyOf payerKey).toOption | throw (IO.userError "the payer's key")
  let coin : SilentPaymentSending.Input :=
    { txid := ByteArray.mk (Array.replicate 32 1), vout := 0, privateKey := payerKey,
      prevoutScriptPubKey := ByteArray.mk #[0x51, 0x20] ++ payerPoint.extract 1 33 }
  check "a standard silent payment to the same address pays a script the card does not derive"
    (match SilentPaymentSending.outputScripts [coin] [firstAddress] with
     | .ok [standard] => (List.range 40).all fun i => scriptOf card i.toUInt32 != some standard
     | _ => false)
  -- what is refused
  let zero := ByteArray.mk (Array.replicate 32 0)
  let order := hx "fffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd0364141"
  check "a zero tweak" (refusedWith (scriptPubKey { card with tweak := zero } 0) .invalidTweak)
  check "a tweak that is the group order" (refusedWith (scriptPubKey { card with tweak := order } 0) .invalidTweak)
  check "a short tweak" (refusedWith (scriptPubKey { card with tweak := card.tweak.extract 0 31 } 0) .invalidTweak)
  let offCurve := ByteArray.mk #[0x02] ++ ByteArray.mk (Array.replicate 32 0xFF)
  check "a scan key off the curve" (refusedWith (scriptPubKey { card with address := { firstAddress with scanKey := offCurve } } 0) .invalidAddress)
  check "a spend key off the curve" (refusedWith (scriptPubKey { card with address := { firstAddress with spendKey := offCurve } } 0) .invalidAddress)
  -- the spending secret is the recipient's alone
  check "the scan key is not the spend key" (refusedWith (spendSecret (hx first.scanSecret) card 0) .keyMismatch)
  check "another wallet's spend key is refused" (refusedWith (spendSecret (hx third.spendSecret) card 0) .keyMismatch)
  check "a zero private key is refused" (refusedWith (spendSecret zero card 0) .invalidPrivateKey)
  check "a short private key is refused" (refusedWith (spendSecret ((hx first.spendSecret).extract 0 31) card 0) .invalidPrivateKey)
  -- tweaks
  check "a person's tweak needs a scan key" (refusedWith (tweakFor zero 0) .invalidPrivateKey)
  check "200 people of one wallet have 200 tweaks" (Id.run do
    let mut seen : Std.HashSet ByteArray := {}
    for k in [0:200] do
      match tweakFor (hx first.scanSecret) k.toUInt32 with
      | .ok x => seen := seen.insert x
      | .error _ => return false
    return seen.size == 200)
  check "the same person index in another wallet has another tweak"
    ((tweakFor (hx first.scanSecret) 0).toOption != (tweakFor (hx third.scanSecret) 0).toOption)
