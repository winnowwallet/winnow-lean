import Lean.Data.Json
import Winnow.Keys
import Winnow.Keys.BIP86
import Winnow.Wallet.People

/-! `silent-payment-test`: upstream's `SilentPaymentTests`: every sending case of the official BIP352
vectors (`Vectors/bip352-send-receive-vectors.json`: eligibility, the key sum, the shared secrets and the
output set), address round trips and negatives, the same code paid twice, and the sender's view of an
unsigned P2TR input. Run from `Lean/`. -/

open Lean Winnow Winnow.Keys Winnow.Keys.SilentPaymentSending

initialize passes : IO.Ref Nat ← IO.mkRef 0
initialize failures : IO.Ref Nat ← IO.mkRef 0

def check (name : String) (ok : Bool) : IO Unit := do
  if ok then passes.modify (· + 1) else
    failures.modify (· + 1)
    IO.eprintln s!"FAIL {name}"

def hx (s : String) : ByteArray := (ofHex? s).getD .empty

/-- The vectors' witness serialization: CompactSize count, then CompactSize-prefixed items. -/
def witnessStack (b : ByteArray) : Option (List ByteArray) := Id.run do
  if b.isEmpty then return some []
  let mut i := 0
  let varint (i : Nat) : Option (Nat × Nat) :=
    match b[i]? with
    | none => none
    | some f =>
      if f.toNat < 0xFD then some (f.toNat, i + 1)
      else if f == 0xFD then
        match b[i+1]?, b[i+2]? with
        | some lo, some hi => some (lo.toNat + hi.toNat * 256, i + 3)
        | _, _ => none
      else none
  let some (count, j) := varint i | return none
  i := j
  let mut out := #[]
  for _ in [0:count] do
    let some (len, k) := varint i | return none
    if k + len > b.size then return none
    out := out.push (b.extract k (k + len))
    i := k + len
  return if i == b.size then some out.toList else none

structure Case where
  comment : String
  inputs : List Input
  addresses : List String
  scanKeys : List String
  spendKeys : List String
  outputs : List (List String)
  secrets : List (Option String)
  keySum : Option String
  inputKeys : List String

def str (j : Json) (k : String) : String := (j.getObjValAs? String k).toOption.getD ""

def cases : IO (List Case) := do
  let j ← IO.ofExcept (Json.parse (← IO.FS.readFile "Vectors/bip352-send-receive-vectors.json"))
  let entries ← IO.ofExcept (j.getArr?)
  let mut out := #[]
  for e in entries do
    let comment := str e "comment"
    for s in (← IO.ofExcept ((e.getObjValD "sending").getArr?)) do
      let given := s.getObjValD "given"
      let expected := s.getObjValD "expected"
      let mut inputs := #[]
      for v in (← IO.ofExcept ((given.getObjValD "vin").getArr?)) do
        let some witness := witnessStack (hx (str v "txinwitness")) | throw (IO.userError s!"witness in {comment}")
        let script := (((v.getObjValD "prevout").getObjValD "scriptPubKey").getObjValAs? String "hex").toOption.getD ""
        inputs := inputs.push {
          txid := ByteArray.mk (hx (str v "txid")).toList.reverse.toArray
          vout := ((v.getObjValAs? Nat "vout").toOption.getD 0).toUInt32
          prevoutScriptPubKey := hx script, scriptSig := hx (str v "scriptSig"), witness
          privateKey := hx (str v "private_key") }
      let mut addresses := #[]
      let mut scans := #[]
      let mut spends := #[]
      for r in (← IO.ofExcept ((given.getObjValD "recipients").getArr?)) do
        for _ in [0:(r.getObjValAs? Nat "count").toOption.getD 1] do
          addresses := addresses.push (str r "address")
          scans := scans.push (str r "scan_pub_key")
          spends := spends.push (str r "spend_pub_key")
      let outputs := ((expected.getObjValAs? (List (List String)) "outputs").toOption.getD [])
      let secrets := ((expected.getObjValAs? (List (Option String)) "shared_secrets").toOption.getD [])
      out := out.push {
        comment, inputs := inputs.toList, addresses := addresses.toList, scanKeys := scans.toList,
        spendKeys := spends.toList, outputs, secrets
        keySum := (expected.getObjValAs? String "input_private_key_sum").toOption
        inputKeys := (expected.getObjValAs? (List String) "input_pub_keys").toOption.getD [] }
  return out.toList

def failsWith {α} (r : Except SilentPaymentAddressError α) (e : SilentPaymentAddressError) : Bool :=
  match r with
  | .error x => x == e
  | .ok _ => false

def errOf {α} (r : Except String α) : Option String := match r with | .error e => some e | .ok _ => none

def sameSet (a b : List String) : Bool := a.length == b.length && a.all b.contains && b.all a.contains

def main : IO UInt32 := do
  let all ← cases
  check "28 sending cases" (all.length == 28)
  for c in all do
    let n := c.comment
    let recipients := c.addresses.filterMap fun a => (SilentPaymentAddress.decode a (some "sp")).toOption
    check s!"{n}: the codes decode" (recipients.length == c.addresses.length)
    check s!"{n}: the codes' keys" (recipients.map (hex ·.scanKey) == c.scanKeys && recipients.map (hex ·.spendKey) == c.spendKeys)
    check s!"{n}: eligibility" ((c.inputs.filterMap (·.eligiblePublicKey)).map hex == c.inputKeys)
    let result := outputScripts c.inputs recipients
    if c.outputs == [[]] then
      let want : Error :=
        if c.inputKeys.isEmpty then .noEligibleInputs
        else if c.keySum.isNone then .inputKeysSumToZero
        else .tooManyRecipientsPerGroup
      check s!"{n}: fails with {want.name}" (match result with | .error e => e == want | .ok _ => false)
      continue
    match context c.inputs with
    | .error e => check s!"{n}: context ({e.name})" false
    | .ok ctx =>
      check s!"{n}: key sum" (some (hex ctx.privateKeySum) == c.keySum)
      check s!"{n}: input keys" (ctx.eligiblePublicKeys.map hex == c.inputKeys)
      for (r, i) in recipients.zipIdx do
        check s!"{n}: shared secret {i}" ((sharedSecret ctx r.scanKey).toOption.map hex == c.secrets[i]?.join)
    match result with
    | .error e => check s!"{n}: outputs ({e.name})" false
    | .ok scripts =>
      check s!"{n}: one P2TR script per recipient" (scripts.length == recipients.length &&
        scripts.all fun s => s.size == 34 && s[0]! == 0x51 && s[1]! == 0x20)
      let set := scripts.map fun s => hex (s.extract 2 34)
      check s!"{n}: the output set" (c.outputs.any (sameSet set))
  -- round trips
  let mut seen : List String := []
  for c in all do
    for a in c.addresses do
      if seen.contains a then continue
      seen := a :: seen
      match SilentPaymentAddress.decode a (some "sp") with
      | .ok d =>
        check s!"round trip {a}" (d.encoded.toOption == some a)
        check s!"rebuilt {a}" ((SilentPaymentAddress.make d.scanKey d.spendKey "sp").toOption.bind (·.encoded.toOption) == some a)
      | .error _ => check s!"decode {a}" false
  check "some codes round-tripped" (!seen.isEmpty)
  -- negatives (addressValidation)
  let valid := "sp1qqgste7k9hx0qftg6qmwlkqtwuy6cycyavzmzj85c6qdfhjdpdjtdgqjuexzk6murw56suy3e0rd2cgqvycxttddwsvgxe2usfpxumr70xc9pkqwv"
  let some decoded := (SilentPaymentAddress.decode valid (some "sp")).toOption | throw (IO.userError "valid code")
  check "wrong HRP" (failsWith (SilentPaymentAddress.decode valid (some "tsp")) (.wrongHRP "tsp" "sp"))
  check "bad checksum" (failsWith (SilentPaymentAddress.decode (String.ofList (valid.toList.dropLast) ++ "p")) .invalidEncoding)
  check "117 characters exceed BIP173's limit" (match Bech32.decode valid with | .error .tooLong => true | _ => false)
  check "but not BIP352's" ((SilentPaymentAddress.decode valid).toOption == some decoded)
  let payload := (SegwitAddress.convertBits (decoded.scanKey ++ decoded.spendKey).toList 8 5 true).toOption.getD []
  let enc (data : List UInt8) (e : Bech32Encoding) := (Bech32.encode "sp" data e SilentPaymentAddress.maxAddressLength).toOption.getD ""
  check "bech32 refused" (failsWith (SilentPaymentAddress.decode (enc (0 :: payload) .bech32)) .invalidEncoding)
  check "version 1 refused" (failsWith (SilentPaymentAddress.decode (enc (1 :: payload) .bech32m)) (.unsupportedVersion 1))
  let short := (SegwitAddress.convertBits ((decoded.scanKey ++ decoded.spendKey).extract 0 65).toList 8 5 true).toOption.getD []
  check "65 bytes refused" (failsWith (SilentPaymentAddress.decode (enc (0 :: short) .bech32m)) (.invalidDataLength 65))
  let badKey := ByteArray.mk #[0x02] ++ ByteArray.mk (Array.replicate 32 0xFF)
  check "a key off the curve" ((SilentPaymentAddress.make badKey decoded.spendKey "sp").toOption.isNone)
  let badPayload := (SegwitAddress.convertBits (badKey ++ decoded.spendKey).toList 8 5 true).toOption.getD []
  check "a code with a key off the curve" (failsWith (SilentPaymentAddress.decode (enc (0 :: badPayload) .bech32m)) .invalidPublicKey)
  check "mixed case" (failsWith (SilentPaymentAddress.decode ("sp1QQ" ++ String.ofList (valid.toList.drop 4))) .invalidEncoding)
  check "shape: upper case with a space" (SilentPaymentAddress.looksLikeCode (" " ++ valid.toUpper))
  check "shape: tsp1" (SilentPaymentAddress.looksLikeCode "tsp1qqexample")
  check "shape: not bc1p" (!SilentPaymentAddress.looksLikeCode ("bc1p" ++ String.ofList (valid.toList.drop 4)))
  check "shape: not tb1q" (!SilentPaymentAddress.looksLikeCode "tb1qexample")
  -- the same code twice (k index)
  match all.find? (fun c => c.addresses.length == 2 && c.addresses[0]? == c.addresses[1]? && c.outputs != [[]]) with
  | some c =>
    let a := (SilentPaymentAddress.decode c.addresses[0]! (some "sp")).toOption.get!
    match outputScripts c.inputs [a, a] with
    | .ok [s0, s1] =>
      check "same code twice: two distinct outputs" (s0 != s1)
      check "same code twice: the vector's set" (c.outputs.any (sameSet [hex (s0.extract 2 34), hex (s1.extract 2 34)]))
    | _ => check "same code twice" false
  | none => check "a same-code vector" false
  -- the sender's view: an unsigned P2TR key-path input counts; a NUMS script path and v2+ do not
  let outputKey := (BIP86.tweakedOutputKey (hx "a60869f0dbcf1dc659c9cecbaf8050135ea9e8cdc487053f1dc6880949dc684c")).toOption.getD .empty
  let one := ByteArray.mk (Array.replicate 31 0) ++ ByteArray.mk #[1]
  let txid := ByteArray.mk (Array.replicate 32 1)
  let keyPath : Input := { txid, vout := 0, prevoutScriptPubKey := ByteArray.mk #[0x51, 0x20] ++ outputKey, privateKey := one }
  check "unsigned P2TR key path counts" (keyPath.eligiblePublicKey == some (ByteArray.mk #[0x02] ++ outputKey))
  let nums := ByteArray.mk #[0xC1] ++ Taproot.unspendableInternalKey
  check "NUMS script path skipped" ({ keyPath with witness := [ByteArray.mk (Array.replicate 64 0), ByteArray.mk #[0xAB], nums] } : Input).eligiblePublicKey.isNone
  check "witness v2 skipped" ({ keyPath with prevoutScriptPubKey := ByteArray.mk #[0x52, 0x20] ++ outputKey } : Input).eligiblePublicKey.isNone
  -- P2PKH: the key found in a canonical scriptSig
  let pub := (publicKeyPoint one).toOption.getD .empty
  let p2pkh := ByteArray.mk #[0x76, 0xA9, 0x14] ++ hash160 pub ++ ByteArray.mk #[0x88, 0xAC]
  let scriptSig := ByteArray.mk #[0x47] ++ ByteArray.mk (Array.replicate 71 0x30) ++ ByteArray.mk #[0x21] ++ pub
  check "P2PKH key from the scriptSig" (eligiblePublicKey p2pkh scriptSig [] == some pub)
  -- PeopleTests.silentPaymentCodePaste: a code is a reusable pay-to of its own kind
  let some master := (HDKey.ofSeed (ByteArray.mk (Array.replicate 32 0x5A))).toOption | throw (IO.userError "master")
  let scan := (master.derived "m/352'/1'/0'/1'/0").toOption.get!.neutered.publicKey
  let spend := (master.derived "m/352'/1'/0'/0'/0").toOption.get!.neutered.publicKey
  let signet := ((SilentPaymentAddress.make scan spend "tsp").toOption.bind (·.encoded.toOption)).getD ""
  let mainnetCode := ((SilentPaymentAddress.make scan spend "sp").toOption.bind (·.encoded.toOption)).getD ""
  match PersonPaste.parse s!" {signet.toUpper}\n" .signet with
  | .ok imported =>
    check "person: a pasted code" (imported == { name := none, payTo := some (.silentPayment signet), source := .address })
    let payTo := imported.payTo.get!
    check "person: a code is a silent payment, not fresh addresses" (payTo.isSilentPayment && !payTo.derivesFreshAddresses)
    check "person: its address at any index is the code" ((payTo.addressAt 7 .signet).toOption == some signet)
    check "person: no scripts to watch" ((payTo.scripts 20 .signet).toOption == some #[])
    check "person: identified by its keys" ((payTo.identity .signet).toOption == some (scan ++ spend))
    check "person: no fixed script" (errOf (payTo.scriptPubKeyAt 0 .signet) == some "noFixedScript")
  | .error e => check s!"person: a pasted code ({e})" false
  check "person: a mainnet code on signet says so" (errOf (PersonPaste.parse mainnetCode .signet) == some "wrongHRP")
  check "person: a code-shaped paste that is not one" (errOf (PersonPaste.parse "sp1qqexample" .signet) == some "unrecognised")
  let card : PersonCard := { network := "signet", name := "Robin", payTo := some signet }
  check "person: a card paying a code" ((PersonPaste.parse card.serialized .signet).toOption.bind (·.payTo) == some (.silentPayment signet))
  let p ← passes.get
  let f ← failures.get
  IO.println s!"silent-payment-test: {p} passed, {f} failed"
  return if f == 0 then 0 else 1
