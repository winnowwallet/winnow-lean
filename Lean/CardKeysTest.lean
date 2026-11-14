import Lean.Data.Json
import Winnow.Keys
import TestKit.Check

/-! `card-keys-test`: the card code and its derivation (`Winnow/Keys/CardKeys.lean`, issue #94) against
`Vectors/card-keys-vectors.json`, which `scripts/card-keys-vectors` computes without the wallet's code: from a
BIP32 seed to the account key, the card's node, its code, and each payment's tweak, output key, script and
spending secret. Then what the vectors cannot say: that the spending secret signs for the output and the
tweak alone does not, that another network, key, seed or index pays another script, that the account's
public key derives no card, and which codes are refused. Run from `Lean/`. -/

open Lean Winnow Winnow.Keys Winnow.Keys.CardKeys TestKit

def hx (s : String) : ByteArray := (ofHex? s).getD .empty

structure PaymentCase where
  index : UInt32
  tweak : String
  outputKey : String
  oddY : Bool
  script : String
  spendSecret : String

structure CardCase where
  seed : String
  accountPath : String
  hrp : String
  card : UInt32
  secret : String
  key : String
  cardSeed : String
  code : String
  payments : List PaymentCase

def str (j : Json) (k : String) : String := (j.getObjValAs? String k).toOption.getD ""
def num (j : Json) (k : String) : UInt32 := ((j.getObjValAs? Nat k).toOption.getD 0).toUInt32

def cases : IO (List CardCase) := do
  let j ← IO.ofExcept (Json.parse (← IO.FS.readFile "Vectors/card-keys-vectors.json"))
  let mut out := #[]
  for c in (← IO.ofExcept ((j.getObjValD "cases").getArr?)) do
    let mut payments := #[]
    for p in (← IO.ofExcept ((c.getObjValD "payments").getArr?)) do
      payments := payments.push {
        index := num p "index", tweak := str p "tweak", outputKey := str p "outputKey",
        oddY := (p.getObjValAs? Bool "oddY").toOption.getD false, script := str p "script",
        spendSecret := str p "spendSecret" }
    out := out.push {
      seed := str c "seed", accountPath := str c "accountPath", hrp := str c "hrp", card := num c "card",
      secret := str c "secret", key := str c "key", cardSeed := str c "cardSeed", code := str c "code",
      payments := payments.toList }
  return out.toList

def failsWith {α} (r : Except CardCodeError α) (e : CardCodeError) : Bool :=
  match r with | .error got => got == e | .ok _ => false

def refusedWith {α} (r : CK α) (e : Error) : Bool :=
  match r with | .error got => got == e | .ok _ => false

def message : ByteArray := ByteArray.mk (Array.replicate 32 0x94)
def aux : ByteArray := ByteArray.mk (Array.replicate 32 0)

/-- Whether a BIP340 signature by `secret` over `message` verifies under the x-only key `xonly`. -/
def signsFor (secret xonly : ByteArray) : Bool :=
  match secretOf secret >>= fun d => schnorrSign d message aux with
  | .ok sig => (schnorrVerify xonly message sig).toOption == some true
  | .error _ => false

def main : IO UInt32 := runMain "card-keys-test" do
  let all ← cases
  check "5 cards" (all.length == 5)
  check "22 payments" ((all.map (·.payments.length)).foldl (· + ·) 0 == 22)
  check "output keys of both parities" (all.any (·.payments.any (·.oddY)) && all.any (·.payments.any (!·.oddY)))
  for c in all do
    let n := s!"{c.hrp} card {c.card}"
    let some master := (HDKey.ofSeed (hx c.seed)).toOption | throw (IO.userError s!"{n}: master")
    let some account := (master.derived c.accountPath).toOption | throw (IO.userError s!"{n}: account")
    match issue account c.card c.hrp with
    | .error e => check s!"{n}: issued ({e.name})" false
    | .ok (code, secret) =>
      check s!"{n}: the key" (hex code.key == c.key)
      check s!"{n}: the seed" (hex code.seed == c.cardSeed)
      check s!"{n}: the private key" (hex secret == c.secret)
      check s!"{n}: the code" (code.encoded.toOption == some c.code)
      check s!"{n}: the code decodes to the card" ((CardCode.decode c.code (some c.hrp)).toOption == some code)
      check s!"{n}: an upper-case code" ((CardCode.decode c.code.toUpper).toOption == some code)
      check s!"{n}: shaped like a code" (CardCode.looksLikeCode s!" {c.code.toUpper}\n")
      check s!"{n}: the account's public key derives no card" (refusedWith (node account.neutered c.card) .derivation)
      for p in c.payments do
        let m := s!"{n} payment {p.index}"
        check s!"{m}: tweak" ((tweak code p.index).toOption.map hex == some p.tweak)
        check s!"{m}: script" ((scriptPubKey code p.index).toOption.map hex == some p.script)
        match outputKey code p.index with
        | .error e => check s!"{m}: output key ({e.name})" false
        | .ok point =>
          check s!"{m}: output key" (hex (xonlyBytes point) == p.outputKey && hasOddY point == p.oddY)
          match spendSecret secret code p.index with
          | .error e => check s!"{m}: spending secret ({e.name})" false
          | .ok spend =>
            check s!"{m}: spending secret" (hex spend == p.spendSecret)
            check s!"{m}: the spending secret's point is the output key"
              ((publicKeyOf spend).toOption == some (serializeCompressed point))
            check s!"{m}: the issuer signs for the output" (signsFor spend (xonlyBytes point))
            -- what the payer holds: the tweak, and the card's public key
            check s!"{m}: the tweak alone does not sign for the output" (!signsFor (hx p.tweak) (xonlyBytes point))
            check s!"{m}: the card's key alone does not sign for the output" (!signsFor secret (xonlyBytes point))
  -- one card, read back from its code
  let some first := all.head? | throw (IO.userError "a first card")
  let some code := (CardCode.decode first.code).toOption | throw (IO.userError "the first code")
  let some script := (scriptPubKey code 0).toOption | throw (IO.userError "the first script")
  -- what a tweak binds
  let scriptOf (c : CardCode) (i : UInt32) : Option ByteArray := (scriptPubKey c i).toOption
  check "another index pays another script" (scriptOf code 1 != some script && (scriptOf code 1).isSome)
  for hrp in [CardCode.signetHRP, CardCode.regtestHRP] do
    check s!"the same key and seed on {hrp} pay another script"
      (scriptOf { code with hrp } 0 != some script && (scriptOf { code with hrp } 0).isSome)
  let otherSeed := ByteArray.mk (code.seed.toList.map (· ^^^ 1)).toArray
  check "another seed pays another script" (scriptOf { code with seed := otherSeed } 0 != some script)
  let some second := all[1]? | throw (IO.userError "a second card")
  check "another card's key with this seed pays another script"
    (scriptOf { code with key := hx second.key } 0 != some script)
  check "two cards of one wallet share neither key nor seed" (first.key != second.key && first.cardSeed != second.cardSeed)
  check "500 payments of one card are 500 scripts" (Id.run do
    let mut seen : Std.HashSet ByteArray := {}
    for i in [0:500] do
      match scriptOf code i.toUInt32 with
      | some s => seen := seen.insert s
      | none => return false
    return seen.size == 500)
  -- the derivation refuses what is not a card
  check "an HRP that names no network" (refusedWith (tweak { code with hrp := "sp" } 0) .invalidCode)
  check "a short seed" (refusedWith (tweak { code with seed := code.seed.extract 0 31 } 0) .invalidCode)
  let offCurve := ByteArray.mk #[0x02] ++ ByteArray.mk (Array.replicate 32 0xFF)
  check "a key off the curve pays nothing" (refusedWith (scriptPubKey { code with key := offCurve } 0) .invalidCode)
  -- the spending secret is the issuer's alone
  check "another card's private key is refused" (refusedWith (spendSecret (hx second.secret) code 0) .keyMismatch)
  check "a zero private key is refused"
    (refusedWith (spendSecret (ByteArray.mk (Array.replicate 32 0)) code 0) .invalidPrivateKey)
  check "a short private key is refused" (refusedWith (spendSecret (hx first.secret |>.extract 0 31) code 0) .invalidPrivateKey)
  -- where cards live
  let some master := (HDKey.ofSeed (hx first.seed)).toOption | throw (IO.userError "master")
  let some account := (master.derived first.accountPath).toOption | throw (IO.userError "account")
  check "a card index past the hardened range" (refusedWith (node account HDKey.hardenedOffset) .derivation)
  check "the last card index" ((node account (HDKey.hardenedOffset - 1)).toOption.isSome)
  check "a card's node is account/2'/k'"
    ((node account 7).toOption.map (·.publicKey) == (account.derived "2'/7'").toOption.map (·.publicKey))
  let unhardened := [0, 1, 2].filterMap fun chain => (account.neutered.child chain).toOption
  check "the account's public key reaches no card key in its first children" (unhardened.length == 3 &&
    unhardened.all fun chain => (List.range 40).all fun i =>
      ((chain.child i.toUInt32).toOption.map (·.publicKey)) != some code.key)
  check "an unknown HRP issues nothing" (refusedWith (issue account 0 "bc") .invalidCode)
  -- codes that are refused
  check "wrong HRP" (failsWith (CardCode.decode first.code (some CardCode.signetHRP)) (.wrongHRP "twnc" "wnc"))
  check "bad checksum" (failsWith (CardCode.decode (String.ofList first.code.toList.dropLast ++ "q")) .invalidEncoding)
  check "past BIP173's 90 characters" (match Bech32.decode first.code with | .error .tooLong => true | _ => false)
  let payload := (SegwitAddress.convertBits (code.key ++ code.seed).toList 8 5 true).toOption.getD []
  let enc (hrp : String) (data : List UInt8) (e : Bech32Encoding) := (Bech32.encode hrp data e CardCode.maxLength).toOption.getD ""
  check "the test encoder writes the vector's code" (enc "wnc" (0 :: payload) .bech32m == first.code)
  check "bech32 refused" (failsWith (CardCode.decode (enc "wnc" (0 :: payload) .bech32)) .invalidEncoding)
  check "version 1 refused" (failsWith (CardCode.decode (enc "wnc" (1 :: payload) .bech32m)) (.unsupportedVersion 1))
  check "no version at all" (failsWith (CardCode.decode (enc "wnc" [] .bech32m)) .invalidEncoding)
  check "a silent payment HRP" (failsWith (CardCode.decode (enc "sp" (0 :: payload) .bech32m)) (.unknownHRP "sp"))
  check "an address HRP" (failsWith (CardCode.decode (enc "bc" (0 :: payload) .bech32m)) (.unknownHRP "bc"))
  let sized (bytes : ByteArray) := (SegwitAddress.convertBits bytes.toList 8 5 true).toOption.getD []
  check "64 bytes refused"
    (failsWith (CardCode.decode (enc "wnc" (0 :: sized ((code.key ++ code.seed).extract 0 64)) .bech32m)) (.invalidDataLength 64))
  check "66 bytes refused"
    (failsWith (CardCode.decode (enc "wnc" (0 :: sized (code.key ++ code.seed ++ ByteArray.mk #[0])) .bech32m)) (.invalidDataLength 66))
  check "a code with a key off the curve"
    (failsWith (CardCode.decode (enc "wnc" (0 :: sized (offCurve ++ code.seed)) .bech32m)) .invalidPublicKey)
  check "an uncompressed key's tag"
    (failsWith (CardCode.decode (enc "wnc" (0 :: sized (ByteArray.mk #[0x04] ++ code.key.extract 1 33 ++ code.seed)) .bech32m)) .invalidPublicKey)
  check "mixed case" (failsWith (CardCode.decode ("wnc1QQ" ++ String.ofList (first.code.toList.drop 6))) .invalidEncoding)
  check "longer than the bound"
    (failsWith (CardCode.decode (enc "wnc" (0 :: sized (ByteArray.mk (Array.replicate 700 0))) .bech32m ++ "q")) .invalidEncoding)
  check "a made code needs a card HRP" (failsWith (CardCode.make code.key code.seed "tsp") (.unknownHRP "tsp"))
  check "a made code needs a 32-byte seed" (failsWith (CardCode.make code.key (code.seed.extract 0 31) "wnc") (.invalidDataLength 64))
  check "shape: not a silent payment code" (!CardCode.looksLikeCode "sp1qqexample")
  check "shape: not an address" (!CardCode.looksLikeCode "bc1pexample" && !CardCode.looksLikeCode "tb1qexample")
  check "shape: rwnc1 and twnc1" (CardCode.looksLikeCode "rwnc1qexample" && CardCode.looksLikeCode "TWNC1QEXAMPLE")
