import Winnow
import Lean.Data.Json

/-! `crypto-test`: AES (FIPS 197) and AES-GCM (SP 800-38D) against published and CryptoKit vectors, and
BIP340 signing against BIP340's own vectors.

* FIPS 197 Appendix C: one block under AES-128, AES-192 and AES-256, and S-box entries.
* `Vectors/wycheproof-aes-gcm.json`: every Wycheproof AES-GCM test (316; source URL and SHA-256 of the
  fetched file inside). Valid tests seal to their ciphertext and tag and open back; invalid ones (modified
  tags and friends) fail to open; nonces under 12 bytes are refused with `incorrectParameterSize`, as
  CryptoKit refuses them.
* `Vectors/cryptokit-aes-gcm.json`: CryptoKit's own output (`AES.GCM.seal` with a given nonce, the
  `combined` layout, long nonces, and the error each refusal raises), written by a scratch Swift program
  over CryptoKit; see that file's `source`.
* `Vectors/bip340-test-vectors.csv`: BIP340's test vectors, byte for byte as published (bitcoin/bips at
  200f9b26fe0a2f235a2af8b30c4be9f12f6bc9cb, `bip-0340/test-vectors.csv`, SHA-256
  34c9d1d9c3a88d524bc80778540dc43f8306ec249a7485293063c376db851c2d). Where a vector has a secret key, the
  x-only key derived from it and the signature `schnorrSign` makes with its `aux_rand` must be the
  vector's exactly, so the nonce derivation is checked, not only that signatures verify (`sign_verifies`
  proves that much). Every vector's verification result must be the vector's. Then one message signed
  twice with `Signer.randomAuxiliaryRand` gives two different signatures that both verify.

Run from `Lean/`. Exits 1 on any failure. -/

open Winnow Winnow.Keys Lean

initialize passed : IO.Ref Nat ← IO.mkRef 0
initialize failures : IO.Ref (Array String) ← IO.mkRef #[]

def check (name : String) (ok : Bool) (detail : String := "") : IO Unit := do
  if ok then passed.modify (· + 1)
  else
    failures.modify (·.push name)
    IO.println s!"FAIL {name}{if detail.isEmpty then "" else ": " ++ detail}"

def field (j : Json) (k : String) : String := (j.getObjValAs? String k).toOption.getD ""
def bytesOf (j : Json) (k : String) : ByteArray := ofHex! (field j k)

def errName {α} (r : Except AESGCM.Error α) : String := match r with | .ok _ => "none" | .error e => e.name

def fips197 : IO Unit := do
  check "S-box: S(00) = 63, S(53) = ed, S(ff) = 16"
    (AES.sbox[0]! == 0x63 && AES.sbox[0x53]! == 0xed && AES.sbox[0xff]! == 0x16)
  let pt := ofHex! "00112233445566778899aabbccddeeff"
  let key := ofHex! "000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f"
  for (size, expected) in [(16, "69c4e0d86a7b0430d8cdb78070b4c55a"), (24, "dda97ca4864cdfe06eaf70a0ec0d7191"),
                           (32, "8ea2b7ca516745bfeafc49904b496089")] do
    let ct := AES.encrypt (key.extract 0 size) pt
    check s!"FIPS 197 C: AES-{size * 8}" ((ct.map hex) == some expected) s!"{ct.map hex}"
  check "AES refuses a 20-byte key" (AES.encrypt (key.extract 0 20) pt).isNone

def wycheproof : IO Unit := do
  let j ← IO.ofExcept (Json.parse (← IO.FS.readFile "Vectors/wycheproof-aes-gcm.json"))
  let tests ← IO.ofExcept (j.getObjValAs? (Array Json) "tests")
  let mut sealed := 0
  let mut opened := 0
  let mut refusedOpen := 0
  let mut shortNonce := 0
  for t in tests do
    let id := (t.getObjValAs? Nat "tcId").toOption.getD 0
    let key := bytesOf t "key"
    let iv := bytesOf t "iv"
    let aad := bytesOf t "aad"
    let msg := bytesOf t "msg"
    let ct := bytesOf t "ct"
    let tag := bytesOf t "tag"
    let valid := field t "result" == "valid"
    let box : AESGCM.SealedBox := { nonce := iv, ciphertext := ct, tag }
    if iv.size < AESGCM.nonceSize then
      -- CryptoKit's `AES.GCM.Nonce` needs at least 12 bytes
      check s!"wycheproof {id}: a {iv.size}-byte nonce is refused"
        (errName (AESGCM.seal key msg iv aad) == "incorrectParameterSize" &&
         errName (AESGCM.open key box aad) == "incorrectParameterSize")
      shortNonce := shortNonce + 1
    else if valid then
      match AESGCM.seal key msg iv aad with
      | .ok b => check s!"wycheproof {id}: seal" (b.ciphertext == ct && b.tag == tag) s!"{hex b.ciphertext} {hex b.tag}"
      | .error e => check s!"wycheproof {id}: seal" false e.name
      check s!"wycheproof {id}: open" (match AESGCM.open key box aad with | .ok m => m == msg | .error _ => false)
      sealed := sealed + 1
      opened := opened + 1
    else
      check s!"wycheproof {id}: refused ({field t "flags"})" (errName (AESGCM.open key box aad) == "authenticationFailure")
        (errName (AESGCM.open key box aad))
      refusedOpen := refusedOpen + 1
  IO.println s!"  wycheproof: {tests.size} tests: {sealed} sealed and opened, {refusedOpen} refused, {shortNonce} short nonces refused"

def cryptokit : IO Unit := do
  let j ← IO.ofExcept (Json.parse (← IO.FS.readFile "Vectors/cryptokit-aes-gcm.json"))
  let cases ← IO.ofExcept (j.getObjValAs? (Array Json) "cases")
  for (c, i) in cases.zipIdx do
    let key := bytesOf c "key"
    let nonce := bytesOf c "nonce"
    let aad := bytesOf c "aad"
    let msg := bytesOf c "msg"
    let combined := bytesOf c "combined"
    let label := s!"cryptokit {i} (AES-{key.size * 8}, {aad.size} aad, {msg.size} bytes)"
    check s!"{label}: seal gives CryptoKit's combined box"
      (match AESGCM.seal key msg nonce aad with | .ok b => b.combined == some combined | .error _ => false)
    check s!"{label}: open" (match AESGCM.openCombined key combined aad with | .ok m => m == msg | .error _ => false)
  let long ← IO.ofExcept (j.getObjValAs? (Array Json) "longNonces")
  for c in long do
    let nonce := bytesOf c "nonce"
    let r := AESGCM.seal (bytesOf c "key") (bytesOf c "msg") nonce (bytesOf c "aad")
    check s!"cryptokit: a {nonce.size}-byte nonce seals as CryptoKit, with no combined form"
      (match r with
       | .ok b => b.ciphertext == bytesOf c "ciphertext" && b.tag == bytesOf c "tag" && b.combined.isNone
       | .error _ => false)
  let refusals ← IO.ofExcept (j.getObjValAs? (Array Json) "refusals")
  for c in refusals do
    let got := errName (AESGCM.openCombined (bytesOf c "key") (bytesOf c "combined") (bytesOf c "aad"))
    check s!"cryptokit refusal: {field c "case"} is {field c "error"}" (got == field c "error") got
  let nonceErrors ← IO.ofExcept (j.getObjVal? "nonceErrors")
  let key := ByteArray.mk (Array.replicate 32 1)
  check "cryptokit: an 8-byte nonce is incorrectParameterSize"
    (errName (AESGCM.seal key .empty (ByteArray.mk (Array.replicate 8 0))) == field nonceErrors "8 bytes")
  check "cryptokit: a 16-byte nonce is accepted"
    (errName (AESGCM.seal key .empty (ByteArray.mk (Array.replicate 16 0))) == field nonceErrors "16 bytes")
  let keyErrors ← IO.ofExcept (j.getObjVal? "keyErrors")
  check "cryptokit: a 20-byte key is incorrectKeySize"
    (errName (AESGCM.seal (ByteArray.mk (Array.replicate 20 1)) .empty (ByteArray.mk (Array.replicate 12 0))) ==
      field keyErrors "20 bytes")

def bip340 : IO Unit := do
  let rows := ((← IO.FS.readFile "Vectors/bip340-test-vectors.csv").splitOn "\n").drop 1
    |>.map (·.replace "\r" "") |>.filter (!·.isEmpty)
  check "bip340: 19 vectors" (rows.length == 19) s!"{rows.length}"
  for row in rows do
    match row.splitOn "," with
    | i :: sk :: pk :: aux :: msg :: sig :: result :: _ =>
      let hx (h : String) := ofHex! h.toLower
      if !sk.isEmpty then
        match secretOf (hx sk) with
        | .error e => check s!"bip340 {i}: secret key" false e.name
        | .ok d =>
          check s!"bip340 {i}: x-only key" (match pointOfSecret d with
            | .ok p => xonlyBytes p == hx pk | .error _ => false)
          let got := schnorrSign d (hx msg) (hx aux)
          check s!"bip340 {i}: signature" (match got with | .ok s => s == hx sig | .error _ => false)
            (match got with | .ok s => hex s | .error e => e.name)
      let ok := (schnorrVerify (hx pk) (hx msg) (hx sig)).toOption.getD false
      check s!"bip340 {i}: verifies {result}" (ok == (result == "TRUE"))
    | _ => check s!"bip340: row {row.take 8}" false "fewer than 7 fields"
  let d := 0xB7E151628AED2A6ABF7158809CF4F3C762E7160F38B4DA56A784D9045190CFEF
  let msg := ofHex! "243f6a8885a308d313198a2e03707344a4093822299f31d0082efa98ec4e6c89"
  let some p := (pointOfSecret d).toOption | check "bip340: fresh aux key" false; return
  match schnorrSign d msg (← Signer.randomAuxiliaryRand), schnorrSign d msg (← Signer.randomAuxiliaryRand) with
  | .ok s1, .ok s2 =>
    check "bip340: fresh auxiliary randomness gives a fresh nonce" (s1.extract 0 32 != s2.extract 0 32)
    check "bip340: both verify" ((schnorrVerify (xonlyBytes p) msg s1).toOption.getD false &&
      (schnorrVerify (xonlyBytes p) msg s2).toOption.getD false)
  | _, _ => check "bip340: signing with fresh auxiliary randomness" false

def roundTrips : IO Unit := do
  let key ← IO.getRandomBytes 32
  let msg ← IO.getRandomBytes 1_048_576
  let start ← IO.monoMsNow
  let r ← AESGCM.sealRandom key msg "context".toUTF8
  let sealedAt ← IO.monoMsNow
  match r with
  | .error e => check "1 MiB round trip" false e.name
  | .ok box =>
    let some combined := box.combined | check "1 MiB round trip" false "no combined form"; return
    let back := AESGCM.openCombined key combined "context".toUTF8
    let openedAt ← IO.monoMsNow
    check "1 MiB round trip under a random nonce" (match back with | .ok m => m == msg | .error _ => false)
      s!"seal {sealedAt - start} ms, open {openedAt - sealedAt} ms"
    IO.println s!"  1 MiB: seal {sealedAt - start} ms, open {openedAt - sealedAt} ms"
    check "a random nonce is 12 bytes and fresh" (box.nonce.size == 12 &&
      (match ← AESGCM.sealRandom key msg with | .ok b => b.nonce != box.nonce | .error _ => false))
  check "constant-time compare" (AESGCM.constantTimeEqual "abc".toUTF8 "abc".toUTF8 &&
    !AESGCM.constantTimeEqual "abc".toUTF8 "abd".toUTF8 && !AESGCM.constantTimeEqual "abc".toUTF8 "ab".toUTF8)

def main : IO UInt32 := do
  fips197
  wycheproof
  cryptokit
  bip340
  roundTrips
  let f ← failures.get
  IO.println s!"crypto-test: {← passed.get} passed, {f.size} failed"
  return if f.isEmpty then 0 else 1
