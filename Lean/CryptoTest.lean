import Winnow
import Lean.Data.Json
import TestKit.Check

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
* `Vectors/bip32-test-vectors.json`: BIP32's test vectors, written by `scripts/bip32-vectors`.
* `Vectors/bip340-test-vectors.csv`: BIP340's test vectors, byte for byte as published (bitcoin/bips at
  200f9b26fe0a2f235a2af8b30c4be9f12f6bc9cb, `bip-0340/test-vectors.csv`, SHA-256
  34c9d1d9c3a88d524bc80778540dc43f8306ec249a7485293063c376db851c2d). Where a vector has a secret key, the
  x-only key derived from it and the signature `schnorrSign` makes with its `aux_rand` must be the
  vector's exactly, so the nonce derivation is checked, not only that signatures verify (`sign_verifies`
  proves that much). Every vector's verification result must be the vector's. Then one message signed
  twice with `Signer.randomAuxiliaryRand` gives two different signatures that both verify.
* `Vectors/swift-utf8-decoding.json`: what Swift's `String(decoding:as: UTF8.self)` makes of well-formed text,
  truncated sequences, overlongs, surrogates, code points past U+10FFFF, lone continuation bytes and seeded
  runs of high bytes, written by `scripts/swift-utf8-vectors`. `Text.decodeUTF8Lossy` must give Swift's
  scalars for every vector (one U+FFFD per maximal subpart), and so must `ByteReader.readVarString`, the
  version message's user agent, which reads through it.
* `Vectors/mainnet-retargets.json`: the headers either side of every mainnet retarget, written by
  `scripts/mainnet-retarget-vectors`. `HeaderChain.expectedBits` must give each one's real bits, and
  `requireDifficulty` must take them and refuse others. Core's `pow_tests.cpp` and `arith_uint256_tests.cpp` cover
  what mainnet never did: the 4× easier clamp and a negative timespan. `requireBoundedAdjustment` is held to 4×
  easier and to powLimit, either side of each.
* The fast curve (`Secp.Fast`), which compiled code runs in place of the proved scalar multiplication,
  lift_x and point addition (`@[implemented_by]`): each `…Fast` function against the proved code it stands in
  for (`Secp.smul?`, `smulJ`, `Fq.sqrt?`), over edge scalars, seeded random ones and the points they give.
  The BIP340 vectors above already run through it.

Run from `Lean/`. Exits 1 on any failure. -/

open Winnow Winnow.Keys Lean TestKit

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

/-! ## The fast curve against the proved one -/

def utf8 : IO Unit := do
  let j ← IO.ofExcept (Json.parse (← IO.FS.readFile "Vectors/swift-utf8-decoding.json"))
  let vectors ← IO.ofExcept (j.getObjValAs? (Array Json) "vectors")
  let mut wire := 0
  for v in vectors do
    let name := field v "name"
    let b := bytesOf v "bytes"
    let want ← IO.ofExcept (v.getObjValAs? (List Nat) "scalars")
    let got := (Text.decodeUTF8Lossy b).toList.map Char.toNat
    check s!"utf8: {name}" (got == want) s!"{got} for Swift's {want}"
    if b.size ≤ 1_000 then
      let read := (ByteReader.M.runAll ByteReader.readVarString (varBytes b)).toOption.map (·.toList.map Char.toNat)
      check s!"utf8: {name}, read as a var string" (read == some want) s!"{read}"
      wire := wire + 1
  IO.println s!"  utf8: {vectors.size} vectors from Swift, {wire} also read off the wire"

section FastCurve
open Secp

def pointText : APoint → String
  | .inf => "infinity"
  | .pt x y => s!"({x.toNat}, {y.toNat})"

def resultText {ε} : Except ε APoint → String
  | .ok p => pointText p
  | .error _ => "error"

def optionText : Keys.PK (Option Keys.Point) → String
  | .ok (some (x, y)) => s!"({x.toNat}, {y.toNat})"
  | .ok none => "infinity"
  | .error _ => "error"

def liftedText : Option (Fq × Fq) → String
  | some (x, y) => s!"({x.toNat}, {y.toNat})"
  | none => "none"

/-- The proved `lift_x` (`Secp.liftX?`'s body: compiled code runs `liftXFast?` for the name itself). -/
def provedLiftX? (x : Nat) : Option (Fq × Fq) :=
  if x < P then
    let fx := Fq.ofNat x
    match (fx * fx * fx + 7).sqrt? with
    | some y => some (fx, if y.isOdd then -y else y)
    | none => none
  else none

def fastCurve : IO Unit := do
  let n := Secp.Spec.N
  -- edges, then seeded random scalars (an LCG, so a failure names a scalar that reproduces it)
  let mut ks : Array Nat := #[0, 1, 2, 3, 15, 16, 17, 255, 256, n - 2, n - 1, n, n + 1, n / 2, 2^128 + 1, 2^255,
    2^256 - 1]
  let mut seed := 0x243F6A8885A308D313198A2E03707344A4093822299F31D0082EFA98EC4E6C89
  for _ in [0:60] do
    seed := (seed * 6364136223846793005 + 1442695040888963407) % 2^256
    ks := ks.push seed
  let points : Array APoint := (ks.extract 1 9).filterMap (smul? · Secp.Gpt) |>.push .inf
  let mut bad : Array String := #[]
  for k in ks do
    let proved := match smul? k Secp.Gpt with | some q => pointText q | none => "error"
    if resultText (Secp.mulGFast k) != proved then bad := bad.push s!"mulG {k}"
    let provedGen := optionText (Keys.affine (smulJ k Secp.Gpt))
    if optionText (Keys.mulGenFast k) != provedGen then bad := bad.push s!"mulGen {k}"
  for h : i in [0:ks.size] do
    let k := ks[i]
    let pt := points[i % points.size]?.getD .inf
    let provedPt := match smul? k pt with | some q => pointText q | none => "error"
    if resultText (Secp.mulPtFast k pt) != provedPt then bad := bad.push s!"mulPt {k} {pointText pt}"
    let provedAdd := match ((smulJ k Secp.Gpt).add pt).toAffine? with | some q => pointText q | none => "error"
    if resultText (Secp.mulGAddFast k pt) != provedAdd then bad := bad.push s!"mulGAdd {k} {pointText pt}"
    if let .pt x y := pt then
      let provedMul := optionText (Keys.affine (smulJ k (.pt x y)))
      if k % n != 0 && optionText (Keys.mulOptFast k (x, y)) != provedMul then bad := bad.push s!"mulOpt {k}"
      for other in [points[(i + 1) % points.size]?.getD .inf, .inf, .pt x (-y), pt] do
        let b : Option Keys.Point := match other with | .pt u v => some (u, v) | .inf => none
        let provedSum := optionText (Keys.affine ((Jac.inf.add (.pt x y)).add (Keys.toA b)))
        if optionText (Keys.addOptFast (some (x, y)) b) != provedSum then
          bad := bad.push s!"addOpt {pointText pt} {pointText other}"
  -- lift_x: every point's x, x + 1 (often not on the curve), 0, P - 1 and values past P
  let xs := points.toList.filterMap (fun | .pt x _ => some x.toNat | .inf => none)
  let edges : List Nat := [0, 1, Secp.P - 1, Secp.P, Secp.P + 1, 2^256 - 1]
  for x in xs ++ xs.map (· + 1) ++ edges do
    if liftedText (Secp.liftXFast? x) != liftedText (provedLiftX? x) then bad := bad.push s!"liftX {x}"
  check "the fast curve agrees with the proved one" bad.isEmpty s!"{bad.size} disagreements, first {bad[0]?}"
  IO.println s!"  fast curve: {ks.size} scalars, {points.size} points, {bad.size} disagreements"

end FastCurve

/-- `Text.parseJson`'s bound: what the wallet reads still parses, the exponents that stop it do not (SEC-040), and
a string that looks like one is only a string. -/
def jsonExponents : IO Unit := do
  let took (t : String) := (Winnow.Text.parseJson t).toBool
  check "json: a Double's exponents parse" (took "[1e308,1e-320,2.5E+3,0]")
  check "json: the bound itself parses" (took "1e400" && took "1e-400")
  check "json: past the bound, refused" (!took "1e401" && !took "1E-401" && !took "1e+99999999" && !took "{\"a\":1e-99999999}")
  check "json: inside a string it is text" (took "{\"a\":\"1e99999999\"}")
  check "json: after an escaped quote it is still text" (took "[\"\\\"1e99999999\"]")
  check "json: the next value after a string is a number again" (!took "[\"a\",1e99999999]")

/-! ## Difficulty retargeting: mainnet's own retargets and Core's cases -/

section Retargets
open Winnow.Net Winnow.Net.NetworkParams

/-- A header of which the retarget rules read only the time and bits. -/
def timedHeader (time bits : UInt32) : BlockHeader :=
  .mk' 1 (ByteArray.mk (Array.replicate 32 0)) (ByteArray.mk (Array.replicate 32 0)) time bits 0

def expectedIs (r : Except HeaderChainError (Option UInt32)) (want : UInt32) : Bool :=
  match r with | .ok (some bits) => bits == want | _ => false

def showExpected (r : Except HeaderChainError (Option UInt32)) : String :=
  match r with | .ok b => s!"{b.map (·.toNat)}" | .error e => e.name

def refusedAs (kind : String) (r : Except HeaderChainError Unit) : Bool :=
  match r with | .ok () => false | .error e => e.name == kind

/-- `requireDifficulty` for `h` at `height` on a chain held from `baseHeight`, with `first` at the period's
first height and `last` below `h`. Any other height is a header no retarget could come from, so reading the
wrong one shows. -/
def difficultyOn (h first last : BlockHeader) (height baseHeight : UInt32) : Except HeaderChainError Unit :=
  HeaderChain.requireDifficulty h height baseHeight mainnet fun i =>
    let at_ := baseHeight + i.toUInt32
    if at_ == height - 1 then last
    else if at_ + 2_016 == height then first
    else timedHeader 0 0x1d00ffff

/-- Core's `pow_tests.cpp`: (case, height, period's first time, last time, last bits, the next bits). -/
def corePowTests : List (String × UInt32 × UInt32 × UInt32 × UInt32 × UInt32) := [
  ("no constraint applies", 32_256, 1_261_130_161, 1_262_152_739, 0x1d00ffff, 0x1d00d86a),
  ("capped at powLimit", 2_016, 1_231_006_505, 1_233_061_996, 0x1d00ffff, 0x1d00ffff),
  ("the 4× harder clamp", 68_544, 1_279_008_237, 1_279_297_671, 0x1c05a3f4, 0x1c0168fd),
  ("the 4× harder clamp rounds down", 68_544, 1_279_297_671 - 302_400, 1_279_297_671, 0x1c05a3f5, 0x1c0168fd),
  ("a negative timespan takes the 4× harder clamp", 68_544, 1_279_297_671, 1_279_008_237, 0x1c05a3f4, 0x1c0168fd),
  ("the 4× easier clamp, on a built time", 46_368, 1_263_163_443, 1_269_211_443, 0x1c387f6f, 0x1d00e1fd),
  ("the window starts at its first block's time", 4_032, 1_269_211_443 + 2_016 * 600, 1_269_211_443 + 4_031 * 600,
    0x1c05a3f4, 0x1c05a33c)]

/-- Core's `arith_uint256_tests.cpp`: (bits, the target it reads as, that target's own bits). -/
def coreCompact : List (UInt32 × Nat × UInt32) := [
  (0x01123456, 0x12, 0x01120000), (0x02123456, 0x1234, 0x02123400), (0x03123456, 0x123456, 0x03123456),
  (0x04123456, 0x12345600, 0x04123456), (0x05009234, 0x92340000, 0x05009234),
  (0x20123456, 0x123456 * 2 ^ 232, 0x20123456), (0x1d00ffff, 0xffff * 2 ^ 208, 0x1d00ffff)]

def retargetRules : IO Unit := do
  for (name, p) in [("mainnet", mainnet), ("signet", signet), ("regtest", regtest)] do
    check s!"params: {name} are well formed" p.valid
  check "params: signet's magic comes from its challenge" (signet.magic == signetMagic signetChallenge)
  for (name, height, firstTime, lastTime, lastBits, want) in corePowTests do
    let r := HeaderChain.expectedBits height (timedHeader lastTime lastBits) (some (timedHeader firstTime 0)) mainnet
    check s!"retarget: {name}" (expectedIs r want) (showExpected r)
  for (bits, value, canonical) in coreCompact do
    check s!"compact: {bits.toNat} reads as {value}" (UInt256.target bits == some ⟨value⟩)
    check s!"compact: {value} writes as {canonical.toNat}" ((UInt256.mk value).compact == canonical)
  -- the mantissa's top bit means negative, so a target whose top byte has it takes one more byte
  check "compact: 0x80 takes the extra byte" ((UInt256.mk 0x80).compact == 0x02008000)
  check "compact: 0xFFFF takes the extra byte" ((UInt256.mk 0xffff).compact == 0x0300ffff)
  check "compact: the top of 256 bits takes the extra byte" (UInt256.max.compact == 0x2100ffff)
  check "compact: zero" (UInt256.zero.compact == 0)
  check "bitWidth: at the byte edges" ([0, 1, 0xff, 0x100, 2 ^ 255].map (fun v => (UInt256.mk v).bitWidth) == [0, 1, 8, 9, 256])
  check "multiplied wraps at 256 bits" ((UInt256.mk (2 ^ 255)).multiplied 3 == UInt256.mk (2 ^ 255))
  -- negative, zero and overflowing bits, which `targetAndWork` refuses as Core's CheckProofOfWork does
  for bits in [0, 0x00123456, 0x01003456, 0x02000056, 0x03000000, 0x04000000, 0x00923456, 0x01803456, 0x02800056,
               0x03800000, 0x04800000, 0x01fedcba, 0x04923456, 0xff123456] do
    check s!"target: {bits} is no target"
      (refusedAs "invalidTarget" ((HeaderChain.targetAndWork (UInt32.ofNat bits) mainnet 1).map fun _ => ()))
  -- between retargets the bits may not change
  let last := timedHeader 1_300_000_000 0x1c05a3f4
  check "difficulty: unchanged between retargets" (difficultyOn last last last 2_017 0 |>.isOk)
  check "difficulty: refused between retargets, one easier"
    (refusedAs "unexpectedDifficulty" (difficultyOn (timedHeader 0 0x1c05a3f5) last last 2_017 0))
  check "difficulty: refused between retargets, one harder"
    (refusedAs "unexpectedDifficulty" (difficultyOn (timedHeader 0 0x1c05a3f3) last last 2_017 0))
  -- the first retarget after a mid-period checkpoint: at most 4× easier, never past powLimit
  let bounded (bits previous : UInt32) :=
    HeaderChain.requireBoundedAdjustment (timedHeader 0 bits) (timedHeader 0 previous) mainnet 2_016
  check "bounded: exactly 4× easier" (bounded 0x1b10132c 0x1b0404cb |>.isOk)
  check "bounded: refused just past 4×" (refusedAs "unexpectedDifficulty" (bounded 0x1b10132d 0x1b0404cb))
  check "bounded: harder is not its business" (bounded 0x1b000001 0x1b0404cb |>.isOk)
  check "bounded: powLimit, where 4× reaches past it" (bounded 0x1d00ffff 0x1d00d86a |>.isOk)
  check "bounded: refused just past powLimit" (refusedAs "unexpectedDifficulty" (bounded 0x1d010000 0x1d00d86a))
  check "bounded: refused unreadable bits" (refusedAs "invalidTarget" (bounded 0x1d80ffff 0x1d00ffff))
  check "bounded: refused unreadable previous bits" (refusedAs "invalidTarget" (bounded 0x1d00ffff 0x1d80ffff))
  let unreadable := HeaderChain.expectedBits 2_016 (timedHeader 0 0x1d80ffff) (some (timedHeader 0 0)) mainnet
  check "retarget: refused when the last bits are unreadable"
    (refusedAs "invalidTarget" (unreadable.map fun _ => ()))

/-- Every retarget mainnet has had. The headers carry their proof of work, so the table can't be wrong without
that showing: each row's two headers must link and meet their own bits, and the period's first header is the
row before's `next`, which pins the windows together. -/
def mainnetRetargets : IO Unit := do
  let j ← IO.ofExcept (Json.parse (← IO.FS.readFile "Vectors/mainnet-retargets.json"))
  let rows ← IO.ofExcept (j.getObjValAs? (Array Json) "boundaries")
  let header (row : Json) (key : String) : IO BlockHeader :=
    match BlockHeader.decode (bytesOf row key) with
    | .ok h => pure h
    | .error _ => throw (IO.userError s!"retarget: {key} of {row.compress} is no header")
  let powLimit := UInt256.ofLittleEndian mainnet.powLimit
  let timespan : Int := mainnet.powTargetTimespan.toNat
  let mut first := HeaderChain.genesisHeader mainnet
  let mut changed := 0
  let mut capped : Array Nat := #[]
  let mut harder : Array Nat := #[]
  let mut easier : Array Nat := #[]
  for row in rows do
    let height ← IO.ofExcept (row.getObjValAs? Nat "height")
    let last ← header row "last"
    let next ← header row "next"
    let h := height.toUInt32
    check s!"mainnet {height}: the headers are real"
      (next.previousHash == last.hash && (HeaderChain.checkedWork last mainnet (h - 1)).isOk &&
       (HeaderChain.checkedWork next mainnet h).isOk)
    let r := HeaderChain.expectedBits h last (some first) mainnet
    check s!"mainnet {height}: the bits" (expectedIs r next.bits) (showExpected r)
    check s!"mainnet {height}: the bits round trip"
      ((UInt256.target next.bits).map (·.compact) == some next.bits)
    check s!"mainnet {height}: accepted from the period's first header" (difficultyOn next first last h (h - 2_016) |>.isOk)
    check s!"mainnet {height}: refused with other bits"
      (refusedAs "unexpectedDifficulty" (difficultyOn { next with bits := next.bits + 1 } first last h (h - 2_016)))
    check s!"mainnet {height}: accepted from a checkpoint inside the period"
      (difficultyOn next first last h (h - 2_015) |>.isOk)
    let raw : Int := (last.time.toNat : Int) - (first.time.toNat : Int)
    if next.bits != last.bits then changed := changed + 1
    if raw < timespan / 4 then harder := harder.push height
    if raw > timespan * 4 then easier := easier.push height
    if last.bits == powLimit.compact && raw > timespan then capped := capped.push height
    first := next
  let heights := rows.filterMap fun r => (r.getObjValAs? Nat "height").toOption
  check "mainnet: every period, in order"
    (heights == (Array.range heights.size).map fun i => (i + 1) * 2_016)
  check "mainnet: reaches the shipped checkpoint" (heights.contains 959_616)
  let checkpoint := rows.find? fun r => (r.getObjValAs? Nat "height").toOption == some 959_616
  check "mainnet: the shipped checkpoint is that header"
    ((checkpoint.map (bytesOf · "next")) == mainnet.checkpoint.map (·.header))
  check "mainnet: block 2016 is capped at powLimit" (capped[0]? == some 2_016)
  check "mainnet: block 32256 is the first change"
    ((rows.find? fun r => ((bytesOf r "last").extract 72 76) != ((bytesOf r "next").extract 72 76)).bind
      (fun r => (r.getObjValAs? Nat "height").toOption) == some 32_256)
  check "mainnet: block 68544 hits the 4× harder clamp" (harder.contains 68_544)
  IO.println s!"  retarget: {rows.size} mainnet periods, {changed} changed the bits, {capped.size} capped at powLimit, {harder.size} at the harder clamp {harder}, {easier.size} at the easier"

end Retargets

/-- BIP32's own test vectors (`scripts/bip32-vectors`): `ofSeed` and `derived` reach every extended key, private
(through `privateAdd`) and neutered; a neutered parent reaches each unhardened child (through `publicAdd`) and is
refused a hardened one; every key reads back; and vector 5's invalid keys are refused. -/
def bip32 : IO Unit := do
  let j ← IO.ofExcept (Json.parse (← IO.FS.readFile "Vectors/bip32-test-vectors.json"))
  let vectors ← IO.ofExcept (j.getObjValAs? (Array Json) "vectors")
  let invalid ← IO.ofExcept (j.getObjValAs? (Array Json) "invalid")
  let mut publicSteps := 0
  let mut hardenedSteps := 0
  for v in vectors do
    let .ok root := HDKey.ofSeed (bytesOf v "seed") | throw (IO.userError s!"bip32: seed of {v.compress}")
    let mut parent : Option HDKey := none
    for c in ← IO.ofExcept (v.getObjValAs? (Array Json) "chains") do
      let path := field c "path"
      let .ok k := root.derived path | throw (IO.userError s!"bip32: {path} did not derive")
      check s!"bip32 {path}: the private key" (k.serialized == field c "prv") k.serialized
      check s!"bip32 {path}: the public key" (k.neutered.serialized == field c "pub") k.neutered.serialized
      for key in [field c "prv", field c "pub"] do
        check s!"bip32 {path}: {key} reads back"
          (match HDKey.deserialize key with | .ok read => read.serialized == key | .error _ => false)
      if let some p := parent then
        match p.neutered.child k.childIndex with
        | .ok child =>
          publicSteps := publicSteps + 1
          check s!"bip32 {path}: reached from the public parent" (child.serialized == field c "pub") child.serialized
        | .error e =>
          hardenedSteps := hardenedSteps + 1
          check s!"bip32 {path}: hardened, so the public parent is refused"
            (k.childIndex ≥ HDKey.hardenedOffset && e matches .hardenedDerivationFromPublicKey) e.name
      parent := some k
  check "bip32: both kinds of step ran" (publicSteps ≥ 5 && hardenedSteps ≥ 5) s!"{publicSteps}, {hardenedSteps}"
  check "bip32: vector 5 has its keys" (invalid.size ≥ 10) s!"{invalid.size}"
  for row in invalid do
    check s!"bip32 refuses: {field row "why"}" (HDKey.deserialize (field row "key") matches .error _)

def main : IO UInt32 := runMain "crypto-test" do
  fips197
  wycheproof
  cryptokit
  bip340
  fastCurve
  roundTrips
  bip32
  utf8
  jsonExponents
  retargetRules
  mainnetRetargets
