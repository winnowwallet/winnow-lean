import SecpCt.Schnorr
import SecpCt.Ecdsa
import Secp.Ecdsa
import TestKit.Check
import TestKit.SecpAnswers
import Winnow.Keys.Secp256k1

/-! # The constant-time signing code against the reference

`SecpCt` is held to `Secp`, whose definitions are the ones its proofs are about: the same public key for the
same secret, and the same signature, byte for byte, for the same key, message and randomness. BIP 340 signing
is a function, so there is exactly one right answer to compare with.

ECDSA is held the same way to the reference in `Secp/Ecdsa.lean`, and every signature is put to the verifier
and through DER and back. The verifier, the DER writer and the DER reader are held to a signature OpenSSL
made, so that they are not only checked against code written beside them.

Before any of that, every curve operation the wallet uses is held to `Vectors/secp-known-answers.json`: answers
computed by `scripts/secp-vectors` with none of the wallet's code (`TestKit/SecpAnswers.lean`).

The proofs say all of this for every input (`SecpCt/Gate.lean`); this runs the compiled code, which the
proofs do not reach, on the inputs tried. Inputs are a fixed stream of pseudo-random bytes, the same on every
run, plus the keys at the edges. `secpct-test N` tries N keys (200 without it; CI runs 2000). -/

open SecpCt

def hex (b : ByteArray) : String :=
  b.foldl (fun s x => s ++ String.ofList [Nat.digitChar (x.toNat / 16), Nat.digitChar (x.toNat % 16)]) ""

/-- The next 32 bytes of the stream, and the stream's next state. -/
def next32 (state : UInt64) : ByteArray × UInt64 := Id.run do
  let mut s := state
  let mut out := ByteArray.emptyWithCapacity 32
  for _ in [0:4] do
    s := s ^^^ (s <<< 13)
    s := s ^^^ (s >>> 7)
    s := s ^^^ (s <<< 17)
    out := pushWord out s
  return (out, s)

def toBytes32 (n : Nat) : ByteArray := Secp.toBE32 n

/-- Whether the verifier said yes; an error counts as neither yes nor no. -/
def accepts (r : Secp.R Bool) : Bool := match r with | .ok true => true | _ => false
def rejects (r : Secp.R Bool) : Bool := match r with | .ok false => true | _ => false

def unhex (s : String) : ByteArray := (Secp.ofHex? s).getD ByteArray.empty

/-- The 33-byte public key for a secret key, from the constant-time code. -/
def compressedOf (secret : ByteArray) : Option ByteArray :=
  (publicKey secret).map fun (x, odd) => ByteArray.mk #[if odd == 1 then 3 else 2] ++ x

def fromBytes (b : ByteArray) : Nat := b.foldl (fun acc x => acc * 256 + x.toNat) 0

/-- The curve the wallet runs today, as the known answers see it. -/
def walletCurve : TestKit.SecpAnswers.Curve :=
  let point (b : ByteArray) : Option Winnow.Keys.Point :=
    if b.size == 33 then (Winnow.Keys.parsePublicKey b (compressed := true)).toOption
    else if b.size == 65 then (Winnow.Keys.parsePublicKey b (compressed := false)).toOption else none
  { publicKey := fun secret => (Winnow.Keys.publicKeyOf secret).toOption
    liftX := fun x => if x.size == 32 then (Secp.liftX? (Secp.fromBE x)).map (fun q => Secp.toBE32 q.2.toNat) else none
    parse := fun b => (point b).map fun q => (Secp.toBE32 q.1.toNat, Secp.toBE32 q.2.toNat)
    pointAdd := fun p t => do
      let q ← point p
      (Winnow.Keys.publicAdd q t).toOption.map Winnow.Keys.serializeCompressed
    xonlyAdd := fun x t => (Winnow.Keys.xonlyAdd x t).toOption
    pointMul := fun p t => do
      let q ← point p
      (Winnow.Keys.publicMultiply q t).toOption.map Winnow.Keys.serializeCompressed
    combine := fun points => do
      let qs ← points.toList.mapM point
      (Winnow.Keys.combine qs).toOption.map Winnow.Keys.serializeCompressed
    secretAdd := fun d t => do
      let secret ← (Winnow.Keys.secretOf d).toOption
      (Winnow.Keys.privateAdd secret t).toOption.map Secp.toBE32
    secretAddXOnly := fun d t => do
      let secret ← (Winnow.Keys.secretOf d).toOption
      (Winnow.Keys.keypairXonlyAdd secret t).toOption.map Secp.toBE32
    bip340Sign := fun d m aux => do
      let secret ← (Winnow.Keys.secretOf d).toOption
      (Winnow.Keys.schnorrSign secret m aux).toOption
    bip340Verify := fun key m signature => (Winnow.Keys.schnorrVerify key m signature).toOption == some true
    ecdsaSign := fun d digest aux => (Secp.Ecdsa.sign digest (Secp.fromBE d) aux).toOption
    ecdsaVerify := fun key digest signature => match Secp.Ecdsa.verify signature digest key with
      | .ok true => true
      | _ => false }

def main (args : List String) : IO UInt32 := TestKit.runMain "secpct-test" do
  TestKit.SecpAnswers.check walletCurve
  let rounds := (args.head?.bind String.toNat?).getD 200
  let check (name : String) (holds : Bool) : IO Unit := TestKit.check name holds
  -- The field and the scalars against plain arithmetic on naturals.
  let mut state : UInt64 := 0x9E3779B97F4A7C15
  for round in [0:rounds * 4] do
    let (a, s1) := next32 state
    let (b, s2) := next32 s1
    state := s2
    let (x, y) := (fromBytes a % Secp.P, fromBytes b % Secp.P)
    let (fa, fb) := (Fe.ofBytes a, Fe.ofBytes b)
    check s!"field multiply {round}" (fromBytes (Fe.mul fa fb).bytes == x * y % Secp.P)
    check s!"field add {round}" (fromBytes (Fe.add fa fb).bytes == (x + y) % Secp.P)
    check s!"field subtract {round}" (fromBytes (Fe.sub fa fb).bytes == (x + Secp.P - y) % Secp.P)
    let (u, v) := (fromBytes a % Secp.Spec.N, fromBytes b % Secp.Spec.N)
    let (sa, sb) := (Sc.ofBytes a, Sc.ofBytes b)
    check s!"scalar multiply {round}" (fromBytes (Sc.mul sa sb).bytes == u * v % Secp.Spec.N)
    check s!"scalar add {round}" (fromBytes (Sc.add sa sb).bytes == (u + v) % Secp.Spec.N)
    check s!"scalar negate {round}" (fromBytes (Sc.neg sa).bytes == (Secp.Spec.N - u) % Secp.Spec.N)
  -- The edges of both.
  let edges : List Nat := [0, 1, 2, Secp.P - 1, Secp.P, Secp.P + 1, Secp.Spec.N - 1, Secp.Spec.N, Secp.Spec.N + 1, 2 ^ 256 - 1,
    2 ^ 255, 2 ^ 128, 2 ^ 64 - 1, 2 ^ 192 + 2 ^ 64]
  for x in edges do
    for y in edges do
      let (a, b) := (toBytes32 x, toBytes32 y)
      check s!"field at the edges {x} {y}"
        (fromBytes (Fe.mul (Fe.ofBytes a) (Fe.ofBytes b)).bytes == (x % Secp.P) * (y % Secp.P) % Secp.P &&
         fromBytes (Fe.add (Fe.ofBytes a) (Fe.ofBytes b)).bytes == (x % Secp.P + y % Secp.P) % Secp.P &&
         fromBytes (Fe.sub (Fe.ofBytes a) (Fe.ofBytes b)).bytes == (x % Secp.P + Secp.P - y % Secp.P) % Secp.P)
      check s!"scalars at the edges {x} {y}"
        (fromBytes (Sc.mul (Sc.ofBytes a) (Sc.ofBytes b)).bytes == (x % Secp.Spec.N) * (y % Secp.Spec.N) % Secp.Spec.N &&
         fromBytes (Sc.add (Sc.ofBytes a) (Sc.ofBytes b)).bytes == (x % Secp.Spec.N + y % Secp.Spec.N) % Secp.Spec.N)
  let (a, _) := next32 12345
  check "an inverse multiplies back to one" (fromBytes (Fe.mul (Fe.ofBytes a) (Fe.inv (Fe.ofBytes a))).bytes == 1)
  check "zero has no inverse and gets zero" (fromBytes (Fe.inv Fe.zero).bytes == 0)
  -- Keys and signatures against the reference.
  let secrets : List ByteArray := [1, 2, 3, Secp.Spec.N - 1, Secp.Spec.N - 2, 2 ^ 255, (Secp.Spec.N + 1) / 2].map toBytes32
  for round in [0:rounds] do
    let (secret, s1) := if h : round < secrets.length then (secrets[round], state) else next32 state
    let (message, s2) := next32 s1
    let (aux, s3) := next32 s2
    state := s3
    let d := fromBytes secret
    if d == 0 || d ≥ Secp.Spec.N then
      check s!"not a key {round}" ((sign secret message aux).isNone && (publicKey secret).isNone)
    else
      match Secp.pubOf d, publicKey secret with
      | .ok (px, py), some (x, odd) =>
        check s!"public key {round}" (x == Secp.toBE32 px.toNat && (odd == 1) == py.isOdd)
      | _, _ => check s!"public key {round} could not be computed" false
      match Secp.sign message d aux, sign secret message aux with
      | .ok reference, some signature =>
        check s!"signature {round} for key {hex secret}" (signature == reference)
      | _, _ => check s!"signature {round} could not be made" false
  check "zero is not a key" ((sign (toBytes32 0) (toBytes32 5) (toBytes32 6)).isNone)
  check "N is not a key" ((sign (toBytes32 Secp.Spec.N) (toBytes32 5) (toBytes32 6)).isNone)
  check "N + 1 is not a key" ((publicKey (toBytes32 (Secp.Spec.N + 1))).isNone)
  check "a key is 32 bytes" ((sign (ByteArray.mk #[1]) (toBytes32 5) (toBytes32 6)).isNone)
  -- A message of another length, which BIP 340 allows.
  let long := ByteArray.mk (Array.replicate 100 0x5a)
  match Secp.sign long 7 (toBytes32 9), sign (toBytes32 7) long (toBytes32 9) with
  | .ok reference, some signature => check "a message of 100 bytes" (signature == reference)
  | _, _ => check "a message of 100 bytes could not be signed" false
  -- ECDSA: the scalars it adds, then signatures against the reference and through the verifier.
  let n := Secp.Spec.N
  state := 0xD1B54A32D192ED03
  for round in [0:rounds] do
    let (a, s1) := next32 state
    state := s1
    let u := fromBytes a % n
    let sa := Sc.ofBytes a
    check s!"scalar inverse {round}" (u == 0 || fromBytes (Sc.mul sa (Sc.inv sa)).bytes == 1)
    check s!"upper half {round}" ((Sc.isHigh sa == 1) == (u > n / 2))
  for x in [0, 1, 2, n / 2 - 1, n / 2, n / 2 + 1, n - 2, n - 1] do
    let sx := Sc.ofBytes (toBytes32 x)
    check s!"upper half at the edges {x}" ((Sc.isHigh sx == 1) == (x > n / 2))
    check s!"inverse at the edges {x}" (fromBytes (Sc.mul sx (Sc.inv sx)).bytes == (if x == 0 then 0 else 1))
    check s!"the reference's inverse at the edges {x}" (x * Secp.Ecdsa.inverse x % n == (if x == 0 then 0 else 1))
  for round in [0:rounds] do
    let (secret, s1) := if h : round < secrets.length then (secrets[round], state) else next32 state
    let (digest, s2) := next32 s1
    let (aux, s3) := next32 s2
    state := s3
    let d := fromBytes secret
    if d == 0 || d ≥ n then
      check s!"ECDSA: not a key {round}" (Ecdsa.sign secret digest aux).isNone
    else
      match (Secp.Ecdsa.signRaw digest d aux).map Secp.Ecdsa.encode, Ecdsa.sign secret digest aux, compressedOf secret with
      | .ok reference, some signature, some key =>
        check s!"ECDSA signature {round} for key {hex secret}" (signature == reference)
        check s!"ECDSA signature {round} verifies" (accepts (Secp.Ecdsa.verify signature digest key))
        check s!"ECDSA signature {round} is what the reference returns once it has checked it"
          ((Secp.Ecdsa.sign digest d aux).toOption == some signature)
        check s!"ECDSA signature {round} reads back from DER"
          (Secp.Ecdsa.parseDer (Secp.Ecdsa.der signature) == some signature)
        check s!"ECDSA signature {round} has s in the lower half" (fromBytes (signature.extract 32 64) ≤ n / 2)
        let other := digest.set! 31 (digest[31]! ^^^ 1)
        check s!"ECDSA signature {round} is of that digest only" (rejects (Secp.Ecdsa.verify signature other key))
        let flipped := toBytes32 (n - fromBytes (signature.extract 32 64))
        check s!"ECDSA signature {round} with s in the upper half is refused"
          (rejects (Secp.Ecdsa.verify (signature.extract 0 32 ++ flipped) digest key))
      | _, _, _ => check s!"ECDSA signature {round} could not be made" false
  check "ECDSA: zero is not a key" ((Ecdsa.sign (toBytes32 0) (toBytes32 5) (toBytes32 6)).isNone)
  check "ECDSA: N is not a key" ((Ecdsa.sign (toBytes32 n) (toBytes32 5) (toBytes32 6)).isNone)
  check "ECDSA: a digest is 32 bytes" ((Ecdsa.sign (toBytes32 7) long (toBytes32 6)).isNone)
  -- A signature OpenSSL made (`openssl pkeyutl -sign` with a secp256k1 key over these 32 bytes), its s already
  -- in the lower half: the verifier takes it, and the DER written here is OpenSSL's, byte for byte.
  let theirKey := unhex "033eb723c033df92fee43f9f0bf562ba2f90ff2be1d78330621ea9558e3f48e21d"
  let theirDigest := unhex "a9b39aa2f942395c700296208d1e67041e6f4bba05a43573d96440f319839f23"
  let theirs := unhex "3caf7674ca36b3c124c490b5e066d5e186ce1a7444ea5916af3dfe4df0c2a81c2810eaf82d3fc578719cc13a678afa152b85d1daa3d8f875a4789a4ee2e43786"
  let theirDer := unhex "304402203caf7674ca36b3c124c490b5e066d5e186ce1a7444ea5916af3dfe4df0c2a81c02202810eaf82d3fc578719cc13a678afa152b85d1daa3d8f875a4789a4ee2e43786"
  check "OpenSSL's signature verifies" (accepts (Secp.Ecdsa.verify theirs theirDigest theirKey))
  check "and not under another key" (rejects (Secp.Ecdsa.verify theirs theirDigest (theirKey.set! 0 2)))
  check "and not with r changed" (rejects (Secp.Ecdsa.verify (theirs.set! 5 0) theirDigest theirKey))
  check "DER as OpenSSL writes it" (Secp.Ecdsa.der theirs == theirDer)
  check "DER as OpenSSL writes it reads back" (Secp.Ecdsa.parseDer theirDer == some theirs)
  check "DER: a byte after the end is refused" ((Secp.Ecdsa.parseDer (theirDer.push 0)).isNone)
  check "DER: a wrong length is refused" ((Secp.Ecdsa.parseDer (theirDer.set! 1 0x45)).isNone)
  check "DER: a negative integer is refused"
    ((Secp.Ecdsa.parseDer (unhex ("3025" ++ "0220" ++ hex (toBytes32 (2 ^ 255)) ++ "020101"))).isNone)
  check "DER: a zero byte in front that is not needed is refused"
    ((Secp.Ecdsa.parseDer (unhex "3009" ++ unhex "0203007f00" ++ unhex "02020080")).isNone)
  check "DER: an integer of no bytes is refused" ((Secp.Ecdsa.parseDer (unhex "3006" ++ unhex "0200" ++ unhex "02020080")).isNone)
  check "DER: a first bit set gets a zero byte in front"
    (Secp.Ecdsa.der (toBytes32 (2 ^ 255) ++ toBytes32 1) == unhex ("3026" ++ "022100" ++ hex (toBytes32 (2 ^ 255)) ++ "020101"))
  check "DER: zero bytes in front are dropped" (Secp.Ecdsa.der (toBytes32 0x7f00 ++ toBytes32 0x80) == unhex "300802027f0002020080")
  check "keys add modulo N" (addKeys (toBytes32 (Secp.Spec.N - 1)) (toBytes32 5) == some (toBytes32 4))
  check "keys that add to zero are refused" ((addKeys (toBytes32 (Secp.Spec.N - 5)) (toBytes32 5)).isNone)
  IO.println s!"secpct-test: {rounds} keys, and BIP 340 and ECDSA signatures, against the references"
