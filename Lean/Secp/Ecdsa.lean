import Secp.Keys

/-! # ECDSA: signing, checking a signature, and writing one down

A SegWit v0 wallet takes ECDSA signatures, not BIP340's. This is ECDSA over the same proven curve, in the
plainest form there is: numbers are `Nat`s, points are `Secp.mulG`, `Secp.mulPt` and `Secp.mulGAdd`, and each
step is one line. For a key `d`, a 32-byte digest `z` and a secret number `k`,

    R = k·G,   r = R's x modulo N,   s = (z + r·d) / k modulo N,

and the signature is `r` and `s`, with `s` replaced by `N − s` if it is in the upper half (Bitcoin relays
only the lower one, BIP146).

`k` is made the way BIP340 makes its own, under tags of this project's: the key, masked by a hash of 32
bytes of fresh randomness, is hashed together with the digest. So `k` is different for every digest, as
ECDSA needs (two signatures with one `k` give the key away), and it does not rest on the randomness being
good: with none at all it is still a function of the key and the digest that nobody without the key can
work out. The tags are not BIP340's, so a key used for both kinds of signature never has one `k` in both.
RFC 6979 is the usual way to do the same; it is not used so that a signer whose work must not depend on its
key (one that hashes a fixed number of times) can make this same signature, byte for byte.

`signRaw` divides by `k` as the power N − 2, which is `1/k` because N is prime. That N is prime is not
proved here, and nothing proved here needs it: `sign` puts every signature to `verify` before returning it,
and `verify` divides another way, by Euclid's algorithm, and checks its own division by multiplying. What
`verify` accepting means on the curve as specified is `Secp.Ecdsa.verify_sound` (`Secp/Proofs/Ecdsa.lean`).

`der` writes the 64 bytes `r`, `s` the way Bitcoin's scripts want a signature (BIP66), and `parseDer` reads
that form and no other.

**Not constant-time**, like the rest of `Secp.Keys` and for the same reasons (see there, and SECURITY.md,
"Timing side channels"). A signer that must hide its key from whoever asks it to sign implements these same
steps on machine words and proves its signatures equal to `signRaw`'s. -/

namespace Secp.Ecdsa

open Secp (fromBE toBE32 Sha256.tagged)
open Secp.Spec (N)

/-! ## Signing -/

/-- What one bit of an exponent does to a running power modulo `m`: square, and multiply if the bit is set. -/
def powerStep (a m : Nat) (acc : Nat) (bit : Bool) : Nat :=
  if bit then acc * acc % m * a % m else acc * acc % m

/-- `k` to the power N − 2, modulo N, by squaring: `1/k` modulo N. -/
def inverse (k : Nat) : Nat :=
  ((List.range 256).reverse.map (fun i => (N - 2).testBit i)).foldl (powerStep k N) 1

/-- The secret number a signature of `digest` under `d` is made with, given 32 bytes `aux` of randomness. -/
def nonce (d : Nat) (digest aux : ByteArray) : Nat :=
  Secp.hashMod (Sha256.tagged "winnow/ecdsa/nonce"
    (Secp.xorBytes (toBE32 d) (Sha256.tagged "winnow/ecdsa/aux" aux) ++ digest))

/-- `s`, or `N − s` if `s` is in the upper half. -/
def lowS (s : Nat) : Nat := if s > N / 2 then N - s else s

/-- The ECDSA signature of a 32-byte `digest` under the key `d`, before the final self-check: `r` and `s`. -/
def signRaw (digest : ByteArray) (d : Nat) (aux : ByteArray) : Secp.R (Nat × Nat) :=
  if d = 0 ∨ d ≥ N then .error .invalidPrivateKey else
  if aux.size ≠ 32 ∨ digest.size ≠ 32 then .error .invalidAuxiliaryRand else
  let k := nonce d digest aux
  if k = 0 then .error .signingFailed else
  match Secp.mulG k with
  | .error e => .error e
  | .ok .inf => .error .signingFailed
  | .ok (.pt rx _) =>
    let r := rx.toNat % N
    if r = 0 then .error .signingFailed else
    let s := inverse k * ((fromBE digest % N + r * d % N) % N) % N
    if s = 0 then .error .signingFailed else
    .ok (r, lowS s)

/-- A signature as 64 bytes: `r` then `s`. -/
def encode (signature : Nat × Nat) : ByteArray := toBE32 signature.1 ++ toBE32 signature.2

/-! ## Checking -/

/-- `1/s` modulo N, or nothing if `s` has none: Euclid's answer, kept only if it multiplies back to one. -/
def inverse? (s : Nat) : Option Nat :=
  let w := Secp.natInv s N % N
  if s * w % N = 1 then some w else none

/-- Whether the 64 bytes `signature` (`r` then `s`) are an ECDSA signature of the 32-byte `digest` under the
33-byte public key `key`, with `s` in the lower half. For a signature `(r, s)`, a digest `z` and a key `Q`:
`w = 1/s` modulo N, the point `(z·w)·G + (r·w)·Q` is a point, and its x modulo N is `r`.

For the digest of all zeros the equation has only `(r·w)·Q` in it, whose x is the same for `Q` and for `−Q`:
a signature of that digest verifies under a key and under its negation alike. That is ECDSA's own, not this
verifier's; no transaction's digest is zero. -/
def verify (signature digest key : ByteArray) : Secp.R Bool :=
  if signature.size ≠ 64 ∨ digest.size ≠ 32 then .ok false else
  match Secp.parseCompressed key with
  | .error _ => .ok false
  | .ok (qx, qy) =>
    let r := fromBE (signature.extract 0 32)
    let s := fromBE (signature.extract 32 64)
    if r = 0 ∨ r ≥ N ∨ s = 0 ∨ s > N / 2 then .ok false else
    match inverse? s with
    | none => .ok false
    | some w =>
      match Secp.mulPt (r * w % N) (.pt qx qy) with
      | .error e => .error e
      | .ok rQ =>
        match Secp.mulGAdd (fromBE digest % N * w % N) rQ with
        | .error e => .error e
        | .ok .inf => .ok false
        | .ok (.pt x _) => .ok (x.toNat % N == r)

/-- ECDSA signing with the auxiliary randomness given: `r` then `s`, 64 bytes, `s` in the lower half. The
signature is verified under the signer's own public key before it is returned. -/
def sign (digest : ByteArray) (d : Nat) (aux : ByteArray) : Secp.R ByteArray :=
  match signRaw digest d aux with
  | .error e => .error e
  | .ok made =>
    match Secp.pubOf d with
    | .error e => .error e
    | .ok (x, y) =>
      match verify (encode made) digest (Secp.compressed x y) with
      | .ok true => .ok (encode made)
      | .ok false => .error .signingFailed
      | .error e => .error e

/-! ## DER (BIP66) -/

/-- A number's 32 bytes as DER writes an integer: the tag, the length, and the number with no zero bytes in
front, but for one put back where the first bit would otherwise read as a minus sign. -/
def derInteger (number : ByteArray) : ByteArray :=
  let digits := number.toList.dropWhile (· == 0)
  let body := match digits with
    | [] => [0]
    | first :: _ => if first ≥ 0x80 then 0 :: digits else digits
  ByteArray.mk (#[0x02, body.length.toUInt8] ++ body.toArray)

/-- The signature `r`, `s` (64 bytes) in DER, as BIP66 lays it down: a sequence of the two integers. At
most 70 bytes, so every length fits in one byte. -/
def der (signature : ByteArray) : ByteArray :=
  let r := derInteger (signature.extract 0 32)
  let s := derInteger (signature.extract 32 64)
  ByteArray.mk #[0x30, (r.size + s.size).toUInt8] ++ r ++ s

/-- One DER integer at `offset`, as BIP66 allows it: the tag, a length of at least one, not negative, no zero
byte in front that the sign does not need, and a value of at most 32 bytes. The value as 32 bytes and the
offset just past it. -/
def parseDerInteger (b : ByteArray) (offset : Nat) : Option (ByteArray × Nat) := do
  guard (offset + 2 ≤ b.size && b[offset]! == 0x02)
  let length := b[offset + 1]!.toNat
  guard (length ≥ 1 && offset + 2 + length ≤ b.size)
  let body := b.extract (offset + 2) (offset + 2 + length)
  guard (body[0]! &&& 0x80 == 0)
  if length > 1 && body[0]! == 0 then guard (body[1]! &&& 0x80 != 0)
  let digits := if body[0]! == 0 then body.extract 1 length else body
  guard (digits.size ≤ 32)
  return (ByteArray.mk (Array.replicate (32 - digits.size) 0) ++ digits, offset + 2 + length)

/-- The 64 bytes `r`, `s` of a signature in DER, read strictly (BIP66): exactly the form `der` writes, and
nothing after it. -/
def parseDer (b : ByteArray) : Option ByteArray := do
  guard (b.size ≥ 8 && b.size ≤ 72 && b[0]! == 0x30 && b[1]!.toNat == b.size - 2)
  let (r, afterR) ← parseDerInteger b 2
  let (s, afterS) ← parseDerInteger b afterR
  guard (afterS == b.size)
  return r ++ s

end Secp.Ecdsa
