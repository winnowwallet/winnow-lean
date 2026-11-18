import Secp.Sha256
import SecpCt.Keys

/-! # Signing (ECDSA), without the key showing in how it is done

A SegWit v0 wallet takes ECDSA signatures, not BIP 340's. The steps are the textbook ones: for a key `d`, a
32-byte digest `z` and a secret number `k`,

    R = k·G,   r = R's x modulo N,   s = (z + r·d) / k modulo N,

and the signature is `r` and `s`, with `s` replaced by `N − s` if it is in the upper half (Bitcoin relays
only the lower one, BIP 146).

What is secret here is the key, `k`, and everything computed from either until the signature itself. All of
it stays in `SecpCt`'s words. The division is a power, `k` to the N − 2, whose squarings and multiplications
are fixed by N and not by `k` (`Sc.inv`); the choice between `s` and `N − s` is made by a mask.

`k` is made the way BIP 340 makes its own, under tags of this project's: the key, masked by a hash of 32
bytes of fresh randomness, is hashed together with the digest. So `k` is different for every digest, as
ECDSA needs (two signatures with one `k` give the key away), and it does not rest on the randomness being
good: with none at all it is still a function of the key and the digest that nobody without the key can
work out. RFC 6979 is the usual way to do the same; it is not used because its loop runs a number of times
that depends on what it hashes.

Whether the 32 bytes given are a key at all, and whether `k`, `r` or `s` came out zero (which does not
happen), are the only questions answered by branching, and only after all the work is done.

`sign` does not check what it made. `signVerified` does: it puts the signature to `verify`, below, which has
nothing to hide and is written plainly.

`Ecdsa.sign_eq` (`SecpCt/EcdsaProofs.lean`): what this returns is what the reference in `Secp/Signing.lean`
returns, byte for byte. -/

namespace SecpCt.Ecdsa

open Secp (Sha256.tagged)

/-- `r` and `s`, 32 bytes each, for a 32-byte `secret`, a 32-byte `digest` and 32 bytes `aux`, and whether
they are a signature: the bytes were a key and none of `k`, `r` and `s` was zero. Does all of its arithmetic
whatever it is given; the inputs must already have the right sizes. This is what is run with the key marked
as unknown to check compiled code under Valgrind. -/
def signRaw (secret digest aux : ByteArray) : ByteArray × UInt64 :=
  let d := Sc.ofBytes secret
  let z := Sc.ofBytes digest
  let t := xor32 d.bytes (Sha256.tagged "winnow/ecdsa/aux" aux)
  let k := Sc.ofBytes (Sha256.tagged "winnow/ecdsa/nonce" (t ++ digest))
  let (rx, _, _) := (Point.mulGenerator k).affine
  -- R's x is below P, which is below 2N: one subtraction of N brings it below N
  let r := Sc.reduceOnce rx.a0 rx.a1 rx.a2 rx.a3 0
  let s0 := Sc.mul (Sc.inv k) (Sc.add z (Sc.mul r d))
  let s := Sc.negIf (Sc.isHigh s0) s0
  (r.bytes ++ s.bytes, Sc.isKey secret &&& (k.isZero ^^^ 1) &&& (r.isZero ^^^ 1) &&& (s.isZero ^^^ 1))

/-- The ECDSA signature of `digest` under `secret`, as `r` then `s`, 64 bytes, with `s` in the lower half
and `aux` as the 32 bytes of fresh randomness. `none` if `secret` is not a key, or the digest or `aux` is
not 32 bytes. -/
def sign (secret digest aux : ByteArray) : Option ByteArray :=
  if secret.size != 32 || digest.size != 32 || aux.size != 32 then none else
  let (signature, ok) := signRaw secret digest aux
  if ok == 1 then some signature else none

/-! ## Checking a signature

Nothing here is secret: a signature, the digest it is for and a public key. For a signature `(r, s)`, a
digest `z` and a public key `Q`:

    w = 1/s modulo N,   the point (z·w)·G + (r·w)·Q is a point, and its x modulo N is r.

`s` must be in the lower half, as Bitcoin relays it (BIP 146). The division is the same power the signing
code divides by (`Sc.inv`), and its answer is kept only if it multiplies back to one, so the check does not
rest on N being prime. What accepting means on the curve as specified is `Ecdsa.verify_sound`
(`SecpCt/KeySpecs.lean`).

For the digest of all zeros the equation has only `(r·w)·Q` in it, whose x is the same for `Q` and for
`−Q`: a signature of that digest verifies under a key and under its negation alike. That is ECDSA's own, not
this verifier's; no transaction's digest is zero. -/

/-- Whether the 64 bytes `signature` (`r` then `s`) are an ECDSA signature of the 32-byte `digest` under the
33-byte public key `key`, with `s` in the lower half. -/
def verify (signature digest key : ByteArray) : Bool :=
  let (rBytes, sBytes) := (signature.extract 0 32, signature.extract 32 64)
  let (r, s) := (Sc.ofBytes rBytes, Sc.ofBytes sBytes)
  let w := Sc.inv s
  signature.size == 64 && digest.size == 32 &&
  -- r and s from 1 to N − 1, s in the lower half, and the division checked
  Sc.isKey rBytes == 1 && Sc.isKey sBytes == 1 && Sc.isHigh s == 0 && Sc.same (Sc.mul s w) Sc.one &&
  ((parseCompressed key).bind fun q =>
    (Point.add (Point.mulPublic (Sc.mul (Sc.ofBytes digest) w) Point.generator)
        (Point.mulPublic (Sc.mul r w) q.point)).toAffine?.filter fun sum =>
      -- the sum's x is below P, which is below 2N: one subtraction of N brings it below N
      Sc.same (Sc.reduceOnce sum.x.a0 sum.x.a1 sum.x.a2 sum.x.a3 0) r).isSome

/-- The signature `sign` makes, checked under the signer's own public key before it is returned. -/
def signVerified (secret digest aux : ByteArray) : Option ByteArray :=
  (sign secret digest aux).filter fun signature =>
    (publicPoint (Sc.ofBytes secret)).any fun key => verify signature digest key.compressed

end SecpCt.Ecdsa
