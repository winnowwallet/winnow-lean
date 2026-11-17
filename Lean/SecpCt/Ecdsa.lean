import Secp.Sha256
import SecpCt.Schnorr

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

This file signs; it does not verify. The caller checks the signature afterwards with code that has nothing
to hide (`Secp.Ecdsa.verify`, `Secp/Ecdsa.lean`).

`Ecdsa.sign_eq` (`SecpCt/EcdsaProofs.lean`): what this returns is what the reference in `Secp/Ecdsa.lean`
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

end SecpCt.Ecdsa
