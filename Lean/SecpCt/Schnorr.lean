import Secp.Sha256
import SecpCt.Point

/-! # Signing (BIP 340), without the key showing in how it is done

The steps are BIP 340's default signing, in the order it gives them. What is secret here is the key, the
number the signature is made with, and everything computed from either until the signature itself; all of it
stays in `SecpCt`'s words, and the two places BIP 340 says "negate if odd" are done by a mask.

Whether the 32 bytes given are a key at all, and whether the number for the signature came out zero (which
does not happen), are the only questions answered by branching, and only after all the work is done.

The hashing is winnow's SHA-256, which works in 32-bit words with no step that depends on what is hashed.

This file signs and gives the public key; it does not verify. The caller checks the signature afterwards
with code that has nothing to hide (winnow's), as BIP 340 recommends. -/

namespace SecpCt

open Secp (Sha256.tagged)

def xor32 (a b : ByteArray) : ByteArray := Id.run do
  let mut out := ByteArray.emptyWithCapacity 32
  for i in [0:32] do
    out := out.push (a[i]! ^^^ b[i]!)
  return out

/-! ## The work, with nothing decided by a secret

Each of these does all of its arithmetic whatever it is given and reports whether the result means anything
as a bit (1 or 0), which the caller looks at afterwards. They are what is run with the key marked as unknown
to check compiled code under Valgrind. The inputs must already have the right sizes. -/

/-- The public key's two coordinates for a 32-byte secret key, and whether the bytes are a key. -/
def publicRaw (secret : ByteArray) : ByteArray × ByteArray × UInt64 :=
  let (x, y, _) := (Point.mulGenerator (Sc.ofBytes secret)).affine
  (x.bytes, y.bytes, Sc.isKey secret)

/-- The BIP 340 signature of `message` under a 32-byte `secret` with 32 bytes `aux`, and whether it is one:
the bytes were a key and the number the signature is made with was not zero. -/
def signRaw (secret message aux : ByteArray) : ByteArray × UInt64 :=
  let d0 := Sc.ofBytes secret
  let (px, py, _) := (Point.mulGenerator d0).affine
  let d := Sc.negIf py.isOdd d0
  let pxBytes := px.bytes
  let t := xor32 d.bytes (Sha256.tagged "BIP0340/aux" aux)
  let k0 := Sc.ofBytes (Sha256.tagged "BIP0340/nonce" (t ++ pxBytes ++ message))
  let (rx, ry, _) := (Point.mulGenerator k0).affine
  let k := Sc.negIf ry.isOdd k0
  let rxBytes := rx.bytes
  let e := Sc.ofBytes (Sha256.tagged "BIP0340/challenge" (rxBytes ++ pxBytes ++ message))
  (rxBytes ++ (Sc.add k (Sc.mul e d)).bytes, Sc.isKey secret &&& (k0.isZero ^^^ 1))

/-- `a + b` modulo N for two 32-byte numbers, and whether the sum is a key (not zero). -/
def addRaw (a b : ByteArray) : ByteArray × UInt64 :=
  let sum := Sc.add (Sc.ofBytes a) (Sc.ofBytes b)
  (sum.bytes, sum.isZero ^^^ 1)

/-! ## The same, as the rest of the signer uses them -/

/-- The public key for a secret key: its x, 32 bytes, and whether its y is odd (1 or 0). `none` if the bytes
are not a key. -/
def publicKey (secret : ByteArray) : Option (ByteArray × UInt64) :=
  if secret.size != 32 then none else
  let (x, y, ok) := publicRaw secret
  if ok == 1 then some (x, y[31]!.toUInt64 &&& 1) else none

/-- The BIP 340 signature of `message` under `secret`, 64 bytes, with `aux` as the 32 bytes of fresh
randomness. `none` if `secret` is not a key or `aux` is not 32 bytes. -/
def sign (secret message aux : ByteArray) : Option ByteArray :=
  if secret.size != 32 || aux.size != 32 then none else
  let (signature, ok) := signRaw secret message aux
  if ok == 1 then some signature else none

/-- `a + b` modulo N for two secret keys as bytes: what deriving one key from another needs. `none` if the
sum is not a key. -/
def addKeys (a b : ByteArray) : Option ByteArray :=
  if a.size != 32 || b.size != 32 then none else
  let (sum, ok) := addRaw a b
  if ok == 1 then some sum else none

end SecpCt
