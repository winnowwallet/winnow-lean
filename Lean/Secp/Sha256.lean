import Secp.Bytes

/-! # SHA-256 (FIPS 180-4) and the BIP340 tagged hash

A direct transcription over `UInt32`, used by the oracle so that it shares no hash code with the
module under test (which takes SHA-256 from CryptoKit). Trusted and tested, not proven. -/

namespace Secp.Sha256

def K : Array UInt32 := #[
  0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
  0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
  0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
  0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
  0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
  0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
  0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
  0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2]

def H0 : Array UInt32 := #[
  0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19]

@[inline] def rotr (x : UInt32) (n : UInt32) : UInt32 := (x >>> n) ||| (x <<< (32 - n))

def pad (msg : ByteArray) : ByteArray := Id.run do
  let len := msg.size
  let mut b := msg.push 0x80
  while b.size % 64 != 56 do b := b.push 0
  let bits := len * 8
  for i in [0:8] do b := b.push (UInt8.ofNat (bits / 2^(8 * (7 - i))))
  return b

def compress (h : Array UInt32) (blk : ByteArray) (off : Nat) : Array UInt32 := Id.run do
  let mut w : Array UInt32 := Array.replicate 64 0
  for t in [0:16] do
    let i := off + 4 * t
    w := w.set! t ((blk[i]!.toUInt32 <<< 24) ||| (blk[i+1]!.toUInt32 <<< 16) |||
                   (blk[i+2]!.toUInt32 <<< 8) ||| blk[i+3]!.toUInt32)
  for t in [16:64] do
    let s0 := rotr w[t-15]! 7 ^^^ rotr w[t-15]! 18 ^^^ (w[t-15]! >>> 3)
    let s1 := rotr w[t-2]! 17 ^^^ rotr w[t-2]! 19 ^^^ (w[t-2]! >>> 10)
    w := w.set! t (w[t-16]! + s0 + w[t-7]! + s1)
  let mut a := h[0]!; let mut b := h[1]!; let mut c := h[2]!; let mut d := h[3]!
  let mut e := h[4]!; let mut f := h[5]!; let mut g := h[6]!; let mut hh := h[7]!
  for t in [0:64] do
    let S1 := rotr e 6 ^^^ rotr e 11 ^^^ rotr e 25
    let ch := (e &&& f) ^^^ ((~~~ e) &&& g)
    let t1 := hh + S1 + ch + K[t]! + w[t]!
    let S0 := rotr a 2 ^^^ rotr a 13 ^^^ rotr a 22
    let maj := (a &&& b) ^^^ (a &&& c) ^^^ (b &&& c)
    let t2 := S0 + maj
    hh := g; g := f; f := e; e := d + t1; d := c; c := b; b := a; a := t1 + t2
  return #[h[0]! + a, h[1]! + b, h[2]! + c, h[3]! + d, h[4]! + e, h[5]! + f, h[6]! + g, h[7]! + hh]

def hash (msg : ByteArray) : ByteArray := Id.run do
  let p := pad msg
  let mut h := H0
  for i in [0:p.size / 64] do h := compress h p (64 * i)
  let mut out := ByteArray.empty
  for x in h do
    out := out.push (UInt8.ofNat (x >>> 24).toNat) |>.push (UInt8.ofNat ((x >>> 16) &&& 0xff).toNat)
      |>.push (UInt8.ofNat ((x >>> 8) &&& 0xff).toNat) |>.push (UInt8.ofNat (x &&& 0xff).toNat)
  return out

/-- BIP340 `hash_tag(m) = SHA256(SHA256(tag) ‖ SHA256(tag) ‖ m)`. -/
def tagged (tag : String) (msg : ByteArray) : ByteArray :=
  let t := hash tag.toUTF8
  hash (t ++ t ++ msg)

end Secp.Sha256
