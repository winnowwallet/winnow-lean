import Secp.Bytes

/-! # SHA-256 (FIPS 180-4) and the BIP340 tagged hash

A direct transcription over `UInt32` with proof-checked bounds and unboxed 8-word state. -/

namespace Secp.Sha256

structure State where
  h0 : UInt32
  h1 : UInt32
  h2 : UInt32
  h3 : UInt32
  h4 : UInt32
  h5 : UInt32
  h6 : UInt32
  h7 : UInt32

def K : Vector UInt32 64 := #v[
  0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
  0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
  0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
  0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
  0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
  0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
  0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
  0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2]

def H0 : State :=
  ⟨0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19⟩

@[inline] def rotr (x : UInt32) (n : UInt32) : UInt32 := (x >>> n) ||| (x <<< (32 - n))

def pad (msg : ByteArray) : ByteArray := Id.run do
  let len := msg.size
  let mut b := msg.push 0x80
  while b.size % 64 != 56 do b := b.push 0
  let bits := len * 8
  for i in [0:8] do b := b.push (UInt8.ofNat (bits / 2^(8 * (7 - i))))
  return b

def compress (h : State) (blk : ByteArray) (off : Nat) : State :=
  if hblk : off + 64 ≤ blk.size then Id.run do
    let mut w : Vector UInt32 64 := Vector.replicate 64 0
    for ht : t in [0:16] do
      have lt16 : t < 16 := ht.upper
      let i := off + 4 * t
      let v := (blk[i]'(by omega)).toUInt32 <<< 24 ||| (blk[i + 1]'(by omega)).toUInt32 <<< 16 |||
               (blk[i + 2]'(by omega)).toUInt32 <<< 8 ||| (blk[i + 3]'(by omega)).toUInt32
      w := w.set t v (by omega)
    for ht : t in [16:64] do
      have ge16 : 16 ≤ t := ht.lower
      have lt64 : t < 64 := ht.upper
      let w15 := w[t - 15]'(by omega)
      let w2 := w[t - 2]'(by omega)
      let s0 := rotr w15 7 ^^^ rotr w15 18 ^^^ (w15 >>> 3)
      let s1 := rotr w2 17 ^^^ rotr w2 19 ^^^ (w2 >>> 10)
      w := w.set t (w[t - 16]'(by omega) + s0 + w[t - 7]'(by omega) + s1) (by omega)
    let mut a := h.h0; let mut b := h.h1; let mut c := h.h2; let mut d := h.h3
    let mut e := h.h4; let mut f := h.h5; let mut g := h.h6; let mut hh := h.h7
    for ht : t in [0:64] do
      have lt64 : t < 64 := ht.upper
      let S1 := rotr e 6 ^^^ rotr e 11 ^^^ rotr e 25
      let ch := (e &&& f) ^^^ ((~~~ e) &&& g)
      let t1 := hh + S1 + ch + K[t] + w[t]
      let S0 := rotr a 2 ^^^ rotr a 13 ^^^ rotr a 22
      let maj := (a &&& b) ^^^ (a &&& c) ^^^ (b &&& c)
      let t2 := S0 + maj
      hh := g; g := f; f := e; e := d + t1; d := c; c := b; b := a; a := t1 + t2
    return ⟨h.h0 + a, h.h1 + b, h.h2 + c, h.h3 + d, h.h4 + e, h.h5 + f, h.h6 + g, h.h7 + hh⟩
  else h

@[inline] def pushU32BE (out : ByteArray) (x : UInt32) : ByteArray :=
  out.push (x >>> 24).toUInt8 |>.push (x >>> 16).toUInt8 |>.push (x >>> 8).toUInt8 |>.push x.toUInt8

def State.toBytes (s : State) : ByteArray :=
  pushU32BE (pushU32BE (pushU32BE (pushU32BE (pushU32BE (pushU32BE (pushU32BE
    (pushU32BE (ByteArray.emptyWithCapacity 32) s.h0) s.h1) s.h2) s.h3) s.h4) s.h5) s.h6) s.h7

def hash (msg : ByteArray) : ByteArray := Id.run do
  let p := pad msg
  let mut h := H0
  for i in [0:p.size / 64] do h := compress h p (64 * i)
  return h.toBytes

/-- BIP340 `hash_tag(m) = SHA256(SHA256(tag) ‖ SHA256(tag) ‖ m)`. -/
def tagged (tag : String) (msg : ByteArray) : ByteArray :=
  let t := hash tag.toUTF8
  hash (t ++ t ++ msg)

end Secp.Sha256
