import Winnow.Crypto.Sha2

/-! # RIPEMD-160 and Hash160 (`RIPEMD160(SHA256(x))`) -/

namespace Winnow.Ripemd160

def rl : Array Nat := #[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15, 7,4,13,1,10,6,15,3,12,0,9,5,2,14,11,8,
  3,10,14,4,9,15,8,1,2,7,0,6,13,11,5,12, 1,9,11,10,0,8,12,4,13,3,7,15,14,5,6,2, 4,0,5,9,7,12,2,10,14,1,3,8,11,6,15,13]
def rr : Array Nat := #[5,14,7,0,9,2,11,4,13,6,15,8,1,10,3,12, 6,11,3,7,0,13,5,10,14,15,8,12,4,9,1,2,
  15,5,1,3,7,14,6,9,11,8,12,2,10,0,4,13, 8,6,4,1,3,11,15,0,5,12,2,13,9,7,10,14, 12,15,10,4,1,5,8,7,6,2,13,14,0,3,9,11]
def sl : Array UInt32 := #[11,14,15,12,5,8,7,9,11,13,14,15,6,7,9,8, 7,6,8,13,11,9,7,15,7,12,15,9,11,7,13,12,
  11,13,6,7,14,9,13,15,14,8,13,6,5,12,7,5, 11,12,14,15,14,15,9,8,9,14,5,6,8,6,5,12, 9,15,5,11,6,8,13,12,5,12,13,14,11,8,5,6]
def sr : Array UInt32 := #[8,9,9,11,13,15,15,5,7,7,8,11,14,14,12,6, 9,13,15,7,12,8,9,11,7,7,12,7,6,15,13,11,
  9,7,15,11,8,6,6,14,12,13,5,14,13,13,7,5, 15,5,8,11,14,14,6,14,6,9,12,9,12,5,15,8, 8,5,12,9,12,5,14,6,8,13,6,5,15,13,11,11]
def kl : Array UInt32 := #[0x00000000, 0x5a827999, 0x6ed9eba1, 0x8f1bbcdc, 0xa953fd4e]
def kr : Array UInt32 := #[0x50a28be6, 0x5c4dd124, 0x6d703ef3, 0x7a6d76e9, 0x00000000]

@[inline] def rotl (x n : UInt32) : UInt32 := (x <<< n) ||| (x >>> (32 - n))

@[inline] def f (j : Nat) (x y z : UInt32) : UInt32 :=
  if j < 16 then x ^^^ y ^^^ z
  else if j < 32 then (x &&& y) ||| ((~~~ x) &&& z)
  else if j < 48 then (x ||| (~~~ y)) ^^^ z
  else if j < 64 then (x &&& z) ||| (y &&& (~~~ z))
  else x ^^^ (y ||| (~~~ z))

def compress (h : Array UInt32) (p : ByteArray) (off : Nat) : Array UInt32 := Id.run do
  let mut x : Array UInt32 := Array.replicate 16 0
  for i in [0:16] do x := x.set! i (readLE p (off + 4 * i) 4).toUInt32
  let mut al := h[0]!; let mut bl := h[1]!; let mut cl := h[2]!; let mut dl := h[3]!; let mut el := h[4]!
  let mut ar := h[0]!; let mut br := h[1]!; let mut cr := h[2]!; let mut dr := h[3]!; let mut er := h[4]!
  for j in [0:80] do
    let t := rotl (al + f j bl cl dl + x[rl[j]!]! + kl[j / 16]!) sl[j]! + el
    al := el; el := dl; dl := rotl cl 10; cl := bl; bl := t
    let t' := rotl (ar + f (79 - j) br cr dr + x[rr[j]!]! + kr[j / 16]!) sr[j]! + er
    ar := er; er := dr; dr := rotl cr 10; cr := br; br := t'
  return #[h[1]! + cl + dr, h[2]! + dl + er, h[3]! + el + ar, h[4]! + al + br, h[0]! + bl + cr]

def hash (msg : ByteArray) : ByteArray := Id.run do
  let len := msg.size
  let mut p := msg.push 0x80
  while p.size % 64 != 56 do p := p.push 0
  p := p ++ u64LE (len * 8).toUInt64
  let mut h : Array UInt32 := #[0x67452301, 0xefcdab89, 0x98badcfe, 0x10325476, 0xc3d2e1f0]
  for i in [0:p.size / 64] do h := compress h p (64 * i)
  let mut out := ByteArray.emptyWithCapacity 20
  for v in h do out := out ++ u32LE v
  return out

end Winnow.Ripemd160

namespace Winnow
def ripemd160 (b : ByteArray) : ByteArray := Ripemd160.hash b
def hash160 (b : ByteArray) : ByteArray := ripemd160 (sha256 b)
end Winnow
