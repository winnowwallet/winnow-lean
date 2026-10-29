import Secp.Sha256
import Winnow.Bytes

/-! # SHA-256 (from the secp256k1 oracle library), SHA-512, HMAC, PBKDF2 (FIPS 180-4, RFC 2104, RFC 8018)

Replaces CryptoKit's `SHA256`/`SHA512`/`HMAC` and CommonCrypto's `CCKeyDerivationPBKDF`. -/

namespace Winnow

def sha256 (b : ByteArray) : ByteArray := Secp.Sha256.hash b
def sha256d (b : ByteArray) : ByteArray := sha256 (sha256 b)
/-- BIP340 tagged hash: `sha256(sha256(tag) ‖ sha256(tag) ‖ msg)`. -/
def taggedHash (tag : String) (msg : ByteArray) : ByteArray :=
  let t := sha256 tag.toUTF8
  sha256 (t ++ t ++ msg)

namespace Sha512

def K : Array UInt64 := #[
  0x428a2f98d728ae22, 0x7137449123ef65cd, 0xb5c0fbcfec4d3b2f, 0xe9b5dba58189dbbc, 0x3956c25bf348b538,
  0x59f111f1b605d019, 0x923f82a4af194f9b, 0xab1c5ed5da6d8118, 0xd807aa98a3030242, 0x12835b0145706fbe,
  0x243185be4ee4b28c, 0x550c7dc3d5ffb4e2, 0x72be5d74f27b896f, 0x80deb1fe3b1696b1, 0x9bdc06a725c71235,
  0xc19bf174cf692694, 0xe49b69c19ef14ad2, 0xefbe4786384f25e3, 0x0fc19dc68b8cd5b5, 0x240ca1cc77ac9c65,
  0x2de92c6f592b0275, 0x4a7484aa6ea6e483, 0x5cb0a9dcbd41fbd4, 0x76f988da831153b5, 0x983e5152ee66dfab,
  0xa831c66d2db43210, 0xb00327c898fb213f, 0xbf597fc7beef0ee4, 0xc6e00bf33da88fc2, 0xd5a79147930aa725,
  0x06ca6351e003826f, 0x142929670a0e6e70, 0x27b70a8546d22ffc, 0x2e1b21385c26c926, 0x4d2c6dfc5ac42aed,
  0x53380d139d95b3df, 0x650a73548baf63de, 0x766a0abb3c77b2a8, 0x81c2c92e47edaee6, 0x92722c851482353b,
  0xa2bfe8a14cf10364, 0xa81a664bbc423001, 0xc24b8b70d0f89791, 0xc76c51a30654be30, 0xd192e819d6ef5218,
  0xd69906245565a910, 0xf40e35855771202a, 0x106aa07032bbd1b8, 0x19a4c116b8d2d0c8, 0x1e376c085141ab53,
  0x2748774cdf8eeb99, 0x34b0bcb5e19b48a8, 0x391c0cb3c5c95a63, 0x4ed8aa4ae3418acb, 0x5b9cca4f7763e373,
  0x682e6ff3d6b2b8a3, 0x748f82ee5defb2fc, 0x78a5636f43172f60, 0x84c87814a1f0ab72, 0x8cc702081a6439ec,
  0x90befffa23631e28, 0xa4506cebde82bde9, 0xbef9a3f7b2c67915, 0xc67178f2e372532b, 0xca273eceea26619c,
  0xd186b8c721c0c207, 0xeada7dd6cde0eb1e, 0xf57d4f7fee6ed178, 0x06f067aa72176fba, 0x0a637dc5a2c898a6,
  0x113f9804bef90dae, 0x1b710b35131c471b, 0x28db77f523047d84, 0x32caab7b40c72493, 0x3c9ebe0a15c9bebc,
  0x431d67c49c100d4c, 0x4cc5d4becb3e42b6, 0x597f299cfc657e2a, 0x5fcb6fab3ad6faec, 0x6c44198c4a475817]

def H0 : Array UInt64 := #[
  0x6a09e667f3bcc908, 0xbb67ae8584caa73b, 0x3c6ef372fe94f82b, 0xa54ff53a5f1d36f1,
  0x510e527fade682d1, 0x9b05688c2b3e6c1f, 0x1f83d9abfb41bd6b, 0x5be0cd19137e2179]

@[inline] def rotr (x : UInt64) (n : UInt64) : UInt64 := (x >>> n) ||| (x <<< (64 - n))

def compress (h : Array UInt64) (p : ByteArray) (off : Nat) : Array UInt64 := Id.run do
  let mut w : Array UInt64 := Array.replicate 80 0
  for t in [0:16] do w := w.set! t (readBE p (off + 8 * t) 8)
  for t in [16:80] do
    let s0 := rotr w[t-15]! 1 ^^^ rotr w[t-15]! 8 ^^^ (w[t-15]! >>> 7)
    let s1 := rotr w[t-2]! 19 ^^^ rotr w[t-2]! 61 ^^^ (w[t-2]! >>> 6)
    w := w.set! t (w[t-16]! + s0 + w[t-7]! + s1)
  let mut a := h[0]!; let mut b := h[1]!; let mut c := h[2]!; let mut d := h[3]!
  let mut e := h[4]!; let mut f := h[5]!; let mut g := h[6]!; let mut hh := h[7]!
  for t in [0:80] do
    let S1 := rotr e 14 ^^^ rotr e 18 ^^^ rotr e 41
    let ch := (e &&& f) ^^^ ((~~~ e) &&& g)
    let t1 := hh + S1 + ch + K[t]! + w[t]!
    let S0 := rotr a 28 ^^^ rotr a 34 ^^^ rotr a 39
    let maj := (a &&& b) ^^^ (a &&& c) ^^^ (b &&& c)
    let t2 := S0 + maj
    hh := g; g := f; f := e; e := d + t1; d := c; c := b; b := a; a := t1 + t2
  return #[h[0]! + a, h[1]! + b, h[2]! + c, h[3]! + d, h[4]! + e, h[5]! + f, h[6]! + g, h[7]! + hh]

def hash (msg : ByteArray) : ByteArray := Id.run do
  let len := msg.size
  let mut p := msg.push 0x80
  while p.size % 128 != 112 do p := p.push 0
  p := p ++ ByteArray.mk (Array.replicate 8 0) ++ u64BE (len * 8).toUInt64
  let mut h := H0
  for i in [0:p.size / 128] do h := compress h p (128 * i)
  let mut out := ByteArray.emptyWithCapacity 64
  for x in h do
    for i in [0:8] do out := out.push (x >>> (8 * (7 - i)).toUInt64).toUInt8
  return out
where u64BE (n : UInt64) : ByteArray := Id.run do
  let mut b := ByteArray.emptyWithCapacity 8
  for i in [0:8] do b := b.push (n >>> (8 * (7 - i)).toUInt64).toUInt8
  return b

end Sha512

def sha512 (b : ByteArray) : ByteArray := Sha512.hash b

/-- HMAC over a hash with the given block size. -/
def hmac (h : ByteArray → ByteArray) (blockSize : Nat) (key msg : ByteArray) : ByteArray := Id.run do
  let k := if key.size > blockSize then h key else key
  let k := k ++ ByteArray.mk (Array.replicate (blockSize - k.size) 0)
  let mut ipad := ByteArray.emptyWithCapacity blockSize
  let mut opad := ByteArray.emptyWithCapacity blockSize
  for i in [0:blockSize] do
    ipad := ipad.push (k.get! i ^^^ 0x36)
    opad := opad.push (k.get! i ^^^ 0x5c)
  return h (opad ++ h (ipad ++ msg))

def hmacSha256 (key msg : ByteArray) : ByteArray := hmac sha256 64 key msg
def hmacSha512 (key msg : ByteArray) : ByteArray := hmac sha512 128 key msg

/-- PBKDF2-HMAC-SHA512 (BIP39 uses 2048 rounds and a 64-byte key). -/
def pbkdf2HmacSha512 (password salt : ByteArray) (rounds : Nat := 2048) (keyLength : Nat := 64) : ByteArray := Id.run do
  let blocks := (keyLength + 63) / 64
  let mut out := ByteArray.empty
  for i in [1:blocks + 1] do
    let mut u := hmacSha512 password (salt ++ u32BE i.toUInt32)
    let mut t := u
    for _ in [1:rounds] do
      u := hmacSha512 password u
      let mut x := ByteArray.emptyWithCapacity 64
      for j in [0:64] do x := x.push (t.get! j ^^^ u.get! j)
      t := x
    out := out ++ t
  return out.extract 0 keyLength

end Winnow
