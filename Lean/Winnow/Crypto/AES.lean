import Winnow.Bytes

/-! # The AES block cipher (FIPS 197): AES-128, AES-192 and AES-256 encryption

Only the forward cipher: GCM (`Winnow.Crypto.AESGCM`) runs AES in counter mode, so decryption never
inverts the block cipher. The S-box is computed, not transcribed (the multiplicative inverse in GF(2⁸)
followed by the affine map), and the rounds use the usual four 256-word T-tables built from it.

**Not constant-time.** Correct by the FIPS 197 vectors and, through AES-GCM, Wycheproof's and CryptoKit's
(`crypto-test`), but the S-box and T-table lookups are indexed by secret bytes, so their cache timing
depends on the key and the data; this matches neither CryptoKit's hardware AES nor a bitsliced
implementation. That is acceptable for what Winnow does with it: encrypting and decrypting its backup,
rarely, on the user's own device, where no one can trigger encryptions on demand or time them (an attacker
able to time cache lines there already has the process). Do not reuse it in servers, shared hosts, or
anything that encrypts or decrypts on someone else's request (SECURITY.md, "Timing side channels"). -/

namespace Winnow.AES

/-- Multiplication by x in GF(2⁸) modulo x⁸ + x⁴ + x³ + x + 1. -/
def xtime (b : UInt8) : UInt8 := (b <<< 1) ^^^ (if b &&& 0x80 != 0 then 0x1b else 0)

/-- Multiplication in GF(2⁸). -/
def gmul (a b : UInt8) : UInt8 := Id.run do
  let mut x := a
  let mut y := b
  let mut acc : UInt8 := 0
  for _ in [0:8] do
    if y &&& 1 != 0 then acc := acc ^^^ x
    x := xtime x
    y := y >>> 1
  return acc

/-- The multiplicative inverse (x²⁵⁴; 0 maps to 0). -/
def ginv (x : UInt8) : UInt8 := Id.run do
  -- 254 = 0b11111110
  let mut result : UInt8 := 1
  let mut base := x
  let mut e : Nat := 254
  while e > 0 do
    if e % 2 == 1 then result := gmul result base
    base := gmul base base
    e := e / 2
  return result

private def rotl8 (b : UInt8) (n : UInt8) : UInt8 := (b <<< n) ||| (b >>> (8 - n))

/-- The affine map of the S-box. -/
def affine (b : UInt8) : UInt8 := b ^^^ rotl8 b 1 ^^^ rotl8 b 2 ^^^ rotl8 b 3 ^^^ rotl8 b 4 ^^^ 0x63

/-- The S-box. -/
def sbox : Array UInt8 := (Array.range 256).map fun i => affine (ginv i.toUInt8)

private def word (a b c d : UInt8) : UInt32 :=
  (a.toUInt32 <<< 24) ||| (b.toUInt32 <<< 16) ||| (c.toUInt32 <<< 8) ||| d.toUInt32

/-- `Te0[x] = (2·S[x], S[x], S[x], 3·S[x])`; `Te1`…`Te3` are its byte rotations. -/
def te0 : Array UInt32 := sbox.map fun s => word (xtime s) s s (xtime s ^^^ s)
def te1 : Array UInt32 := sbox.map fun s => word (xtime s ^^^ s) (xtime s) s s
def te2 : Array UInt32 := sbox.map fun s => word s (xtime s ^^^ s) (xtime s) s
def te3 : Array UInt32 := sbox.map fun s => word s s (xtime s ^^^ s) (xtime s)

@[inline] private def sb (w : UInt32) (shift : UInt32) : UInt32 := (sbox[((w >>> shift) &&& 0xff).toNat]!).toUInt32

private def subWord (w : UInt32) : UInt32 :=
  (sb w 24 <<< 24) ||| (sb w 16 <<< 16) ||| (sb w 8 <<< 8) ||| sb w 0

private def rotWord (w : UInt32) : UInt32 := (w <<< 8) ||| (w >>> 24)

/-- An expanded key: `4 (rounds + 1)` round-key words. -/
structure Key where
  rounds : Nat
  words : Array UInt32

/-- The key schedule for a 16-, 24- or 32-byte key; none for any other size. -/
def expand (key : ByteArray) : Option Key := do
  let nk := key.size / 4
  unless key.size == 16 || key.size == 24 || key.size == 32 do none
  let rounds := nk + 6
  let mut w : Array UInt32 := #[]
  for i in [0:nk] do
    w := w.push (word key[4 * i]! key[4 * i + 1]! key[4 * i + 2]! key[4 * i + 3]!)
  let mut rcon : UInt32 := 0x01
  for i in [nk:4 * (rounds + 1)] do
    let mut temp := w[i - 1]!
    if i % nk == 0 then
      temp := subWord (rotWord temp) ^^^ (rcon <<< 24)
      rcon := (xtime rcon.toUInt8).toUInt32
    else if nk > 6 && i % nk == 4 then
      temp := subWord temp
    w := w.push (w[i - nk]! ^^^ temp)
  return { rounds, words := w }

/-- One block as four big-endian column words. -/
structure Block where
  s0 : UInt32
  s1 : UInt32
  s2 : UInt32
  s3 : UInt32
  deriving BEq, Inhabited

def Block.ofBytes (b : ByteArray) (off : Nat := 0) : Block :=
  let w (i : Nat) := word b[off + i]! b[off + i + 1]! b[off + i + 2]! b[off + i + 3]!
  { s0 := w 0, s1 := w 4, s2 := w 8, s3 := w 12 }

def Block.toBytes (x : Block) : ByteArray := u32BE x.s0 ++ u32BE x.s1 ++ u32BE x.s2 ++ u32BE x.s3

@[inline] private def t (table : Array UInt32) (w : UInt32) (shift : UInt32) : UInt32 :=
  table[((w >>> shift) &&& 0xff).toNat]!

/-- The forward cipher on one block. -/
def encryptBlock (k : Key) (x : Block) : Block := Id.run do
  let rk := k.words
  let mut s0 := x.s0 ^^^ rk[0]!
  let mut s1 := x.s1 ^^^ rk[1]!
  let mut s2 := x.s2 ^^^ rk[2]!
  let mut s3 := x.s3 ^^^ rk[3]!
  for r in [1:k.rounds] do
    let o := 4 * r
    let n0 := t te0 s0 24 ^^^ t te1 s1 16 ^^^ t te2 s2 8 ^^^ t te3 s3 0 ^^^ rk[o]!
    let n1 := t te0 s1 24 ^^^ t te1 s2 16 ^^^ t te2 s3 8 ^^^ t te3 s0 0 ^^^ rk[o + 1]!
    let n2 := t te0 s2 24 ^^^ t te1 s3 16 ^^^ t te2 s0 8 ^^^ t te3 s1 0 ^^^ rk[o + 2]!
    let n3 := t te0 s3 24 ^^^ t te1 s0 16 ^^^ t te2 s1 8 ^^^ t te3 s2 0 ^^^ rk[o + 3]!
    s0 := n0; s1 := n1; s2 := n2; s3 := n3
  let o := 4 * k.rounds
  let last (a b c d : UInt32) (i : Nat) : UInt32 :=
    ((sb a 24 <<< 24) ||| (sb b 16 <<< 16) ||| (sb c 8 <<< 8) ||| sb d 0) ^^^ rk[o + i]!
  return { s0 := last s0 s1 s2 s3 0, s1 := last s1 s2 s3 s0 1, s2 := last s2 s3 s0 s1 2, s3 := last s3 s0 s1 s2 3 }

/-- The forward cipher on a 16-byte block (none for a bad key or block size). -/
def encrypt (key block : ByteArray) : Option ByteArray := do
  let k ← expand key
  unless block.size == 16 do none
  return (encryptBlock k (Block.ofBytes block)).toBytes

end Winnow.AES
