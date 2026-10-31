import Winnow.Crypto.AES

/-! # AES-GCM (NIST SP 800-38D), as CryptoKit's `AES.GCM` uses it

A 16-byte tag, any additional authenticated data, 128-, 192- or 256-bit keys, and a nonce of at least
12 bytes as CryptoKit's `AES.GCM.Nonce` accepts: 12 bytes give `J0 = nonce ‖ 0³¹ ‖ 1`, a longer one is
GHASHed into `J0`. `SealedBox.combined` is CryptoKit's `combined` layout, nonce ‖ ciphertext ‖ tag, which
exists only for a 12-byte nonce (CryptoKit's is nil otherwise).

GHASH multiplies in GF(2¹²⁸) one bit at a time over two `UInt64` halves with masks instead of branches, so
its running time does not depend on the data or on H; the tag is compared in constant time and nothing is
decrypted before it matches. The AES rounds themselves are **not constant-time** (table lookups indexed by
secret bytes, `Winnow.Crypto.AES`), so AES-GCM as a whole is not either: correct by the NIST, Wycheproof and
CryptoKit vectors (`crypto-test`), acceptable for Winnow's rare backup encryption on the user's own device,
and not for servers, shared hosts or anything that encrypts or decrypts on someone else's request
(SECURITY.md, "Timing side channels").

Failures are CryptoKit's: `authenticationFailure` for a wrong key, nonce, data or tag;
`incorrectParameterSize` for a nonce under 12 bytes or a combined box shorter than nonce and tag;
`incorrectKeySize` for a key that is not 16, 24 or 32 bytes. -/

namespace Winnow.AESGCM
open Winnow.AES

inductive Error where
  | authenticationFailure
  | incorrectParameterSize
  | incorrectKeySize
  deriving Repr, BEq, Inhabited

def Error.name : Error → String
  | .authenticationFailure => "authenticationFailure"
  | .incorrectParameterSize => "incorrectParameterSize"
  | .incorrectKeySize => "incorrectKeySize"

def nonceSize : Nat := 12
def tagSize : Nat := 16

/-- A 128-bit field element, big-endian halves (bit 0 of the spec is the top bit of `hi`). -/
structure Elem where
  hi : UInt64
  lo : UInt64
  deriving BEq, Inhabited

def Elem.ofBytes (b : ByteArray) (off : Nat := 0) : Elem :=
  { hi := readBE b off 8, lo := readBE b (off + 8) 8 }

private def u64BE (v : UInt64) : ByteArray := u32BE (v >>> 32).toUInt32 ++ u32BE v.toUInt32

def Elem.toBytes (x : Elem) : ByteArray := u64BE x.hi ++ u64BE x.lo

def Elem.xor (a b : Elem) : Elem := { hi := a.hi ^^^ b.hi, lo := a.lo ^^^ b.lo }

/-- X·Y in GF(2¹²⁸) with the GCM bit order and reduction polynomial (SP 800-38D, Algorithm 1), with masks
in place of branches. -/
def mul (x y : Elem) : Elem := Id.run do
  let mut zh : UInt64 := 0
  let mut zl : UInt64 := 0
  let mut vh := y.hi
  let mut vl := y.lo
  for i in [0:128] do
    let word := if i < 64 then x.hi else x.lo
    let bit := (word >>> (63 - (i % 64)).toUInt64) &&& 1
    let take := 0 - bit
    zh := zh ^^^ (vh &&& take)
    zl := zl ^^^ (vl &&& take)
    let carry := 0 - (vl &&& 1)
    vl := (vl >>> 1) ||| (vh <<< 63)
    vh := (vh >>> 1) ^^^ (0xE100000000000000 &&& carry)
  return { hi := zh, lo := zl }

/-- GHASH_H over `data` zero-padded to whole blocks, continuing from `acc`. -/
def ghashPadded (h : Elem) (acc : Elem) (data : ByteArray) : Elem := Id.run do
  let mut y := acc
  let full := data.size / 16
  for i in [0:full] do
    y := mul (y.xor (Elem.ofBytes data (16 * i))) h
  if data.size % 16 != 0 then
    let tail := data.extract (16 * full) data.size ++ ByteArray.mk (Array.replicate (16 - data.size % 16) 0)
    y := mul (y.xor (Elem.ofBytes tail)) h
  return y

/-- GCTR from the counter block `icb` (the last word incremented mod 2³²). -/
def gctr (k : Key) (icb : Block) (data : ByteArray) : ByteArray := Id.run do
  let mut out := ByteArray.emptyWithCapacity data.size
  let mut counter := icb
  let mut off := 0
  while off < data.size do
    let ks := (encryptBlock k counter).toBytes
    let n := min 16 (data.size - off)
    for j in [0:n] do
      out := out.push (data[off + j]! ^^^ ks[j]!)
    counter := { counter with s3 := counter.s3 + 1 }
    off := off + n
  return out

private def lengths (aad ct : ByteArray) : Elem :=
  { hi := (aad.size * 8).toUInt64, lo := (ct.size * 8).toUInt64 }

private def tagFor (k : Key) (h : Elem) (j0 : Block) (aad ct : ByteArray) : ByteArray :=
  let s := ghashPadded h (ghashPadded h default aad) ct
  let s := mul (s.xor (lengths aad ct)) h
  let ej0 := Elem.ofBytes (encryptBlock k j0).toBytes
  (s.xor ej0).toBytes

/-- Equal-length byte strings compared without an early exit. -/
def constantTimeEqual (a b : ByteArray) : Bool := Id.run do
  if a.size != b.size then return false
  let mut diff : UInt8 := 0
  for i in [0:a.size] do diff := diff ||| (a[i]! ^^^ b[i]!)
  return diff == 0

structure SealedBox where
  nonce : ByteArray
  ciphertext : ByteArray
  tag : ByteArray

/-- CryptoKit's `combined`: nonce ‖ ciphertext ‖ tag; none unless the nonce is 12 bytes. -/
def SealedBox.combined (b : SealedBox) : Option ByteArray :=
  if b.nonce.size == nonceSize then some (b.nonce ++ b.ciphertext ++ b.tag) else none

/-- `AES.GCM.SealedBox(combined:)`. -/
def SealedBox.ofCombined (b : ByteArray) : Except Error SealedBox :=
  if b.size < nonceSize + tagSize then .error .incorrectParameterSize
  else .ok { nonce := b.extract 0 nonceSize, ciphertext := b.extract nonceSize (b.size - tagSize),
             tag := b.extract (b.size - tagSize) b.size }

private def setup (key nonce : ByteArray) : Except Error (Key × Elem × Block) := do
  let some k := expand key | throw .incorrectKeySize
  unless nonce.size ≥ nonceSize do throw .incorrectParameterSize
  let h := Elem.ofBytes (encryptBlock k default).toBytes
  let j0 := if nonce.size == nonceSize then Block.ofBytes (nonce ++ ByteArray.mk #[0, 0, 0, 1])
    else Block.ofBytes (mul ((ghashPadded h default nonce).xor { hi := 0, lo := (nonce.size * 8).toUInt64 }) h).toBytes
  return (k, h, j0)

/-- `AES.GCM.seal(_:using:nonce:authenticating:)` with the nonce given. -/
def «seal» (key plaintext nonce : ByteArray) (aad : ByteArray := .empty) : Except Error SealedBox := do
  let (k, h, j0) ← setup key nonce
  let ct := gctr k { j0 with s3 := j0.s3 + 1 } plaintext
  return { nonce, ciphertext := ct, tag := tagFor k h j0 aad ct }

/-- `AES.GCM.seal` with a fresh random nonce (CryptoKit's default). -/
def sealRandom (key plaintext : ByteArray) (aad : ByteArray := .empty) : IO (Except Error SealedBox) := do
  return «seal» key plaintext (← IO.getRandomBytes nonceSize.toUSize) aad

/-- `AES.GCM.open(_:using:authenticating:)`: the tag is checked before anything is decrypted. -/
def «open» (key : ByteArray) (box : SealedBox) (aad : ByteArray := .empty) : Except Error ByteArray := do
  let (k, h, j0) ← setup key box.nonce
  unless box.tag.size == tagSize do throw .authenticationFailure
  unless constantTimeEqual (tagFor k h j0 aad box.ciphertext) box.tag do throw .authenticationFailure
  return gctr k { j0 with s3 := j0.s3 + 1 } box.ciphertext

/-- `open` of a `combined` box. -/
def openCombined (key combined : ByteArray) (aad : ByteArray := .empty) : Except Error ByteArray := do
  «open» key (← SealedBox.ofCombined combined) aad

end Winnow.AESGCM
