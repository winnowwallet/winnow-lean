import Winnow.Crypto
import Winnow.Net.Wire

/-! # Block headers (the `BlockHeader` half of `Network/Protocol/Block.swift`) -/

namespace Winnow.Net

/-- 80-byte block header; `hash` (SHA256d of the header, internal order) is computed once. -/
structure BlockHeader where
  version : Int32
  previousHash : ByteArray
  merkleRoot : ByteArray
  time : UInt32
  bits : UInt32
  nonce : UInt32
  hash : ByteArray
  deriving Inhabited

namespace BlockHeader

def serializedSize : Nat := 80

def serializeFields (version : Int32) (previousHash merkleRoot : ByteArray) (time bits nonce : UInt32) : ByteArray :=
  i32LE version ++ previousHash ++ merkleRoot ++ u32LE time ++ u32LE bits ++ u32LE nonce

/-- `BlockHeader(version:previousHash:merkleRoot:time:bits:nonce:)` (hashes must be 32 bytes). -/
def mk' (version : Int32) (previousHash merkleRoot : ByteArray) (time bits nonce : UInt32) : BlockHeader :=
  { version, previousHash, merkleRoot, time, bits, nonce,
    hash := sha256d (serializeFields version previousHash merkleRoot time bits nonce) }

def serialized (h : BlockHeader) : ByteArray :=
  serializeFields h.version h.previousHash h.merkleRoot h.time h.bits h.nonce

instance : BEq BlockHeader := ⟨fun a b => a.version == b.version && a.previousHash == b.previousHash &&
  a.merkleRoot == b.merkleRoot && a.time == b.time && a.bits == b.bits && a.nonce == b.nonce && a.hash == b.hash⟩

def read : Wire BlockHeader := do
  let version ← Wire.i32
  let previousHash ← Wire.bytes 32
  let merkleRoot ← Wire.bytes 32
  let time ← Wire.u32
  let bits ← Wire.u32
  let nonce ← Wire.u32
  return mk' version previousHash merkleRoot time bits nonce

def decode (data : ByteArray) : Except WireError BlockHeader :=
  Wire.eval (do let h ← read; Wire.requireEnd; return h) data

end BlockHeader
end Winnow.Net
