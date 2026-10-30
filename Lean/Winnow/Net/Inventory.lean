import Winnow.Net.Wire

/-! # Inventory vectors (`Network/Protocol/Inventory.swift`): `inv`, `getdata`, `notfound` payloads -/

namespace Winnow.Net

/-- Inventory type (uint32); MSG_WITNESS_FLAG (0x40000000) asks for witness serialization (BIP144). -/
structure InventoryType where
  rawValue : UInt32
  deriving BEq, Inhabited, Repr, Hashable

namespace InventoryType
def error : InventoryType := ⟨0⟩
def tx : InventoryType := ⟨1⟩
def block : InventoryType := ⟨2⟩
def filteredBlock : InventoryType := ⟨3⟩
def cmpctBlock : InventoryType := ⟨4⟩
def witnessTx : InventoryType := ⟨0x40000001⟩
def witnessBlock : InventoryType := ⟨0x40000002⟩
def baseType (t : InventoryType) : InventoryType := ⟨t.rawValue &&& 0x3FFFFFFF⟩
def isWitness (t : InventoryType) : Bool := t.rawValue &&& 0x40000000 != 0
end InventoryType

/-- One (type, 32-byte hash) pair; for witness types the hash is still the plain txid/block hash. -/
structure InventoryVector where
  type : InventoryType
  hash : ByteArray
  deriving Inhabited

instance : BEq InventoryVector := ⟨fun a b => a.type == b.type && a.hash == b.hash⟩

def InventoryVector.serialized (v : InventoryVector) : ByteArray := u32LE v.type.rawValue ++ v.hash
def InventoryVector.read : Wire InventoryVector := do
  let t ← Wire.u32
  let h ← Wire.bytes 32
  return { type := ⟨t⟩, hash := h }

structure InventoryPayload where
  vectors : Array InventoryVector
  deriving Inhabited, BEq

namespace InventoryPayload
def maxCount : UInt64 := 50_000

def serialized (p : InventoryPayload) : ByteArray :=
  p.vectors.foldl (fun d v => d ++ v.serialized) (compactSize p.vectors.size.toUInt64)

def decode (payload : ByteArray) : Except WireError InventoryPayload := Wire.eval (do
  let count ← Wire.varInt
  if count > maxCount then throw (.malformed s!"inventory count {count}")
  let mut vs : Array InventoryVector := Array.mkEmpty count.toNat
  for _ in [0:count.toNat] do vs := vs.push (← InventoryVector.read)
  Wire.requireEnd
  return { vectors := vs }) payload
end InventoryPayload

end Winnow.Net
