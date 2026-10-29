import Winnow.Tx.Transaction
import Winnow.Net.Header
import Std.Data.HashSet

/-! # Full blocks (the `Block` half of `Network/Protocol/Block.swift`), segwit serialization

Transactions are the Tx area's `Winnow.Transaction`. -/

namespace Winnow.Net

structure Block where
  header : BlockHeader
  transactions : Array Transaction
  deriving Inhabited

namespace Block

def maxTransactions : UInt64 := 100_000

def hash (b : Block) : ByteArray := b.header.hash

/-- Merkle root over the txids (odd rows duplicate their last node); `none` for an empty block. -/
def computedMerkleRoot (b : Block) : Option ByteArray := Id.run do
  if b.transactions.isEmpty then return none
  let mut level := b.transactions.map (·.txid)
  while level.size > 1 do
    if level.size % 2 == 1 then level := level.push level.back!
    let mut next : Array ByteArray := Array.mkEmpty (level.size / 2)
    let mut i := 0
    while i < level.size do
      next := next.push (sha256d (level[i]! ++ level[i + 1]!))
      i := i + 2
    level := next
  return level[0]?

/-- The transaction set hashes to the committed root, duplicate txids refused first (CVE-2012-2459). -/
def hasValidMerkleRoot (b : Block) : Bool :=
  let txids := b.transactions.map (·.txid)
  let unique : Std.HashSet ByteArray := txids.foldl (·.insert ·) {}
  if unique.size != txids.size then false
  else match b.computedMerkleRoot with
    | some r => r == b.header.merkleRoot
    | none => false

def serialized (b : Block) : ByteArray :=
  b.transactions.foldl (fun d tx => d ++ tx.serialized true) (b.header.serialized ++ compactSize b.transactions.size.toUInt64)

def decode (data : ByteArray) : Except WireError Block := Wire.eval (do
  let header ← BlockHeader.read
  let count ← Wire.varInt
  if count > maxTransactions then throw (.malformed s!"block tx count {count}")
  let mut txs : Array Transaction := Array.mkEmpty count.toNat
  for _ in [0:count.toNat] do txs := txs.push (← Transaction.decodeFrom)
  Wire.requireEnd
  return { header, transactions := txs }) data

end Block
end Winnow.Net
