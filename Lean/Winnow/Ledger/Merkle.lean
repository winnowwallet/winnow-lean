import Winnow.Crypto
import Winnow.Tx.PSBT

/-! # The Merkle commitments of Ledger's Bitcoin app

Port of `Sources/WalletCore/Ledger/LedgerMerkle.swift` (upstream 1cf93fb). The phone commits to a list
or a key/value map by its root; the device then asks for one element and its proof at a time and
checks each against the root, so it never has to hold the whole PSBT. -/

namespace Winnow.Ledger.Merkle

/-- The root of an empty tree. -/
def emptyRoot : ByteArray := ByteArray.mk (Array.replicate 32 0)

/-- SHA-256(0x00 ‖ element): the leaf of a committed list element. -/
def elementHash (element : ByteArray) : ByteArray := sha256 (ByteArray.mk #[0x00] ++ element)

/-- SHA-256(0x01 ‖ left ‖ right): an inner node. -/
def combine (left right : ByteArray) : ByteArray := sha256 (ByteArray.mk #[0x01] ++ left ++ right)

/-- The left subtree of n ≥ 2 leaves holds the largest power of two strictly below n, so it is
always complete. -/
def leftCount (count : Nat) : Nat := Id.run do
  let mut left := 1
  for _ in [0:count] do
    if left * 2 < count then left := left * 2 else break
  return left

/-- The root over already-hashed 32-byte leaves, on the slice `[lo, lo + n)`. `fuel` bounds the
recursion depth (each level at least halves `n`, so `n` itself is always enough). -/
def rootSlice (leaves : Array ByteArray) : (fuel lo n : Nat) → ByteArray
  | 0, _, _ => emptyRoot
  | fuel + 1, lo, n =>
    if n == 0 then emptyRoot
    else if n == 1 then leaves[lo]!
    else
      let left := leftCount n
      combine (rootSlice leaves fuel lo left) (rootSlice leaves fuel (lo + left) (n - left))

/-- The root over already-hashed 32-byte leaves. -/
def root (leaves : Array ByteArray) : ByteArray := rootSlice leaves leaves.size 0 leaves.size

/-- The sibling hashes from leaf `index` of the slice `[lo, lo + n)` up to its root, bottom first. -/
def proofSlice (leaves : Array ByteArray) : (fuel lo n index : Nat) → Array ByteArray
  | 0, _, _, _ => #[]
  | fuel + 1, lo, n, index =>
    if n ≤ 1 then #[]
    else
      let left := leftCount n
      if index < left then
        proofSlice leaves fuel lo left index |>.push (rootSlice leaves n (lo + left) (n - left))
      else
        proofSlice leaves fuel (lo + left) (n - left) (index - left) |>.push (rootSlice leaves n lo left)

/-- The sibling hashes from leaf `index` up to the root, bottom first. -/
def proof (leaves : Array ByteArray) (index : Nat) : Array ByteArray :=
  proofSlice leaves leaves.size 0 leaves.size index

/-- `sortedPairs`: a map's pairs by key, lexicographically. -/
def sortedPairs (pairs : Array PSBT.KeyValue) : Array PSBT.KeyValue := sortBytes (·.key) pairs

/-- A key/value map sorted by key: compactSize(n) ‖ keys root ‖ values root, each tree over the
element hashes of the keys or values in that order. -/
def mapCommitment (pairs : Array PSBT.KeyValue) : ByteArray :=
  let sorted := sortedPairs pairs
  compactSize sorted.size.toUInt64 ++ root (sorted.map (elementHash ·.key)) ++ root (sorted.map (elementHash ·.value))

end Winnow.Ledger.Merkle
