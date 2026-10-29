import Winnow.Keys.Secp256k1

/-! # BIP341 Taproot (port of `Script/Taproot.swift`)

Tapleaf/tapbranch hashes, script-tree merkle root, taptweak and output key, and control blocks. Leaf
scripts are raw bytes (`Script.bytes` in the Swift original). -/

namespace Winnow.Keys

inductive TaprootError where
  | invalidInternalKey | invalidControlBlock | tweakFailed | leafNotFound
  deriving Repr, DecidableEq

def TaprootError.name : TaprootError → String
  | .invalidInternalKey => "invalidInternalKey" | .invalidControlBlock => "invalidControlBlock"
  | .tweakFailed => "tweakFailed" | .leafNotFound => "leafNotFound"

/-- `Data.lexicographicallyPrecedes`. -/
def lexPrecedes (a b : ByteArray) : Bool := Id.run do
  for i in [0:min a.size b.size] do
    if a[i]! < b[i]! then return true
    if a[i]! > b[i]! then return false
  return a.size < b.size

namespace Taproot

/-- Leaf version for BIP342 tapscript leaves. -/
def leafVersion : UInt8 := 0xC0

/-- A Taproot script tree: leaves are (version, script) pairs, inner nodes binary branches. -/
inductive Tree where
  | leaf (version : UInt8) (script : ByteArray)
  | branch (l r : Tree)
  deriving Inhabited

/-- BIP341 control block: proof that a leaf is committed to by an output key. -/
structure ControlBlock where
  leafVersion : UInt8
  outputKeyParity : Bool
  internalKey : ByteArray
  /-- Sibling hashes, leaf level first (bottom-up). -/
  path : List ByteArray
  deriving Inhabited

namespace ControlBlock

def serialized (c : ControlBlock) : ByteArray :=
  c.path.foldl (· ++ ·) (ByteArray.mk #[c.leafVersion ||| (if c.outputKeyParity then 1 else 0)] ++ c.internalKey)

/-- Parses a control block; length must be 33 + 32m with m in 0...128. -/
def parse (b : ByteArray) : Except TaprootError ControlBlock := do
  if b.size < 33 || (b.size - 33) % 32 != 0 || (b.size - 33) / 32 > 128 then throw .invalidControlBlock
  let cb := b[0]!
  return { leafVersion := cb &&& 0xFE, outputKeyParity := cb &&& 1 != 0, internalKey := b.extract 1 33,
           path := (List.range ((b.size - 33) / 32)).map fun i => b.extract (33 + 32 * i) (65 + 32 * i) }

end ControlBlock

/-- TapLeaf hash: H_TapLeaf(leafVersion || CompactSize(script length) || script). -/
def leafHash (version : UInt8 := leafVersion) (script : ByteArray) : ByteArray :=
  taggedHash "TapLeaf" (ByteArray.mk #[version] ++ compactSize script.size.toUInt64 ++ script)

/-- TapBranch hash of the lexicographically sorted pair. -/
def branchHash (a b : ByteArray) : ByteArray :=
  if lexPrecedes a b then taggedHash "TapBranch" (a ++ b) else taggedHash "TapBranch" (b ++ a)

/-- BIP341 taproot_tree_helper: the root hash and, for every leaf (in-order), its version, script and
bottom-up sibling path. -/
def hashes : Tree → ByteArray × List (UInt8 × ByteArray × List ByteArray)
  | .leaf v s => (leafHash v s, [(v, s, [])])
  | .branch l r =>
    let (lr, ll) := hashes l
    let (rr, rl) := hashes r
    (branchHash lr rr, ll.map (fun (v, s, p) => (v, s, p ++ [rr])) ++ rl.map (fun (v, s, p) => (v, s, p ++ [lr])))

def merkleRoot (t : Tree) : ByteArray := (hashes t).1

/-- TapTweak hash: H_TapTweak(internalKey || merkleRoot), or H_TapTweak(internalKey) without a tree. -/
def tweak (internalKey : ByteArray) (merkleRoot : Option ByteArray) : ByteArray :=
  taggedHash "TapTweak" (internalKey ++ merkleRoot.getD .empty)

/-- Tweaked output key Q = P + H_TapTweak(P || root)·G and its Y parity. -/
def tweakedOutputKey (internalKey : ByteArray) (merkleRoot : Option ByteArray := none) :
    Except TaprootError (ByteArray × Bool) := do
  if internalKey.size != 32 then throw .invalidInternalKey
  match xonlyAdd internalKey (tweak internalKey merkleRoot) with
  | .ok r => pure r
  | .error _ => throw .tweakFailed

/-- P2TR scriptPubKey: OP_1 <32-byte output key>. -/
def scriptPubKey (internalKey : ByteArray) (merkleRoot : Option ByteArray := none) : Except TaprootError ByteArray := do
  return ByteArray.mk #[0x51, 0x20] ++ (← tweakedOutputKey internalKey merkleRoot).1

/-- Control blocks for every leaf of the tree, in order. -/
def controlBlocks (internalKey : ByteArray) (tree : Tree) : Except TaprootError (List ControlBlock) := do
  let root := merkleRoot tree
  let (_, parity) ← tweakedOutputKey internalKey (some root)
  return (hashes tree).2.map fun (v, _, p) => { leafVersion := v, outputKeyParity := parity, internalKey, path := p }

/-- Control block for the leaf with the given in-order index. -/
def controlBlock (internalKey : ByteArray) (tree : Tree) (leafIndex : Int) : Except TaprootError ControlBlock := do
  let blocks ← controlBlocks internalKey tree
  if leafIndex < 0 || leafIndex ≥ blocks.length then throw .leafNotFound
  return blocks[leafIndex.toNat]!

/-- Verifies a control block against a merkle root by walking the path bottom-up. -/
def verify (cb : ControlBlock) (script : ByteArray) (merkleRoot : ByteArray) : Bool :=
  cb.path.foldl branchHash (leafHash cb.leafVersion script) == merkleRoot

/-- The BIP341 NUMS internal key H = lift_x(SHA256(uncompressed SEC encoding of G)). -/
def unspendableInternalKey : ByteArray :=
  match publicKeyOf (Secp.toBE32 1) (compressed := false) with
  | .ok g => sha256 g
  | .error _ => .empty

end Taproot
end Winnow.Keys
