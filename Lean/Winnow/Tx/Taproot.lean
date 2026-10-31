import Secp.Keys
import Winnow.Crypto
import Winnow.Tx.Script

/-! # The BIP341 pieces the Tx area needs

`Script/Taproot.swift` is not part of the Tx area; this is the subset of it that FundingSources,
`SighashBIP341.ScriptPath(leafScript:)` and PSBT's tap-leaf fields use: the control block, the
TapLeaf/TapBranch/TapTweak hashes and the tweaked output key. It lives in `Winnow.Tx.Taproot` so as not
to collide with a full port of `Taproot.swift` elsewhere. -/

namespace Winnow.Tx.Taproot

/-- Leaf version for BIP342 tapscript leaves. -/
def leafVersion : UInt8 := 0xC0

structure ControlBlock where
  leafVersion : UInt8
  outputKeyParity : Bool
  internalKey : ByteArray
  path : Array ByteArray
  deriving Inhabited

instance : BEq ControlBlock := ⟨fun a b => a.leafVersion == b.leafVersion && a.outputKeyParity == b.outputKeyParity &&
  a.internalKey == b.internalKey && a.path == b.path⟩

namespace ControlBlock

def serialized (c : ControlBlock) : ByteArray :=
  c.path.foldl (· ++ ·) (ByteArray.mk #[c.leafVersion ||| (if c.outputKeyParity then 1 else 0)] ++ c.internalKey)

/-- `ControlBlock(serialized:)`: 33 + 32m bytes with m ≤ 128 (`invalidControlBlock` otherwise). -/
def parse? (b : ByteArray) : Option ControlBlock :=
  if b.size ≥ 33 && (b.size - 33) % 32 == 0 && (b.size - 33) / 32 ≤ 128 then
    let c := b[0]!
    some { leafVersion := c &&& 0xFE, outputKeyParity := c &&& 1 != 0, internalKey := b.extract 1 33,
           path := (List.range ((b.size - 33) / 32)).toArray.map fun i => b.extract (33 + 32 * i) (65 + 32 * i) }
  else none

end ControlBlock

/-- H_TapLeaf(leafVersion ‖ CompactSize(script length) ‖ script). -/
def leafHash (version : UInt8 := leafVersion) (script : Script) : ByteArray :=
  taggedHash "TapLeaf" (ByteArray.mk #[version] ++ varBytes script.bytes)

/-- TapBranch hash of the lexicographically sorted pair. -/
def branchHash (a b : ByteArray) : ByteArray :=
  if bytesLt a b then taggedHash "TapBranch" (a ++ b) else taggedHash "TapBranch" (b ++ a)

def tweak (internalKey : ByteArray) (merkleRoot : Option ByteArray) : ByteArray :=
  taggedHash "TapTweak" (internalKey ++ merkleRoot.getD .empty)

/-- Q = P + H_TapTweak(P ‖ root)·G and its y parity; `none` where the Swift original throws
(`invalidInternalKey` for a key that is not 32 bytes, `tweakFailed` for one off the curve or a failed
tweak). -/
def tweakedOutputKey (internalKey : ByteArray) (merkleRoot : Option ByteArray := none) :
    Option (ByteArray × Bool) :=
  if internalKey.size != 32 then none
  else
    match Secp.parseXOnly internalKey with
    | .error _ => none
    | .ok (x, y) =>
      match Secp.xonlyAdd x y (tweak internalKey merkleRoot) with
      | .ok (qx, qy) => some (Secp.toBE32 qx.toNat, qy.isOdd)
      | .error _ => none

end Winnow.Tx.Taproot
