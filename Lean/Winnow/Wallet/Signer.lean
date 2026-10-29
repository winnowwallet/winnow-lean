import Winnow.Keys
import Winnow.Tx.SighashBIP341
import Winnow.Tx.Multisig

/-! # Taproot signing

Port of `Sources/WalletCore/Transactions/Signer.swift`: key-path witnesses (BIP341/BIP340, the BIP86
tweaked key supplied by the caller), BIP342 script-path signatures and the BIP387 `multi_a` witness
stack. The Swift original draws fresh auxiliary randomness when none is given; here it is an argument
(`randomAuxiliaryRand` draws it in `IO`). -/

namespace Winnow
open Keys

inductive SignerError where
  | invalidPrivateKey
  | spentOutputCountMismatch (inputs spentOutputs : Nat)
  /-- No key for an input's spent scriptPubKey (hex). -/
  | missingKey (scriptPubKey : String)
  | malformedLeafScript
  deriving Inhabited

def SignerError.name : SignerError → String
  | .invalidPrivateKey => "invalidPrivateKey" | .spentOutputCountMismatch .. => "spentOutputCountMismatch"
  | .missingKey _ => "missingKey" | .malformedLeafScript => "malformedLeafScript"

/-- What signing can throw: the signer's errors, the sighash's, or the curve library's. -/
inductive SignFailure where
  | signer (e : SignerError)
  | sighash (e : SighashError)
  | crypto (e : P256KError)
  deriving Inhabited

def SignFailure.name : SignFailure → String
  | .signer e => e.name | .sighash e => e.name | .crypto e => e.name

namespace Signer

abbrev M := Except SignFailure

def randomAuxiliaryRand : IO ByteArray := IO.getRandomBytes 32

/-- A BIP340 signature with the hash-type byte appended unless SIGHASH_DEFAULT. -/
def signItem (sighash secret aux : ByteArray) (hashType : SighashBIP341.HashType) : M ByteArray := do
  let d ← match secretOf secret with
    | .ok d => pure d
    | .error _ => throw (.signer .invalidPrivateKey)
  let sig ← (schnorrSign d sighash aux).mapError .crypto
  return if hashType.rawValue != 0 then sig.push hashType.rawValue else sig

/-- The key-path witness (one item) for input `inputIndex`. -/
def witness (tx : Transaction) (inputIndex : Int) (spentOutputs : Array SighashBIP341.SpentOutput)
    (tweakedPrivateKey : ByteArray) (hashType : SighashBIP341.HashType := .default) (auxiliaryRand : ByteArray) :
    M (Array ByteArray) := do
  let sighash ← (SighashBIP341.sighash tx inputIndex spentOutputs hashType).mapError .sighash
  return #[← signItem sighash tweakedPrivateKey auxiliaryRand hashType]

/-- Signs every input; `privateKeyFor` maps a spent scriptPubKey to its tweaked secret. -/
def sign (tx : Transaction) (spentOutputs : Array SighashBIP341.SpentOutput) (hashType : SighashBIP341.HashType := .default)
    (auxiliaryRand : ByteArray) (privateKeyFor : ByteArray → Option ByteArray) : M Transaction := do
  unless tx.inputs.size == spentOutputs.size do
    throw (.signer (.spentOutputCountMismatch tx.inputs.size spentOutputs.size))
  let mut tx := tx
  for h : i in [0:tx.inputs.size] do
    let script := spentOutputs[i]!.scriptPubKey
    let some key := privateKeyFor script | throw (.signer (.missingKey (hex script)))
    let w ← witness tx i spentOutputs key hashType auxiliaryRand
    tx := { tx with inputs := tx.inputs.modify i fun inp => { inp with witness := w } }
  return tx

/-- A BIP342 script-path signature (untweaked key; the sighash commits to the leaf and the annex). -/
def scriptPathSignature (tx : Transaction) (inputIndex : Int) (spentOutputs : Array SighashBIP341.SpentOutput)
    (leafScript : Script) (leafVersion : UInt8 := Tx.Taproot.leafVersion) (hashType : SighashBIP341.HashType := .default)
    (annex : Option ByteArray := none) (privateKey : ByteArray) (auxiliaryRand : ByteArray) : M ByteArray := do
  let sighash ← (SighashBIP341.sighash tx inputIndex spentOutputs hashType
    (some (SighashBIP341.ScriptPath.ofLeaf leafScript leafVersion)) annex).mapError .sighash
  signItem sighash privateKey auxiliaryRand hashType

/-- The BIP387 witness: one item per script key in reverse script order (signature or empty), then the
leaf script and the control block. `signatures` maps x-only keys to signature items. -/
def multisigWitness (signatures : Array (ByteArray × ByteArray)) (leafScript : Script)
    (controlBlock : Tx.Taproot.ControlBlock) : Except SignerError (Array ByteArray) := do
  let some policy := Multisig.parsePolicy leafScript | throw .malformedLeafScript
  let keys := policy.keys
  let stack := keys.reverse.map fun k => ((signatures.find? (·.1 == k)).map (·.2)).getD .empty
  return (stack.push leafScript.bytes).push controlBlock.serialized

end Signer
end Winnow
