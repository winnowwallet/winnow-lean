import Oracle.Base
import Winnow.Keys

/-! Oracle ops for the Keys area (Lean side of LeanOracle/Keys). -/

namespace Oracle
open Lean Winnow Winnow.Keys

/-! ## Request helpers -/

def optBytes (j : Json) (k : String) : Except String (Option ByteArray) :=
  match j.getObjVal? k with
  | .ok .null | .error _ => pure none
  | .ok _ => some <$> bytes j k

def bytesList (j : Json) (k : String) : Except String (List ByteArray) := do
  let xs ← j.getObjValAs? (List String) k
  xs.mapM fun s => match ofHex? s with
    | some b => pure b
    | none => throw s!"{k}: not hex"

def boolList (j : Json) (k : String) : Except String (List Bool) := j.getObjValAs? (List Bool) k
def bool (j : Json) (k : String) : Except String Bool := j.getObjValAs? Bool k
def int (j : Json) (k : String) : Except String Int := j.getObjValAs? Int k
def u32 (j : Json) (k : String) : Except String UInt32 := do return (← nat j k).toUInt32

def reply {ε α} (name : ε → String) (f : α → Json) : Except ε α → Json
  | .ok a => ok (f a)
  | .error e => err (name e)

def listJ (xs : List ByteArray) : Json := Json.arr (xs.map hexJ).toArray

/-! ## Shapes -/

def hdKeyJ (k : HDKey) : Json := Json.mkObj [
  ("xprv", Json.str (k.serialized .mainnet)), ("tprv", Json.str (k.serialized .testnet)),
  ("fingerprint", toJson k.fingerprint.toNat), ("depth", toJson k.depth.toNat),
  ("parentFingerprint", toJson k.parentFingerprint.toNat), ("childIndex", toJson k.childIndex.toNat),
  ("chainCode", hexJ k.chainCode), ("privateKey", match k.privateKey with | some s => hexJ s | none => Json.null),
  ("publicKey", hexJ k.publicKey)]

def hdKey (j : Json) (k : String := "key") : Except String (Except HDKeyParseError HDKey) := do
  return HDKey.deserialize (← str j k)

/-- Run on a key given as its serialization; a key that does not parse is a bad request. -/
def withKey (j : Json) (f : HDKey → Json) : Except String Json := do
  match ← hdKey j with
  | .ok k => pure (f k)
  | .error e => throw s!"key: {e.name}"

def secretJ (s : WalletSecret) : Json := match s with
  | .mnemonic w => Json.mkObj [("kind", "mnemonic"), ("value", Json.str w)]
  | .masterKey x => Json.mkObj [("kind", "xprv"), ("value", Json.str x)]
  | .accountKey x fp => Json.mkObj [("kind", "account"), ("value", Json.str x), ("fingerprint", Json.num fp.toNat)]

def walletSecret (j : Json) : Except String WalletSecret := do
  let v ← str j "value"
  match ← str j "kind" with
  | "mnemonic" => pure (.mnemonic v)
  | "xprv" => pure (.masterKey v)
  | "account" => pure (.accountKey v (← nat j "fingerprint").toUInt32)
  | k => throw s!"kind {k}"

partial def tree (j : Json) : Except String Taproot.Tree := do
  match j.getObjVal? "leaf" with
  | .ok l => return .leaf (← nat l "version").toUInt8 (← bytes l "script")
  | .error _ =>
    let bs ← j.getObjValAs? (Array Json) "branch"
    if bs.size != 2 then throw "branch: two subtrees"
    return .branch (← tree bs[0]!) (← tree bs[1]!)

def controlBlockJ (c : Taproot.ControlBlock) : Json := Json.mkObj [
  ("leafVersion", toJson c.leafVersion.toNat), ("parity", toJson c.outputKeyParity),
  ("internalKey", hexJ c.internalKey), ("path", listJ c.path), ("serialized", hexJ c.serialized)]

def pointJ (data : ByteArray) (p : Point) : Json := Json.mkObj [
  ("data", hexJ data), ("uncompressed", hexJ (serializeUncompressed p)),
  ("xonly", hexJ (xonlyBytes p)), ("parity", toJson (hasOddY p))]

def p256k {α} (f : α → Json) (r : PK α) : Json := reply P256KError.name f r

def keystoreRun (steps : Array Json) : Except String Json := do
  let mut st : InMemorySecrets := {}
  let mut out : Array Json := #[]
  let ks : KeyStore (StateM InMemorySecrets) := InMemoryKeyStore
  for s in steps do
    let id ← str s "id"
    let act : ExceptT KeyStoreError (StateM InMemorySecrets) Json ← match ← str s "do" with
      | "store" => do let w ← walletSecret s; pure (do ks.store w id; pure Json.null)
      | "load" => pure (secretJ <$> ks.load id)
      | "delete" => pure (do ks.delete id; pure Json.null)
      | "upgrade" => pure (toJson <$> ks.upgradeProtection id)
      | d => throw s!"do {d}"
    let (r, st') := (act.run).run st
    st := st'
    out := out.push (reply KeyStoreError.name (fun x => x) r)
  return ok (Json.arr out)

def keysOps : List (String × Handler) := [
  -- secp256k1 through P256K
  ("p256k.privateKey", fun j => do
    let s ← bytes j "secret"
    return p256k id do
      let p ← pointOfSecret (← secretOf s)
      pure (pointJ (serializeCompressed p) p)),
  ("p256k.publicKey", fun j => do
    let b ← bytes j "data"
    return p256k (pointJ b) (parsePublicKey b (← bool j "compressed"))),
  ("p256k.privateAdd", fun j => do
    let s ← bytes j "secret"; let t ← bytes j "tweak"
    return p256k (hexJ ∘ Secp.toBE32) (do privateAdd (← secretOf s) t)),
  ("p256k.privateMultiply", fun j => do
    let s ← bytes j "secret"; let t ← bytes j "tweak"
    return p256k (hexJ ∘ Secp.toBE32) (do privateMultiply (← secretOf s) t)),
  ("p256k.privateNegate", fun j => do
    let s ← bytes j "secret"
    return p256k (hexJ ∘ Secp.toBE32) (do pure (privateNegate (← secretOf s)))),
  ("p256k.publicAdd", fun j => do
    let k ← bytes j "publicKey"; let t ← bytes j "tweak"
    return p256k (hexJ ∘ serializeCompressed) (do publicAdd (← parsePublicKey k) t)),
  ("p256k.publicMultiply", fun j => do
    let k ← bytes j "publicKey"; let t ← bytes j "tweak"
    return p256k (hexJ ∘ serializeCompressed) (do publicMultiply (← parsePublicKey k) t)),
  ("p256k.publicNegate", fun j => do
    let k ← bytes j "publicKey"
    return p256k (hexJ ∘ serializeCompressed) (do pure (publicNegate (← parsePublicKey k)))),
  ("p256k.combine", fun j => do
    let ks ← bytesList j "keys"
    return p256k (hexJ ∘ serializeCompressed) (do combine (← ks.mapM (parsePublicKey ·)))),
  ("p256k.xonlyAdd", fun j => do
    let x ← bytes j "xonly"; let t ← bytes j "tweak"
    return p256k (fun (k, par) => Json.mkObj [("key", hexJ k), ("parity", toJson par)]) (xonlyAdd x t)),
  ("p256k.schnorrPrivateAdd", fun j => do
    let s ← bytes j "secret"; let t ← bytes j "tweak"
    return p256k (hexJ ∘ Secp.toBE32) (do keypairXonlyAdd (← secretOf s) t)),
  ("p256k.schnorrSign", fun j => do
    let s ← bytes j "secret"; let m ← bytes j "message"; let a ← bytes j "aux"
    return p256k hexJ (do schnorrSign (← secretOf s) m a)),
  ("p256k.schnorrVerify", fun j => do
    return p256k toJson (schnorrVerify (← bytes j "xonly") (← bytes j "message") (← bytes j "signature"))),
  -- BIP32
  ("bip32.fromSeed", fun j => do return reply BIP32Error.name hdKeyJ (HDKey.ofSeed (← bytes j "seed"))),
  ("bip32.deserialize", fun j => do return reply HDKeyParseError.name hdKeyJ (HDKey.deserialize (← str j "text"))),
  ("bip32.neutered", fun j => withKey j (fun k => ok (hdKeyJ k.neutered))),
  ("bip32.child", fun j => do
    let i ← u32 j "index"
    withKey j fun k => reply BIP32Error.name hdKeyJ (k.child i)),
  ("bip32.derive", fun j => do
    let p ← str j "path"
    withKey j fun k => reply BIP32Error.name hdKeyJ (k.derived p)),
  -- BIP39
  ("bip39.mnemonic", fun j => do return reply BIP39Error.name Json.str (BIP39.mnemonic (← bytes j "entropy"))),
  ("bip39.validate", fun j => do
    return reply BIP39Error.name (fun _ => Json.bool true) (BIP39.validate (← str j "mnemonic"))),
  ("bip39.seed", fun j => do return ok (hexJ (BIP39.seed (← str j "mnemonic") (← str j "passphrase")))),
  ("bip39.word", fun j => do
    let i ← nat j "index"
    if i ≥ 2048 then throw "index" else return ok (Json.str BIP39.wordlist[i]!)),
  -- BIP86
  ("bip86.internalKey", fun j => do
    let (c, a, ch, i) := (← u32 j "coinType", ← u32 j "account", ← u32 j "change", ← u32 j "index")
    withKey j fun k => reply BIP32Error.name hexJ (BIP86.internalKey k c a ch i)),
  ("bip86.accountKey", fun j => do
    let (c, a) := (← u32 j "coinType", ← u32 j "account")
    withKey j fun k => reply BIP32Error.name hdKeyJ (BIP86.accountKey k c a)),
  ("bip86.xonlyPublicKey", fun j => withKey j (fun k => ok (hexJ (BIP86.xonlyPublicKey k)))),
  ("bip86.tweakedOutputKey", fun j => do return p256k hexJ (BIP86.tweakedOutputKey (← bytes j "internalKey"))),
  ("bip86.tweakedPrivateKey", fun j => do return p256k hexJ (BIP86.tweakedPrivateKey (← bytes j "secret"))),
  ("bip86.address", fun j => do
    return reply BIP86Error.name Json.str (BIP86.address (← bytes j "internalKey") (← str j "hrp"))),
  ("bip86.scriptPubKey", fun j => do return p256k hexJ (BIP86.scriptPubKey (← bytes j "internalKey"))),
  -- Key store
  ("walletSecret.serialize", fun j => do return ok (hexJ (← walletSecret j).serialized)),
  ("walletSecret.parse", fun j => do return reply KeyStoreError.name secretJ (WalletSecret.parse (← bytes j "data"))),
  ("keystore.run", fun j => do keystoreRun (← j.getObjValAs? (Array Json) "steps")),
  ("keystore.errorDescription", fun j => do
    let e : KeyStoreError ← match ← str j "case" with
      | "notFound" => pure (.notFound (← str j "walletID"))
      | "alreadyExists" => pure (.alreadyExists (← str j "walletID"))
      | "malformedSecret" => pure .malformedSecret
      | "keychain" => pure (.keychain (← int j "status").toInt32)
      | c => throw s!"case {c}"
    match e.errorDescription with
    | some d => return ok (Json.str d)
    | none => throw "keychain status described by the Security framework"),
  -- Taproot
  ("taproot.leafHash", fun j => do return ok (hexJ (Taproot.leafHash (← nat j "version").toUInt8 (← bytes j "script")))),
  ("taproot.branchHash", fun j => do return ok (hexJ (Taproot.branchHash (← bytes j "a") (← bytes j "b")))),
  ("taproot.merkleRoot", fun j => do return ok (hexJ (Taproot.merkleRoot (← tree (← j.getObjVal? "tree"))))),
  ("taproot.tweak", fun j => do return ok (hexJ (Taproot.tweak (← bytes j "internalKey") (← optBytes j "merkleRoot")))),
  ("taproot.tweakedOutputKey", fun j => do
    return reply TaprootError.name (fun (k, par) => Json.mkObj [("key", hexJ k), ("parity", toJson par)])
      (Taproot.tweakedOutputKey (← bytes j "internalKey") (← optBytes j "merkleRoot"))),
  ("taproot.scriptPubKey", fun j => do
    return reply TaprootError.name hexJ (Taproot.scriptPubKey (← bytes j "internalKey") (← optBytes j "merkleRoot"))),
  ("taproot.controlBlocks", fun j => do
    return reply TaprootError.name (fun cs => Json.arr (cs.map controlBlockJ).toArray)
      (Taproot.controlBlocks (← bytes j "internalKey") (← tree (← j.getObjVal? "tree")))),
  ("taproot.controlBlock", fun j => do
    return reply TaprootError.name controlBlockJ
      (Taproot.controlBlock (← bytes j "internalKey") (← tree (← j.getObjVal? "tree")) (← int j "leafIndex"))),
  ("taproot.controlBlock.parse", fun j => do
    return reply TaprootError.name controlBlockJ (Taproot.ControlBlock.parse (← bytes j "data"))),
  ("taproot.verify", fun j => do
    let cb ← match Taproot.ControlBlock.parse (← bytes j "controlBlock") with
      | .ok c => pure c
      | .error _ => throw "controlBlock"
    return ok (toJson (Taproot.verify cb (← bytes j "script") (← bytes j "merkleRoot")))),
  ("taproot.unspendableInternalKey", fun _ => return ok (hexJ Taproot.unspendableInternalKey))
]

end Oracle
