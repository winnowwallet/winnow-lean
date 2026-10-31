import Winnow.Keys.Secp256k1

/-! # BIP32 hierarchical deterministic keys (port of `Keys/BIP32.swift`)

**Not constant-time.** Private child derivation adds scalars as `Nat`s (GMP-backed, value-dependent timing)
and computes public keys through `Secp`'s bit-by-bit scalar multiplication, so its timing depends on the
private key. Correct by lockstep against the Swift original (`oracle-keys`). That is acceptable for what
Winnow does with it: low-volume signing the user approves, on the user's own device, where no one can
trigger operations on demand or time them. Do not reuse it in servers, signing services, shared hosts, or
anything that signs on someone else's request (SECURITY.md, "Timing side channels"). -/

namespace Winnow.Keys

inductive BIP32Error where
  | invalidSeed | invalidPath | hardenedDerivationFromPublicKey | derivationFailed
  | invalidSerializedKey | invalidVersion
  /-- The key is at depth 255, and a byte counts no deeper. -/
  | depthExhausted
  deriving Repr, DecidableEq, Inhabited

def BIP32Error.name : BIP32Error → String
  | .invalidSeed => "invalidSeed" | .invalidPath => "invalidPath"
  | .hardenedDerivationFromPublicKey => "hardenedDerivationFromPublicKey"
  | .derivationFailed => "derivationFailed" | .invalidSerializedKey => "invalidSerializedKey"
  | .invalidVersion => "invalidVersion" | .depthExhausted => "depthExhausted"

/-- `HDKey.deserialize` throws Base58Check's errors as they are, and BIP32's own. -/
inductive HDKeyParseError where
  | base58 (e : Base58Error)
  | bip32 (e : BIP32Error)

def HDKeyParseError.name : HDKeyParseError → String
  | .base58 e => e.name
  | .bip32 e => e.name

/-- BIP32 hierarchical deterministic key (secp256k1). -/
structure HDKey where
  depth : UInt8
  parentFingerprint : UInt32
  childIndex : UInt32
  chainCode : ByteArray
  /-- 32 bytes, `none` for neutered keys. -/
  privateKey : Option ByteArray
  /-- 33 bytes, compressed. -/
  publicKey : ByteArray
  deriving Inhabited

namespace HDKey

def hardenedOffset : UInt32 := 0x8000_0000

/-- Serialization version (mainnet xprv/xpub, testnet tprv/tpub). -/
inductive Network where
  | mainnet | testnet
  deriving Repr, DecidableEq

def Network.privateVersion : Network → UInt32
  | .mainnet => 0x0488_ADE4 | .testnet => 0x0435_8394
def Network.publicVersion : Network → UInt32
  | .mainnet => 0x0488_B21E | .testnet => 0x0435_87CF

def isPrivate (k : HDKey) : Bool := k.privateKey.isSome

/-- Master key from a BIP39 seed: HMAC-SHA512(key="Bitcoin seed", seed). -/
def ofSeed (seed : ByteArray) : Except BIP32Error HDKey := do
  let i := hmacSha512 "Bitcoin seed".toUTF8 seed
  let secret := i.extract 0 32
  let chain := i.extract 32 64
  match publicKeyOf secret with
  | .error _ => throw .invalidSeed
  | .ok pub => return { depth := 0, parentFingerprint := 0, childIndex := 0, chainCode := chain,
                        privateKey := some secret, publicKey := pub }

/-- HASH160 fingerprint of the compressed public key (first 4 bytes, big-endian). -/
def fingerprint (k : HDKey) : UInt32 := (readBE (hash160 k.publicKey) 0 4).toUInt32

/-- The neutered (public-only) form of this key. -/
def neutered (k : HDKey) : HDKey := { k with privateKey := none }

/-- Child key derivation at a single index (≥ `hardenedOffset` for hardened). -/
def child (k : HDKey) (index : UInt32) : Except BIP32Error HDKey := do
  if k.depth == 255 then throw .depthExhausted
  let hardened := index ≥ hardenedOffset
  let data ← if hardened then
      match k.privateKey with
      | none => throw .hardenedDerivationFromPublicKey
      | some sk => pure (ByteArray.mk #[0] ++ sk)
    else pure k.publicKey
  let i := hmacSha512 k.chainCode (data ++ u32BE index)
  let tw := i.extract 0 32
  let childChain := i.extract 32 64
  let derived : PK HDKey := do
    match k.privateKey with
    | some sk =>
      let s ← privateAdd (← secretOf sk) tw
      let childSecret := toBE32' s
      return { depth := k.depth + 1, parentFingerprint := k.fingerprint, childIndex := index,
               chainCode := childChain, privateKey := some childSecret,
               publicKey := ← publicKeyOf childSecret }
    | none =>
      let p ← publicAdd (← parsePublicKey k.publicKey) tw
      return { depth := k.depth + 1, parentFingerprint := k.fingerprint, childIndex := index,
               chainCode := childChain, privateKey := none, publicKey := serializeCompressed p }
  match derived with
  | .ok c => pure c
  | .error _ => throw .derivationFailed
where toBE32' (s : Nat) : ByteArray := Secp.toBE32 s

/-- Swift's `UInt32(String)`: an optional `+` or `-` sign and ASCII digits; `-` only for zero. -/
def parseUInt32 (s : String) : Option UInt32 :=
  let cs := s.toList
  let (neg, digits) := match cs with
    | '+' :: r => (false, r)
    | '-' :: r => (true, r)
    | r => (false, r)
  if digits.isEmpty || !digits.all Char.isDigit then none else
  let v := digits.foldl (fun acc c => acc * 10 + (c.toNat - '0'.toNat)) 0
  if neg then (if v == 0 then some 0 else none)
  else if v < 2 ^ 32 then some v.toUInt32 else none

/-- Derives along a path like "m/84'/0'/0'/0/0" (also accepts h/H suffixes). Empty components are
skipped, as Swift's `split` drops them. -/
def derived (k : HDKey) (path : String) : Except BIP32Error HDKey := do
  let comps := (path.splitOn "/").filter (· ≠ "")
  let comps := match comps with
    | c :: r => if c == "m" || c == "M" then r else c :: r
    | [] => []
  -- Every component is read before any child is derived (upstream 1cf93fb), so a bad component is
  -- `invalidPath` even after a step that would exhaust the depth.
  let mut indices : Array UInt32 := #[]
  for c in comps do
    let hardened := c.endsWith "'" || c.endsWith "h" || c.endsWith "H"
    let digits := if hardened then String.ofList c.toList.dropLast else c
    match parseUInt32 digits with
    | some index =>
      if index ≥ hardenedOffset then throw .invalidPath
      indices := indices.push (index + (if hardened then hardenedOffset else 0))
    | none => throw .invalidPath
  indices.foldlM (fun key i => key.child i) k

/-- `derived(path: [UInt32])`: derives along already-numeric child indices (hardened ones carry
`hardenedOffset`). -/
def derivedPath (k : HDKey) (path : Array UInt32) : Except BIP32Error HDKey :=
  path.foldlM (fun key i => key.child i) k

/-- Base58Check serialization (78-byte payload: version/depth/fingerprint/index/chain/key). -/
def serialized (k : HDKey) (network : Network := .mainnet) : String :=
  let version := if k.isPrivate then network.privateVersion else network.publicVersion
  let keyPart := match k.privateKey with
    | some sk => ByteArray.mk #[0] ++ sk
    | none => k.publicKey
  Base58Check.encode (u32BE version ++ ByteArray.mk #[k.depth] ++ u32BE k.parentFingerprint ++
    u32BE k.childIndex ++ k.chainCode ++ keyPart)

/-- Parses a Base58Check-serialized extended key, validating version, key material, and the master-key
invariants (zero depth implies zero fingerprint/index). -/
def deserialize (s : String) : Except HDKeyParseError HDKey := do
  let payload ← (Base58Check.decode s).mapError .base58
  if payload.size != 78 then throw (.bip32 .invalidSerializedKey)
  let version := (readBE payload 0 4).toUInt32
  let depth := payload[4]!
  let parentFingerprint := (readBE payload 5 4).toUInt32
  let childIndex := (readBE payload 9 4).toUInt32
  let chainCode := payload.extract 13 45
  let keyData := payload.extract 45 78
  let known := [Network.mainnet.privateVersion, Network.mainnet.publicVersion,
                Network.testnet.privateVersion, Network.testnet.publicVersion]
  if !known.contains version then throw (.bip32 .invalidVersion)
  if depth == 0 && (parentFingerprint != 0 || childIndex != 0) then throw (.bip32 .invalidSerializedKey)
  if version == Network.mainnet.privateVersion || version == Network.testnet.privateVersion then
    if keyData[0]! != 0 then throw (.bip32 .invalidSerializedKey)
    let secret := keyData.extract 1 33
    match publicKeyOf secret with
    | .error _ => throw (.bip32 .invalidSerializedKey)
    | .ok pub => return { depth, parentFingerprint, childIndex, chainCode, privateKey := some secret,
                          publicKey := pub }
  else
    match parsePublicKey keyData with
    | .error _ => throw (.bip32 .invalidSerializedKey)
    | .ok _ => return { depth, parentFingerprint, childIndex, chainCode, privateKey := none,
                        publicKey := keyData }

end HDKey
end Winnow.Keys
