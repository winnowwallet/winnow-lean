import Winnow.Keys.BIP32

/-! # BIP86 single-key Taproot derivation (port of `Keys/BIP86.swift`)

`tweakedOutputKey` and `tweakedPrivateKey` let P256K's errors escape, and `address` adds Bech32's:
`BIP86Error` is the union of what the Swift functions can throw. -/

namespace Winnow.Keys

inductive BIP86Error where
  | bip32 (e : BIP32Error)
  | p256k (e : P256KError)
  | bech32 (e : Bech32Error)

def BIP86Error.name : BIP86Error → String
  | .bip32 e => e.name | .p256k e => e.name | .bech32 e => e.name

namespace BIP86

/-- The account-level extended key at m/86'/coinType'/account'. -/
def accountKey (master : HDKey) (coinType : UInt32 := 0) (account : UInt32 := 0) : Except BIP32Error HDKey :=
  master.derived s!"m/86'/{coinType}'/{account}'"

/-- 32-byte x-only internal public key of any HD key. -/
def xonlyPublicKey (key : HDKey) : ByteArray := key.publicKey.extract 1 key.publicKey.size

/-- The 32-byte Taproot internal key at m/86'/coinType'/account'/change/index. -/
def internalKey (master : HDKey) (coinType : UInt32 := 0) (account : UInt32 := 0) (change : UInt32 := 0)
    (index : UInt32) : Except BIP32Error ByteArray := do
  let key ← master.derived s!"m/86'/{coinType}'/{account}'/{change}/{index}"
  return xonlyPublicKey key

/-- BIP341 taptweak with no script tree: Q = P + H_taptweak(P)·G. -/
def tweakedOutputKey (internalKey : ByteArray) : Except P256KError ByteArray := do
  let t := taggedHash "TapTweak" internalKey
  return (← xonlyAdd internalKey t).1

/-- Tweaked private key matching `tweakedOutputKey` (key-path spending). -/
def tweakedPrivateKey (secret : ByteArray) : Except P256KError ByteArray := do
  let d ← secretOf secret
  let p ← pointOfSecret d
  let t := taggedHash "TapTweak" (xonlyBytes p)
  return Secp.toBE32 (← keypairXonlyAdd d t)

/-- BIP86 address: bech32m, witness v1, program = tweaked output key. -/
def address (internalKey : ByteArray) (hrp : String := "bc") : Except BIP86Error String := do
  let q ← (tweakedOutputKey internalKey).mapError .p256k
  (SegwitAddress.encode hrp 1 q).mapError .bech32

/-- P2TR scriptPubKey: OP_1 <32-byte output key>. -/
def scriptPubKey (internalKey : ByteArray) : Except P256KError ByteArray := do
  return ByteArray.mk #[0x51, 0x20] ++ (← tweakedOutputKey internalKey)

end BIP86
end Winnow.Keys
