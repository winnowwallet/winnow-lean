import Winnow.Keys.BIP32

/-! # BIP86 single-key Taproot derivation (port of `Keys/BIP86.swift`) -/

namespace Winnow.Keys

namespace BIP86

/-- The account-level extended key at m/86'/coinType'/account'. -/
def accountKey (master : HDKey) (coinType : UInt32 := 0) (account : UInt32 := 0) : Except BIP32Error HDKey :=
  master.derived s!"m/86'/{coinType}'/{account}'"

/-- 32-byte x-only internal public key of any HD key. -/
def xonlyPublicKey (key : HDKey) : ByteArray := key.publicKey.extract 1 key.publicKey.size

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

end BIP86
end Winnow.Keys
