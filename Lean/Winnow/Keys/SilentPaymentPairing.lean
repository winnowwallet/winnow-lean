import Winnow.Keys.SilentPayments
import Winnow.Keys.BIP32

/-! # A silent payment address and a tweak for one person (issue #94, `docs/out-of-band-payments.md`)

A BIP352 payment's address depends on the payer's coins: the payer multiplies the recipient's scan key by
`input_hash·a`, a number made from the inputs being spent, and the recipient can only find the output by
doing the same for every transaction on the chain. Here the recipient hands one person, once, their silent
payment address and a tweak `x`, and the payer uses `x` where BIP352 has `input_hash·a`:

```
shared = x·B_scan                                            BIP352: (input_hash·a)·B_scan
t_i    = hash_BIP0352/SharedSecret(ser_P(shared) ‖ ser32(i))  BIP352's own step (`outputScript`)
P_i    = B_spend + t_i·G                                      script 0x51 0x20 x(P_i)
```

Nothing after the first line differs from a silent payment, and it is `SilentPaymentSending.outputScript`
that computes it. Since no input enters, the recipient knows every `P_i` before it is paid and watches for
them as for any address: no scan of the chain, and no word from the payer. `i` counts the person's payments
(not one transaction's outputs). The recipient spends with `b_spend + t_i`; the payer, who holds `x` and the
address, can derive every `P_i` and never has `b_spend`. A standard silent payment scan does not find
these outputs: they are found by knowing `x`.

The tweak for person `k` is `x_k = hash_Winnow/SilentPayment/Pairing(b_scan ‖ ser32(k))`, so the wallet's
phrase gives every tweak it ever handed out. The scan and spend keys are at BIP352's own paths,
`m/352'/coin'/0'/1'/0` and `m/352'/coin'/0'/0'/0`, which need the master key: a wallet that holds only its
account key has neither.

Nothing here reads the wallet; `card-keys-test` holds it to vectors an independent implementation wrote
(`scripts/card-keys-vectors`). The curve work is `Secp256k1`, which is not constant-time. -/

namespace Winnow

/-- What one person is handed: the recipient's silent payment address and the tweak made for them. The tweak
is not a spending secret: whoever holds both can find the payments made with them and cannot spend them. -/
structure PairingCard where
  address : SilentPaymentAddress
  /-- 32 bytes, a valid scalar. -/
  tweak : ByteArray
  deriving BEq, Inhabited

namespace Keys

namespace SilentPaymentPairing

inductive Error where
  /-- the address's keys are not points -/
  | invalidAddress
  /-- the tweak is not 32 bytes of a valid scalar, or an output's tweak hashed to 0 or past the group order -/
  | invalidTweak
  | invalidPrivateKey
  /-- the private key is not the one the address's spend key belongs to -/
  | keyMismatch
  /-- the key cannot derive BIP352's paths (a public key, or one too deep) -/
  | derivation
  deriving Repr, BEq, DecidableEq

def Error.name : Error → String
  | .invalidAddress => "invalidAddress" | .invalidTweak => "invalidTweak" | .invalidPrivateKey => "invalidPrivateKey"
  | .keyMismatch => "keyMismatch" | .derivation => "derivation"

abbrev PP := Except Error

def pairingTag : String := "Winnow/SilentPayment/Pairing"

def ser32 (i : UInt32) : ByteArray :=
  ByteArray.mk #[(i >>> 24).toUInt8, (i >>> 16).toUInt8, (i >>> 8).toUInt8, i.toUInt8]

def isValidTweak (tweak : ByteArray) : Bool := isValidSecret tweak

/-- `x·B_scan`, compressed: what a silent payment's `ecdh_shared_secret` is, with the tweak in place of
`input_hash·a`. Public: the recipient needs no key for it, having made `x`. -/
def sharedSecret (c : PairingCard) : PP ByteArray := do
  unless isValidTweak c.tweak do throw .invalidTweak
  let scan ← match parsePublicKey c.address.scanKey with
    | .ok p => pure p
    | .error _ => throw .invalidAddress
  match publicMultiply scan c.tweak with
  | .ok p => pure (serializeCompressed p)
  | .error _ => throw .invalidTweak

/-- `t_i`: 32 bytes, a valid scalar (BIP352's output tweak for the shared secret at `k = i`). -/
def outputTweak (c : PairingCard) (i : UInt32) : PP ByteArray := do
  let t := taggedHash "BIP0352/SharedSecret" ((← sharedSecret c) ++ ser32 i)
  unless isValidSecret t do throw .invalidTweak
  return t

/-- The P2TR scriptPubKey of the person's payment `i`: BIP352's output for the shared secret. -/
def scriptPubKey (c : PairingCard) (i : UInt32) : PP ByteArray := do
  match SilentPaymentSending.outputScript (← sharedSecret c) c.address.spendKey i with
  | .ok script => pure script
  | .error .invalidTweak => throw .invalidTweak
  | .error _ => throw .invalidAddress

/-- `b_spend + t_i mod n`, the key that signs for `P_i`: only for the secret the address's spend key is of. -/
def spendSecret (spend : ByteArray) (c : PairingCard) (i : UInt32) : PP ByteArray := do
  let b ← match secretOf spend with
    | .ok d => pure d
    | .error _ => throw .invalidPrivateKey
  match publicKeyOf spend with
  | .ok k => unless k == c.address.spendKey do throw .keyMismatch
  | .error _ => throw .invalidPrivateKey
  let t ← outputTweak c i
  match privateAdd b t with
  | .ok p => pure (Secp.toBE32 p)
  | .error _ => throw .invalidTweak

/-! ## Where the keys and the tweaks come from -/

/-- The scan and spend private keys of BIP352's account 0: `m/352'/coin'/0'/1'/0` and `m/352'/coin'/0'/0'/0`. -/
def keys (master : HDKey) (coinType : UInt32) : PP (ByteArray × ByteArray) := do
  let secretAt (path : String) : PP ByteArray :=
    match master.derived path with
    | .ok k => match k.privateKey with
      | some s => pure s
      | none => throw .derivation
    | .error _ => throw .derivation
  return (← secretAt s!"m/352'/{coinType}'/0'/1'/0", ← secretAt s!"m/352'/{coinType}'/0'/0'/0")

/-- The address those keys make, with `hrp` (`sp`, or `tsp` on the test networks). -/
def address (scan spend : ByteArray) (hrp : String) : PP SilentPaymentAddress := do
  let pub (s : ByteArray) : PP ByteArray := match publicKeyOf s with
    | .ok k => pure k
    | .error _ => throw .invalidPrivateKey
  match SilentPaymentAddress.make (← pub scan) (← pub spend) hrp with
  | .ok a => pure a
  | .error _ => throw .invalidAddress

/-- Person `k`'s tweak: a hash of the scan private key and `k`, refused when it is 0 or past the group order
(about one `k` in 2^128), so the phrase gives back every tweak the wallet handed out. -/
def tweakFor (scan : ByteArray) (k : UInt32) : PP ByteArray := do
  unless isValidSecret scan do throw .invalidPrivateKey
  let x := taggedHash pairingTag (scan ++ ser32 k)
  unless isValidTweak x do throw .invalidTweak
  return x

/-- Person `k`'s card from the master key: the wallet's address and their tweak. -/
def issue (master : HDKey) (coinType : UInt32) (hrp : String) (k : UInt32) : PP PairingCard := do
  let (scan, spend) ← keys master coinType
  return { address := ← address scan spend hrp, tweak := ← tweakFor scan k }

end SilentPaymentPairing

end Keys
end Winnow
