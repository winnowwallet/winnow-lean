import Winnow.Crypto
import Winnow.Keys.Secp256k1
import Winnow.Keys.BIP32

/-! # A card per person: the code and its derivation (issue #94, `docs/out-of-band-payments.md`)

The card everybody gets carries the wallet's account key, so each holder can derive every address the
wallet has. A card code is made for one person instead: a public key `B` and a seed `s`, both derived
from the wallet's seed along a hardened branch of the account key, so neither can be computed from the
account key the other card shares. The person pays the outputs

```
t_i = hash_Winnow/Card/Tweak(network ‖ B ‖ s ‖ ser32(i))     refused when 0 or ≥ n
P_i = B + t_i·G                                              script 0x51 0x20 x(P_i)
```

for i = 0, 1, 2, … and the issuer spends them with `b + t_i`. The payer knows every `t_i` and never `b`.
The output key is `P_i` itself with no BIP341 tweak on top, as a BIP352 output is. This is the shape of
BIP32's unhardened derivation with the chain code in the seed's place: the proposal compares the two.

Here: the code's bech32m codec (`CardCode`, modelled on `SilentPaymentAddress`), the derivation both
sides run, the issuer's spending secret, and where a card's key and seed come from below the account key.
The network is named by the code's HRP, one per network, and bound into every tweak. Nothing here reads
the wallet; `card-keys-test` holds it to vectors an independent implementation wrote
(`scripts/card-keys-vectors`). The curve work is `Secp256k1`, which is not constant-time. -/

namespace Winnow

inductive CardCodeError where
  /-- not a bech32m string -/
  | invalidEncoding
  | wrongHRP (expected actual : String)
  /-- a bech32m string whose HRP names no network's card code -/
  | unknownHRP (actual : String)
  /-- version 0 is the only one defined -/
  | unsupportedVersion (version : Nat)
  /-- the payload must be 65 bytes: a compressed key and a 32-byte seed -/
  | invalidDataLength (count : Nat)
  | invalidPublicKey
  /-- `convertBits` refused the payload -/
  | encoding (e : Bech32Error)
  deriving Repr, BEq, Inhabited

def CardCodeError.name : CardCodeError → String
  | .invalidEncoding => "invalidEncoding" | .wrongHRP .. => "wrongHRP" | .unknownHRP _ => "unknownHRP"
  | .unsupportedVersion _ => "unsupportedVersion" | .invalidDataLength _ => "invalidDataLength"
  | .invalidPublicKey => "invalidPublicKey" | .encoding e => e.name

/-- A card code: the issuer's compressed public key for one person, the seed that person derives payment
tweaks from, and the HRP that names the network. The seed is not a spending secret: whoever holds the code
can find the payments made to it and cannot spend them. -/
structure CardCode where
  key : ByteArray
  seed : ByteArray
  hrp : String
  deriving BEq, Inhabited

namespace CardCode

def version : Nat := 0
/-- A v0 code is at most 116 characters; the bound leaves later versions room, as BIP352's does. -/
def maxLength : Nat := 1023

def mainnetHRP : String := "wnc"
def signetHRP : String := "twnc"
def regtestHRP : String := "rwnc"

/-- The byte a tweak binds for the network an HRP names. -/
def networkByte (hrp : String) : Option UInt8 :=
  if hrp == mainnetHRP then some 0 else if hrp == signetHRP then some 1 else if hrp == regtestHRP then some 2 else none

/-- Shaped like a code (either case): routes text to this parser rather than the address decoder. A shape
check only. -/
def looksLikeCode (text : String) : Bool :=
  let lowered := text.trimAscii.toString.toLower
  [mainnetHRP, signetHRP, regtestHRP].any fun hrp => lowered.startsWith (hrp ++ "1")

def isValidPublicKey (key : ByteArray) : Bool := key.size == 33 && (Keys.parsePublicKey key).toBool

def make (key seed : ByteArray) (hrp : String) : Except CardCodeError CardCode := do
  unless (networkByte hrp).isSome do throw (.unknownHRP hrp)
  unless isValidPublicKey key do throw .invalidPublicKey
  unless seed.size == 32 do throw (.invalidDataLength (key.size + seed.size))
  return { key, seed, hrp }

/-- The bech32m encoding (`wnc1q…`, `twnc1q…`, `rwnc1q…`). -/
def encoded (c : CardCode) : Except Bech32Error String := do
  let data ← SegwitAddress.convertBits (c.key ++ c.seed).toList 8 5 true
  Bech32.encode c.hrp ((version.toUInt8) :: data) .bech32m maxLength

/-- Decodes and validates a code strictly: bech32m, a card HRP (`expectedHRP` when given), version 0, and
65 bytes of a valid compressed key and a seed. -/
def decode (s : String) (expectedHRP : Option String := none) : Except CardCodeError CardCode := do
  let (hrp, data, enc) ← match Bech32.decode s maxLength with
    | .ok r => pure r
    | .error _ => throw .invalidEncoding
  unless enc == .bech32m do throw .invalidEncoding
  if let some expected := expectedHRP then
    unless hrp == expected do throw (.wrongHRP expected hrp)
  unless (networkByte hrp).isSome do throw (.unknownHRP hrp)
  let some first := data.head? | throw .invalidEncoding
  unless first.toNat == version do throw (.unsupportedVersion first.toNat)
  let payload ← match SegwitAddress.convertBits data.tail 5 8 false with
    | .ok p => pure p
    | .error e => throw (.encoding e)
  unless payload.length == 65 do throw (.invalidDataLength payload.length)
  let bytes := ByteArray.mk payload.toArray
  make (bytes.extract 0 33) (bytes.extract 33 65) hrp

end CardCode

namespace Keys

namespace CardKeys

inductive Error where
  /-- the code's key is not a point, or its HRP names no network -/
  | invalidCode
  /-- the tweak hashed to 0 or past the group order (about one index in 2^128) -/
  | invalidTweak
  | invalidPrivateKey
  /-- the private key is not the one the code's public key belongs to -/
  | keyMismatch
  /-- a card index at or past the hardened offset, or a derivation the account key cannot make -/
  | derivation
  deriving Repr, BEq, DecidableEq

def Error.name : Error → String
  | .invalidCode => "invalidCode" | .invalidTweak => "invalidTweak" | .invalidPrivateKey => "invalidPrivateKey"
  | .keyMismatch => "keyMismatch" | .derivation => "derivation"

abbrev CK := Except Error

def tweakTag : String := "Winnow/Card/Tweak"
def seedTag : String := "Winnow/Card/Seed"

def ser32 (i : UInt32) : ByteArray :=
  ByteArray.mk #[(i >>> 24).toUInt8, (i >>> 16).toUInt8, (i >>> 8).toUInt8, i.toUInt8]

/-- `t_i`: 32 bytes, a valid scalar. The hash is not reduced: a value that is 0 or ≥ n is refused, so the
two sides can never disagree about what an index pays. -/
def tweak (c : CardCode) (i : UInt32) : CK ByteArray := do
  let some network := CardCode.networkByte c.hrp | throw .invalidCode
  unless c.key.size == 33 && c.seed.size == 32 do throw .invalidCode
  let t := taggedHash tweakTag (ByteArray.mk #[network] ++ c.key ++ c.seed ++ ser32 i)
  unless isValidSecret t do throw .invalidTweak
  return t

/-- `P_i = B + t_i·G`. -/
def outputKey (c : CardCode) (i : UInt32) : CK Point := do
  let t ← tweak c i
  let b ← match parsePublicKey c.key with
    | .ok p => pure p
    | .error _ => throw .invalidCode
  match pointOfSecret (Secp.fromBE t) >>= fun tg => combine [b, tg] with
  | .ok p => pure p
  | .error _ => throw .invalidTweak

/-- The P2TR scriptPubKey of payment `i`. -/
def scriptPubKey (c : CardCode) (i : UInt32) : CK ByteArray := do
  return ByteArray.mk #[0x51, 0x20] ++ xonlyBytes (← outputKey c i)

/-- `b + t_i mod n`, the key that signs for `P_i`: only for the `secret` whose public key is the code's. -/
def spendSecret (secret : ByteArray) (c : CardCode) (i : UInt32) : CK ByteArray := do
  let b ← match secretOf secret with
    | .ok d => pure d
    | .error _ => throw .invalidPrivateKey
  match publicKeyOf secret with
  | .ok k => unless k == c.key do throw .keyMismatch
  | .error _ => throw .invalidPrivateKey
  let t ← tweak c i
  match privateAdd b t with
  | .ok p => pure (Secp.toBE32 p)
  | .error _ => throw .invalidTweak

/-! ## Where a card comes from -/

/-- The hardened child of the account key under which cards live (0 and 1, unhardened, are the receive and
change chains). -/
def branch : UInt32 := 2

/-- Card `k`'s node, `account/2'/k'`. Both steps are hardened, so the account's public key (what the shared
card carries) derives none of it, and a wallet that holds only its account key can still make it. -/
def node (account : HDKey) (k : UInt32) : CK HDKey := do
  unless k < HDKey.hardenedOffset do throw .derivation
  match account.child (branch + HDKey.hardenedOffset) >>= (·.child (k + HDKey.hardenedOffset)) with
  | .ok n => pure n
  | .error _ => throw .derivation

/-- The seed of a card's node: a hash of its chain code, which is independent of its private key. -/
def seedOf (node : HDKey) : ByteArray := taggedHash seedTag node.chainCode

/-- Card `k`'s code on the network `hrp` names, and the private key `b` its coins are spent with. -/
def issue (account : HDKey) (k : UInt32) (hrp : String) : CK (CardCode × ByteArray) := do
  let n ← node account k
  let some secret := n.privateKey | throw .derivation
  match CardCode.make n.publicKey (seedOf n) hrp with
  | .ok c => pure (c, secret)
  | .error _ => throw .invalidCode

end CardKeys

end Keys
end Winnow
