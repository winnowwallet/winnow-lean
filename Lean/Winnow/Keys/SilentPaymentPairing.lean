import Winnow.Keys.SilentPayments
import Winnow.Keys.BIP32

/-! # A shared secret and a spend key for one person (issue #94, `docs/out-of-band-payments.md`)

A BIP352 payment's address depends on the payer's coins: the payer multiplies the recipient's scan key by
`input_hash·a`, a number made from the inputs being spent, and the recipient can only find the output by
doing the same for every transaction on the chain. Here the recipient makes a tweak `x` for one person, once,
and `x` stands where BIP352 has `input_hash·a`:

```
shared = x·B_scan                                            BIP352: (input_hash·a)·B_scan
t_i    = hash_BIP0352/SharedSecret(ser_P(shared) ‖ ser32(i))  BIP352's own step (`outputScript`)
P_i    = B_spend + t_i·G                                      script 0x51 0x20 x(P_i)
```

Nothing after the first line differs from a silent payment, and it is `SilentPaymentSending.outputScript`
that computes it. Since no input enters, the recipient knows every `P_i` before it is paid and watches for
them as for any address: no scan of the chain, and no word from the payer. `i` counts the person's payments
(not one transaction's outputs). The recipient spends with `b_spend + t_i`; the payer, who is handed what
makes `shared`, can derive every `P_i` and never has `b_spend`. A standard silent payment scan does not find
these outputs: they are found by knowing `x`.

The tweak for person `k` is `x_k = hash_Winnow/SilentPayment/Pairing(b_scan ‖ ser32(k))`, so the wallet's
phrase gives every tweak it ever handed out. The scan and spend keys are at BIP352's own paths,
`m/352'/coin'/0'/1'/0` and `m/352'/coin'/0'/0'/0`, which need the master key: a wallet that holds only its
account key has neither.

## What a card carries: a code

The payer needs neither the scan key nor the tweak, only what the two make. So a card carries a code
(`CardCode`): the shared secret itself where a silent payment address has the scan key, and a spend key made
for that one person where it has the spend key.

```
S_k = x_k·B_scan                                               the shared secret, a point
L_k = hash_BIP0352/Label(b_scan ‖ ser32(k + 1))                 BIP352's label k + 1 (label 0 is its change label)
B_k = B_spend + L_k·G                                           BIP352's labelled spend key
P_i = B_k + hash_BIP0352/SharedSecret(ser_P(S_k) ‖ ser32(i))·G  the same step as above; spent with b_spend + L_k + t_i
```

The scan key, the spend key and the tweak never leave the wallet, and two codes of one wallet have no byte in
common: `(B_scan, B_k)` is the labelled silent payment address BIP352 would give that person, of which the
code holds the second half and, in place of the first, what the payer would have made from it.

A code is written like a silent payment address, bech32m over 66 bytes, under a prefix of Winnow's own
(`winnowcard1…`, `twinnowcard1…` on the test networks: `hrp`) and as version 1 (`winnowcard1p…`). Version 0
under that prefix (`winnowcard1q…`) is the wallet's own two keys, as the wallet's file and a backup record
them and as the cards of one release (0.9.12) carried them beside the tweak: such a card is still read
(`codeOf`), and pays `B_spend` with no label. Neither is written as `sp1…`: an address lifted out and paid the
standard way from another wallet would make an output only a scan of the chain finds, and Winnow does no such
scan.

Nothing here reads the wallet; `card-keys-test` holds it to vectors an independent implementation wrote
(`scripts/card-keys-vectors`). The curve work is `Secp256k1`, which is not constant-time. -/

namespace Winnow

/-- What a card of 0.9.12 handed one person: the recipient's two silent payment keys (their `hrp` the card's
own, `SilentPaymentPairing.hrp`) and the tweak made for them. The wallet still holds this of every card: it is
what a card's shared secret is made from. The tweak is not a spending secret: whoever holds both can find the
payments made with them and cannot spend them. -/
structure PairingCard where
  address : SilentPaymentAddress
  /-- 32 bytes, a valid scalar. -/
  tweak : ByteArray
  deriving BEq, Inhabited

/-- What one person is handed: the shared secret their payments are made from (`x_k·B_scan`, a compressed
point) and the spend key made for them, with the card's prefix. Whoever holds it can find the payments made
with it and cannot spend them; it holds neither of the wallet's own keys. -/
structure CardCode where
  sharedSecret : ByteArray
  spendKey : ByteArray
  hrp : String
  deriving BEq, Inhabited

namespace CardCode

/-- The data version a code is written with; 0 under the same prefix is the wallet's two keys. -/
def version : Nat := 1

def make (sharedSecret spendKey : ByteArray) (hrp : String) : Except SilentPaymentAddressError CardCode :=
  if SilentPaymentAddress.isValidPublicKey sharedSecret && SilentPaymentAddress.isValidPublicKey spendKey then
    .ok { sharedSecret, spendKey, hrp }
  else .error .invalidPublicKey

/-- The bech32m encoding (`winnowcard1p…` / `twinnowcard1p…`). -/
def encoded (c : CardCode) : Except Bech32Error String := do
  let data ← SegwitAddress.convertBits (c.sharedSecret ++ c.spendKey).toList 8 5 true
  Bech32.encode c.hrp ((version.toUInt8) :: data) .bech32m SilentPaymentAddress.maxAddressLength

/-- Decodes and validates a code strictly: bech32m, version 1, 66 bytes of two valid compressed points, and
`expectedHRP` when given. -/
def decode (s : String) (expectedHRP : Option String := none) : Except SilentPaymentAddressError CardCode := do
  let (hrp, data, enc) ← match Bech32.decode s SilentPaymentAddress.maxAddressLength with
    | .ok r => pure r
    | .error _ => throw .invalidEncoding
  unless enc == .bech32m do throw .invalidEncoding
  if let some expected := expectedHRP then
    unless hrp == expected do throw (.wrongHRP expected hrp)
  let some v := data.head?.map (·.toNat) | throw .invalidEncoding
  unless v == version do throw (.unsupportedVersion v)
  let payload ← match SegwitAddress.convertBits data.tail 5 8 false with
    | .ok p => pure p
    | .error e => throw (.encoding e)
  unless payload.length == 66 do throw (.invalidDataLength payload.length)
  let bytes := ByteArray.mk payload.toArray
  make (bytes.extract 0 33) (bytes.extract 33 66) hrp

end CardCode

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
  /-- the last card index has no label: its label would be BIP352's change label, 0 -/
  | invalidIndex
  deriving Repr, BEq, DecidableEq

def Error.name : Error → String
  | .invalidAddress => "invalidAddress" | .invalidTweak => "invalidTweak" | .invalidPrivateKey => "invalidPrivateKey"
  | .keyMismatch => "keyMismatch" | .derivation => "derivation" | .invalidIndex => "invalidIndex"

abbrev PP := Except Error

/-- The prefix a card's address is written with: `winnowcard` on mainnet, `twinnowcard` on every test network
(as `sp` and `tsp` divide them). Not `sp`/`tsp`: a wallet that does not know cards refuses the string, so
nobody pays a card's address the standard way, where Winnow would not find it. -/
def hrp (mainnet : Bool) : String := if mainnet then "winnowcard" else "twinnowcard"

/-- Shaped like something written under the card's prefix, of either version and either case. A shape check
only. -/
def looksLikeCardAddress (text : String) : Bool :=
  let lowered := text.trimAscii.toString.toLower
  lowered.startsWith (hrp true ++ "1") || lowered.startsWith (hrp false ++ "1")

/-- Shaped like a code (`winnowcard1p…`: version 1, `p` in bech32's alphabet), which is a whole card. -/
def looksLikeCardCode (text : String) : Bool :=
  let lowered := text.trimAscii.toString.toLower
  lowered.startsWith (hrp true ++ "1p") || lowered.startsWith (hrp false ++ "1p")

/-- Shaped like the two keys out of a 0.9.12 card (`winnowcard1q…`: version 0), which without their tweak
pay nothing: such text is routed to the sentence that says to paste the whole card. -/
def looksLikeCardKeys (text : String) : Bool := looksLikeCardAddress text && !looksLikeCardCode text

def pairingTag : String := "Winnow/SilentPayment/Pairing"

def ser32 (i : UInt32) : ByteArray :=
  ByteArray.mk #[(i >>> 24).toUInt8, (i >>> 16).toUInt8, (i >>> 8).toUInt8, i.toUInt8]

def isValidTweak (tweak : ByteArray) : Bool := isValidSecret tweak

/-- `x·B_scan`, compressed: what a silent payment's `ecdh_shared_secret` is, with the tweak in place of
`input_hash·a`. Public: the recipient needs no key for it, having made `x`. -/
def sharedSecretOf (scanKey tweak : ByteArray) : PP ByteArray := do
  unless isValidTweak tweak do throw .invalidTweak
  let scan ← match parsePublicKey scanKey with
    | .ok p => pure p
    | .error _ => throw .invalidAddress
  match publicMultiply scan tweak with
  | .ok p => pure (serializeCompressed p)
  | .error _ => throw .invalidTweak

def sharedSecret (c : PairingCard) : PP ByteArray := sharedSecretOf c.address.scanKey c.tweak

/-- A 0.9.12 card (the wallet's two keys and a tweak) as the code that pays the same scripts: the shared
secret the payer made from it, and the wallet's own spend key, which such a card pays with no label. -/
def codeOf (c : PairingCard) : PP CardCode := do
  let secret ← sharedSecret c
  unless SilentPaymentAddress.isValidPublicKey c.address.spendKey do throw .invalidAddress
  return { sharedSecret := secret, spendKey := c.address.spendKey, hrp := c.address.hrp }

/-- `t_i`: 32 bytes, a valid scalar (BIP352's output tweak for the shared secret at `k = i`). -/
def codeOutputTweak (c : CardCode) (i : UInt32) : PP ByteArray := do
  unless SilentPaymentAddress.isValidPublicKey c.sharedSecret do throw .invalidAddress
  let t := taggedHash "BIP0352/SharedSecret" (c.sharedSecret ++ ser32 i)
  unless isValidSecret t do throw .invalidTweak
  return t

/-- The P2TR scriptPubKey of the person's payment `i`: BIP352's output for the code's shared secret and
spend key. -/
def codeScript (c : CardCode) (i : UInt32) : PP ByteArray := do
  unless SilentPaymentAddress.isValidPublicKey c.sharedSecret do throw .invalidAddress
  match SilentPaymentSending.outputScript c.sharedSecret c.spendKey i with
  | .ok script => pure script
  | .error .invalidTweak => throw .invalidTweak
  | .error _ => throw .invalidAddress

/-- The key that signs for `P_i`: `b_spend + t_i mod n`, with the person's `label` added when their code's
spend key is a labelled one. Only for the secret (and label) the code's spend key is of. -/
def codeSpendSecret (spend : ByteArray) (label : Option ByteArray) (c : CardCode) (i : UInt32) : PP ByteArray := do
  let b ← match secretOf spend with
    | .ok d => pure d
    | .error _ => throw .invalidPrivateKey
  let d ← match label with
    | none => pure b
    | some l => match privateAdd b l with
      | .ok d => pure d
      | .error _ => throw .invalidTweak
  match publicKeyOf (Secp.toBE32 d) with
  | .ok k => unless k == c.spendKey do throw .keyMismatch
  | .error _ => throw .invalidPrivateKey
  let t ← codeOutputTweak c i
  match privateAdd d t with
  | .ok p => pure (Secp.toBE32 p)
  | .error _ => throw .invalidTweak

/-- `t_i` of a 0.9.12 card. -/
def outputTweak (c : PairingCard) (i : UInt32) : PP ByteArray := do codeOutputTweak (← codeOf c) i

/-- The P2TR scriptPubKey of payment `i` to a 0.9.12 card. -/
def scriptPubKey (c : PairingCard) (i : UInt32) : PP ByteArray := do codeScript (← codeOf c) i

/-- `b_spend + t_i mod n`, the key that signs for payment `i` to a 0.9.12 card. -/
def spendSecret (spend : ByteArray) (c : PairingCard) (i : UInt32) : PP ByteArray := do
  codeSpendSecret spend none (← codeOf c) i

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

/-- The address those keys make, with `hrp` (a card's: `SilentPaymentPairing.hrp`). -/
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

/-- Person `k`'s card as 0.9.12 wrote it, from the master key: the wallet's two keys and their tweak. -/
def issue (master : HDKey) (coinType : UInt32) (hrp : String) (k : UInt32) : PP PairingCard := do
  let (scan, spend) ← keys master coinType
  return { address := ← address scan spend hrp, tweak := ← tweakFor scan k }

def labelTag : String := "BIP0352/Label"

/-- BIP352's label `m` of a scan key: `hash_BIP0352/Label(b_scan ‖ ser32(m))`, refused when it is 0 or past
the group order. -/
def labelAt (scan : ByteArray) (m : UInt32) : PP ByteArray := do
  unless isValidSecret scan do throw .invalidPrivateKey
  let l := taggedHash labelTag (scan ++ ser32 m)
  unless isValidSecret l do throw .invalidTweak
  return l

/-- Person `k`'s label: BIP352's label `k + 1`, since label 0 is the one BIP352 keeps for change. The last
index has none (`invalidIndex`). -/
def labelFor (scan : ByteArray) (k : UInt32) : PP ByteArray := do
  if k == 0xFFFF_FFFF then throw .invalidIndex
  labelAt scan (k + 1)

/-- `B_spend + L·G`, compressed: BIP352's labelled spend key. -/
def labelledSpendKey (spendKey label : ByteArray) : PP ByteArray := do
  let spend ← match parsePublicKey spendKey with
    | .ok p => pure p
    | .error _ => throw .invalidAddress
  match publicAdd spend label with
  | .ok p => pure (serializeCompressed p)
  | .error _ => throw .invalidTweak

/-- Person `k`'s code from the wallet's scan and spend private keys: their shared secret and their labelled
spend key. -/
def codeFor (scan spend : ByteArray) (hrp : String) (k : UInt32) : PP CardCode := do
  let own ← address scan spend hrp
  let secret ← sharedSecretOf own.scanKey (← tweakFor scan k)
  return { sharedSecret := secret, spendKey := ← labelledSpendKey own.spendKey (← labelFor scan k), hrp }

/-- Person `k`'s code from the master key. -/
def issueCode (master : HDKey) (coinType : UInt32) (hrp : String) (k : UInt32) : PP CardCode := do
  let (scan, spend) ← keys master coinType
  codeFor scan spend hrp k

end SilentPaymentPairing

end Keys
end Winnow
