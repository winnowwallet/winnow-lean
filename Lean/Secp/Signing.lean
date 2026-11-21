import Secp.Curve.Spec
import Secp.Bytes
import Secp.Sha256

/-! # What a signature is: BIP 340 and ECDSA signing, step by step on plain numbers

The two signing procedures as their texts give them, with numbers as `Nat`s and one line a step. They are
what the code that signs is proved to return (`SecpCt.sign_eq`, `SecpCt.Ecdsa.sign_eq`): that code works on
machine words and hides its key in how it runs, and these say what it must come to.

Neither computes a point. Each takes "k·G" as a function (`MulG`): the two coordinates of `k` times the
generator, or nothing when that is the point at infinity. The theorems give it the specification's own
multiplication (`Spec.mulG`, which is a definition and not a program); a test gives it one that runs. So
there is no second implementation of the curve behind these, only the steps around it: which number is
negated, what is hashed, what is added.

**BIP 340** (`Bip340.signWith`) is the BIP's default signing.

**ECDSA** (`Ecdsa.signWith`): for a key `d`, a 32-byte digest `z` and a secret number `k`,

    R = k·G,   r = R's x modulo N,   s = (z + r·d) / k modulo N,

and the signature is `r` and `s`, with `s` replaced by `N − s` if it is in the upper half (Bitcoin relays
only the lower one, BIP 146). `k` is made the way BIP 340 makes its own, under tags of this project's: the
key, masked by a hash of 32 bytes of fresh randomness, is hashed together with the digest. So `k` is
different for every digest, as ECDSA needs (two signatures with one `k` give the key away), and it does not
rest on the randomness being good. The tags are not BIP 340's, so a key used for both kinds of signature
never has one `k` in both. RFC 6979 is the usual way to do the same; it is not used so that a signer that
hashes a fixed number of times can make this same signature, byte for byte. The division by `k` is the power
N − 2 (`inverse_eq`), which is `1/k` because N is prime. That N is prime is not proved, and nothing proved
needs it: whoever signs puts the signature to a verifier that checks its own division. -/

namespace Secp
open Spec (N)

/-- `k·G` as two numbers, or nothing for the point at infinity. -/
abbrev MulG := Nat → Option (Nat × Nat)

/-- The specification's `k·G`. A definition to state theorems with: it does not run. -/
noncomputable def Spec.mulG : MulG := fun k =>
  match Spec.smul k Spec.G with
  | .inf => none
  | .pt x y => some (x.val, y.val)

def xorBytes (a b : ByteArray) : ByteArray :=
  ⟨(a.toList.zip b.toList).toArray.map fun (u, v) => u ^^^ v⟩

def hashMod (b : ByteArray) : Nat := fromBE b % N

/-- BIP 340's challenge: the hash of R's x, the key's x and the message, as a number modulo N. -/
def challenge (rx px m : ByteArray) : Nat := hashMod (Sha256.tagged "BIP0340/challenge" (rx ++ px ++ m))

def negN (d : Nat) : Nat := (N - d) % N

namespace Bip340

/-- The BIP 340 signature of `m` under the key `d0` with 32 bytes `aux`, and the x-only key it verifies
under. Nothing when `d0·G` is the point at infinity, `aux` is not 32 bytes, or the number the signature is
made with comes out zero. -/
def signWith (g : MulG) (m : ByteArray) (d0 : Nat) (aux : ByteArray) : Option (ByteArray × ByteArray) :=
  if aux.size ≠ 32 then none else
  match g d0 with
  | none => none
  | some (px, py) =>
    let d := if py % 2 = 1 then negN d0 else d0
    let pxb := toBE32 px
    let t := xorBytes (toBE32 d) (Sha256.tagged "BIP0340/aux" aux)
    let k0 := hashMod (Sha256.tagged "BIP0340/nonce" (t ++ pxb ++ m))
    if k0 = 0 then none else
    match g k0 with
    | none => none
    | some (rx, ry) =>
      let k := if ry % 2 = 1 then negN k0 else k0
      let rxb := toBE32 rx
      let e := challenge rxb pxb m
      some (rxb ++ toBE32 ((k + e * d) % N), pxb)

end Bip340

namespace Ecdsa

/-- What one bit of an exponent does to a running power modulo `m`: square, and multiply if the bit is set. -/
def powerStep (a m : Nat) (acc : Nat) (bit : Bool) : Nat :=
  if bit then acc * acc % m * a % m else acc * acc % m

/-- `k` to the power N − 2, modulo N, by squaring: `1/k` modulo N. -/
def inverse (k : Nat) : Nat :=
  ((List.range 256).reverse.map (fun i => (N - 2).testBit i)).foldl (powerStep k N) 1

/-- The secret number a signature of `digest` under `d` is made with, given 32 bytes `aux` of randomness. -/
def nonce (d : Nat) (digest aux : ByteArray) : Nat :=
  hashMod (Sha256.tagged "winnow/ecdsa/nonce"
    (xorBytes (toBE32 d) (Sha256.tagged "winnow/ecdsa/aux" aux) ++ digest))

/-- `s`, or `N − s` if `s` is in the upper half. -/
def lowS (s : Nat) : Nat := if s > N / 2 then N - s else s

/-- The ECDSA signature of a 32-byte `digest` under the key `d`: `r` and `s`. Nothing when `d` is not from
1 to N − 1, the digest or `aux` is not 32 bytes, or `k`, `r` or `s` comes out zero. -/
def signWith (g : MulG) (digest : ByteArray) (d : Nat) (aux : ByteArray) : Option (Nat × Nat) :=
  if d = 0 ∨ d ≥ N then none else
  if aux.size ≠ 32 ∨ digest.size ≠ 32 then none else
  let k := nonce d digest aux
  if k = 0 then none else
  match g k with
  | none => none
  | some (rx, _) =>
    let r := rx % N
    if r = 0 then none else
    let s := inverse k * ((fromBE digest % N + r * d % N) % N) % N
    if s = 0 then none else some (r, lowS s)

/-- A signature as 64 bytes: `r` then `s`. -/
def encode (signature : Nat × Nat) : ByteArray := toBE32 signature.1 ++ toBE32 signature.2

end Ecdsa
end Secp
