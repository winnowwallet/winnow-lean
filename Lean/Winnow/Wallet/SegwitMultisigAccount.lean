import Winnow.Wallet.SegwitSpendReview
import Winnow.Wallet.MultisigAccount
import Secp.Ecdsa
import SecpCt.Ecdsa

/-! # SegWit v0 multisig accounts: signing, counting signatures, finalizing

What a member of a `wsh(sortedmulti(k, KEY, …))` account does with a PSBT someone else made, beside the
account itself and its review (`Wallet/SegwitSpendReview.lean`, in the core library):

  - `sign` reviews the spend, then adds this member's ECDSA signature to every input as a BIP174 partial
    signature (and the witness script, so that whoever finalizes has it);
  - `approvals` says which of the account's keys have a signature on every input that verifies against the
    digest recomputed here (BIP143);
  - `finalizeSpend` reviews once more and, where every input has the threshold of verified signatures,
    assembles the witness (`OP_0`'s empty item, the signatures in the script's key order, the script) and
    extracts the transaction.

Signatures are made by `SecpCt.Ecdsa.sign`, which does the same work whatever the key is and is proved to
return what the reference returns (`SecpCt.Ecdsa.sign_eq`), and every one is put to `Secp.Ecdsa.verify`
before it is written into the PSBT: a signature that leaves here satisfies ECDSA's equation for the key it
is filed under (`Secp.Ecdsa.verify_sound`). Signatures commit to every input and output (SIGHASH_ALL); no
other kind is made or counted. A signature by someone else is counted only if it is strict DER (BIP66) with
`s` in the lower half (BIP146), as Bitcoin Core's relay rules want it.

The stored record is the Taproot account's (`MultisigAccountRecord`): it names the account by its descriptor
text and nothing in it is particular to a kind. -/

namespace Winnow
open Keys
open Tx (BitcoinNetwork)

namespace SegwitMultisigAccount
open MultisigAccount (refuse lift fail OutputCoordinate)

/-- The digest a signature on input `k` is made over, and the account at the coin that input spends. -/
def signingContext (a : SegwitMultisigAccount) (tx : Transaction) (k : Nat) (coin : WalletUTXO) :
    MAM (Resolved × ByteArray) := do
  let resolved ← a.resolved coin.chain.rawValue coin.index
  let some digest := SighashBIP143.sighashAll tx k resolved.witnessScript coin.amount
    | refuse s!"input {k + 1} is not an input of this transaction"
  return (resolved, digest)

/-- An ECDSA signature by `secret` over `digest`, as a PSBT carries it: DER, then the SIGHASH_ALL byte.
Checked under the public key it will be filed under before it is returned. -/
def partialSignature (secret publicKey digest auxiliaryRand : ByteArray) : MAM ByteArray := do
  let some signature := SecpCt.Ecdsa.sign secret digest auxiliaryRand | throw (.named "signingFailed")
  match Secp.Ecdsa.verify signature digest publicKey with
  | .ok true => return (Secp.Ecdsa.der signature).push SighashBIP143.hashTypeAll
  | _ => throw (.named "signingFailed")

/-- Reviews the spend, then adds a signature to every input for each of the account's keys that `signingKey`
holds (a master, or an account key itself); `noSignerKey` when an input has none. The PSBT is replaced only
when every input signs. -/
def sign (a : SegwitMultisigAccount) (psbt : PSBT) (signingKey : HDKey) (knownUTXOs : Array WalletUTXO)
    (ownedOutputCoordinates : Array OutputCoordinate) (chainTip : UInt32) (auxiliaryRand : ByteArray) : MAM PSBT := do
  discard (a.reviewSpend psbt knownUTXOs ownedOutputCoordinates chainTip)
  let tx ← lift (·.name) psbt.unsignedTransaction
  let mut held : Array (Descriptor.SingleKey × HDKey) := #[]
  for signer in a.keys do
    if let some account ← MultisigAccount.accountSecretKey signer signingKey then held := held.push (signer, account)
  let mut signed := psbt
  for k in [0:signed.inputs.size] do
    let coin ← MultisigAccount.coin signed k knownUTXOs
    let (resolved, digest) ← a.signingContext tx k coin
    let mut signatures : Array (ByteArray × ByteArray) := #[]
    for (signer, account) in held do
      let child ← lift (·.name) (account.derivedPath (MultisigAccount.suffixSteps signer coin.chain.rawValue coin.index))
      let some secret := child.privateKey | continue
      unless resolved.keys.contains child.publicKey do continue
      signatures := signatures.push (child.publicKey, ← partialSignature secret child.publicKey digest auxiliaryRand)
    if signatures.isEmpty then fail (.noSignerKey k)
    signed := signed.modifyInput k fun input =>
      signatures.foldl (fun input (publicKey, signature) => input.setPartialSignature publicKey signature)
        (input.setWitnessScript (some resolved.witnessScript))
  return signed

/-- The 64 bytes `r`, `s` of a PSBT partial signature this wallet counts: strict DER followed by the
SIGHASH_ALL byte. -/
def countedSignature? (partialSig : ByteArray) : Option ByteArray := do
  guard (partialSig.size ≥ 1 && partialSig[partialSig.size - 1]! == SighashBIP143.hashTypeAll)
  Secp.Ecdsa.parseDer (partialSig.extract 0 (partialSig.size - 1))

/-- The partial signatures on input `k` that verify, as (public key, signature as the PSBT carries it), for
keys of the account at that coin only. In key order. -/
def verifiedSignatures (psbt : PSBT) (k : Nat) (resolved : Resolved) (digest : ByteArray) :
    Array (ByteArray × ByteArray) :=
  psbt.inputs[k]!.partialSignatures.filter fun (publicKey, partialSig) =>
    resolved.keys.contains publicKey &&
      match countedSignature? partialSig with
      | some signature => (Secp.Ecdsa.verify signature digest publicKey).toOption == some true
      | none => false

/-- Which of the account's keys (by position in `keys`) have a verified signature on every input, judged by
ECDSA verification against the recomputed digest. Ascending positions. -/
def approvals (a : SegwitMultisigAccount) (psbt : PSBT) (knownUTXOs : Array WalletUTXO) : MAM (Array Nat) := do
  let tx ← lift (·.name) psbt.unsignedTransaction
  let mut approved : Option (Array Nat) := none
  for k in [0:psbt.inputs.size] do
    let coin ← MultisigAccount.coin psbt k knownUTXOs
    let (resolved, digest) ← a.signingContext tx k coin
    let verified := (verifiedSignatures psbt k resolved digest).map (·.1)
    let here := (Array.range a.keys.size).filter fun position => verified.contains resolved.keys[position]!
    approved := some (match approved with | some previous => previous.filter here.contains | none => here)
  return approved.getD #[]

/-- The witness of a P2WSH multisig input: the empty item OP_CHECKMULTISIG takes besides its signatures,
the signatures in the order their keys have in the script, and the script. -/
def witness (signatures : Array ByteArray) (script : ByteArray) : Array ByteArray :=
  #[ByteArray.empty] ++ signatures ++ #[script]

/-- What a finalized input no longer carries (BIP174): its partial signatures, hash type, scripts and key
origins. -/
def finalizedAway : List UInt8 :=
  [PSBT.InType.partialSignature, PSBT.InType.sighashType, 0x04, PSBT.InType.witnessScript, PSBT.InType.bip32Derivation]

/-- Finalizes a PSBT with at least the threshold of verified signatures on every input and extracts the raw
transaction, after one more review. Each witness carries exactly the threshold: the first verified
signatures in the script's key order. Returns the finalized PSBT and the transaction; all or nothing. -/
def finalizeSpend (a : SegwitMultisigAccount) (psbt : PSBT) (knownUTXOs : Array WalletUTXO)
    (ownedOutputCoordinates : Array OutputCoordinate) (chainTip : UInt32) : MAM (PSBT × Transaction) := do
  discard (a.reviewSpend psbt knownUTXOs ownedOutputCoordinates chainTip)
  let tx ← lift (·.name) psbt.unsignedTransaction
  let mut finalized := psbt
  for k in [0:psbt.inputs.size] do
    let coin ← MultisigAccount.coin psbt k knownUTXOs
    let (resolved, digest) ← a.signingContext tx k coin
    let verified := verifiedSignatures psbt k resolved digest
    let inScriptOrder := (sortBytes (fun key => key) resolved.keys).filterMap fun key => (verified.find? (·.1 == key)).map (·.2)
    unless inScriptOrder.size ≥ a.threshold do
      throw (.named (PSBTError.missingField s!"input {k} partial sigs below threshold").name)
    finalized := finalized.modifyInput k fun input =>
      let input := input.setFinalScriptWitness (some (witness (inScriptOrder.extract 0 a.threshold) resolved.witnessScript))
      ⟨input.pairs.filter fun pair => !finalizedAway.contains pair.type⟩
  let extracted ← lift (·.name) finalized.extractedTransaction
  lift (·.name) (Wallet.checkStandardSize extracted)
  return (finalized, extracted)

end SegwitMultisigAccount
end Winnow
