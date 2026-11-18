import Winnow.Tx.Transaction

/-! # SighashBIP143: what a SegWit v0 signature commits to

The digest an ECDSA signature on a version 0 witness program is made over (BIP143), for SIGHASH_ALL, the
only kind this wallet makes or counts: every input's outpoint and sequence, every output, and for the input
being signed its outpoint, the script it is locked to (the witness script of a P2WSH coin), its amount and
its sequence.

A Taproot signature commits to the amount of every coin the transaction spends (`SighashBIP341`); this one
commits only to the amount of the one coin it spends. Whoever relies on a transaction's fee must therefore
know every input's amount from somewhere the signature does not vouch for: the wallet's own record of its
coins, or the whole transaction each coin came from (see `Wallet/SegwitSpendReview.lean`).

`crypto-test` holds it to BIP143's own examples. -/

namespace Winnow
namespace SighashBIP143
open Wire

/-- SIGHASH_ALL, as the byte after a signature and the four bytes the digest ends with. -/
def hashTypeAll : UInt8 := 0x01

/-- The digest a signature on input `index` of `tx` is made over when it commits to every input and output
(SIGHASH_ALL), for a coin of `amount` locked to `scriptCode`; `none` for an input the transaction does not
have. For P2WSH the script code is the witness script (one without OP_CODESEPARATOR, as every script this
wallet signs for is). -/
def sighashAll (tx : Transaction) (index : Nat) (scriptCode : ByteArray) (amount : Int64) : Option ByteArray := do
  let input ← tx.inputs[index]?
  let prevouts := tx.inputs.foldl (fun d i => appendUInt32 (d ++ i.previousOutput.txid) i.previousOutput.vout) .empty
  let sequences := tx.inputs.foldl (fun d i => appendUInt32 d i.sequence) .empty
  let outputs := tx.outputs.foldl (fun d o => appendVarData (appendInt64 d o.value) o.scriptPubKey) .empty
  let m := appendInt32 .empty tx.version ++ sha256d prevouts ++ sha256d sequences
  let m := appendUInt32 (m ++ input.previousOutput.txid) input.previousOutput.vout
  let m := appendInt64 (appendVarData m scriptCode) amount
  let m := appendUInt32 m input.sequence ++ sha256d outputs
  return sha256d (appendUInt32 (appendUInt32 m tx.locktime) hashTypeAll.toUInt32)

end SighashBIP143
end Winnow
