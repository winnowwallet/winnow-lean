import Winnow
import Secp.Keys
import Secp.Ecdsa
import SecpCt.Schnorr
import SecpCt.Ecdsa
import SecpCt.Keys

/-! Temporary: what the curve operations cost, before and after the wallet runs on one implementation.
`secp-bench [rounds]` prints microseconds per operation. Deleted with the old arithmetic. -/

open Winnow Winnow.Keys

def scalarAt (i : Nat) : Nat := Secp.fromBE (sha256 (Secp.toBE32 (i + 1))) % (Secp.Spec.N - 1) + 1

/-- Runs `f` on `rounds` different inputs; microseconds each. `f` returns a byte so that the work is used. -/
def timed (name : String) (rounds : Nat) (f : Nat → UInt8) : IO Unit := do
  let start ← IO.monoNanosNow
  let mut used : UInt8 := 0
  for i in [0:rounds] do
    used := used ^^^ f i
  let stop ← IO.monoNanosNow
  IO.println s!"{name}: {(stop - start) / rounds / 1000} µs   ({used})"

def lastByte (b : ByteArray) : UInt8 := if b.size == 0 then 0 else b[b.size - 1]!

def main (args : List String) : IO UInt32 := do
  let rounds := (args.head?.bind String.toNat?).getD 200
  let some (px, py) := (Secp.pubOf 0x1234567).toOption | return 1
  let point : Secp.APoint := .pt px py
  let xonly := Secp.toBE32 px.toNat
  IO.println s!"old path (Secp.Fast through Secp.Keys), {rounds} rounds each"
  timed "k·G" rounds fun i => match Secp.mulG (scalarAt i) with | .ok (.pt x _) => lastByte (Secp.toBE32 x.toNat) | _ => 0
  timed "k·P" rounds fun i => match Secp.mulPt (scalarAt i) point with | .ok (.pt x _) => lastByte (Secp.toBE32 x.toNat) | _ => 0
  timed "t·G + P" rounds fun i => match Secp.mulGAdd (scalarAt i) point with | .ok (.pt x _) => lastByte (Secp.toBE32 x.toNat) | _ => 0
  timed "lift_x" rounds fun i => match Secp.liftX? (scalarAt i % Secp.P) with | some (_, y) => lastByte (Secp.toBE32 y.toNat) | none => 1
  let message := sha256 "bench".toUTF8
  let signature := (Secp.sign message 0x1234567 (Secp.toBE32 0)).toOption.getD .empty
  timed "BIP340 verify" rounds fun i =>
    match Secp.verify signature (if i % 2 == 0 then message else sha256 message) xonly with | .ok true => 1 | _ => 0
  timed "BIP340 sign" rounds fun i => match Secp.sign message (scalarAt i) (Secp.toBE32 0) with | .ok s => lastByte s | _ => 0
  let compressed := Secp.compressed px py
  let ecdsa := (Secp.Ecdsa.sign message 0x1234567 (Secp.toBE32 0)).toOption.getD .empty
  timed "ECDSA verify" rounds fun i =>
    match Secp.Ecdsa.verify ecdsa (if i % 2 == 0 then message else sha256 message) compressed with | .ok true => 1 | _ => 0
  let some master := (HDKey.ofSeed (sha256 "bench seed".toUTF8)).toOption | return 1
  let some account := (master.derived "m/86'/1'/0'").toOption | return 1
  let xpub := account.neutered
  timed "BIP32 public child" rounds fun i => match xpub.child i.toUInt32 with | .ok k => lastByte k.publicKey | .error _ => 0
  let text := s!"tr([{Descriptor.hex8 master.fingerprint}/86'/1'/0']{xpub.serialized .testnet}/<0;1>/*)"
  let some descriptor := (Descriptor.parse text).toOption | return 1
  timed "one wallet address index (both chains)" (rounds / 4 + 1) fun i =>
    match descriptor.derived i.toUInt32 .regtest with | .ok outs => lastByte (outs[0]!.scriptPubKey) | .error _ => 0
  IO.println "SecpCt"
  timed "k·G (ladder and affine)" rounds fun i =>
    lastByte (SecpCt.Point.mulGenerator (SecpCt.Sc.ofBytes (Secp.toBE32 (scalarAt i)))).affine.1.bytes
  timed "BIP340 sign" rounds fun i => match SecpCt.sign (Secp.toBE32 (scalarAt i)) message (Secp.toBE32 0) with | some s => lastByte s | none => 0
  let some q := SecpCt.parseCompressed compressed | return 1
  let sc (i : Nat) := SecpCt.Sc.ofBytes (Secp.toBE32 (scalarAt i))
  timed "t·G, public" rounds fun i => match SecpCt.generatorMul (sc i) with | some r => lastByte r.xBytes | none => 0
  timed "k·P, constant time" rounds fun i => match SecpCt.pointMul (sc i) q with | some r => lastByte r.xBytes | none => 0
  timed "t·G + P, public" rounds fun i => match SecpCt.pointAdd q (sc i) with | some r => lastByte r.xBytes | none => 0
  timed "lift_x" rounds fun i => match (SecpCt.Fe.ofBytes? (Secp.toBE32 (scalarAt i % Secp.P))).bind SecpCt.liftX? with | some r => lastByte r.y.bytes | none => 1
  timed "BIP340 verify" rounds fun i => if SecpCt.verify signature (if i % 2 == 0 then message else sha256 message) xonly then 1 else 0
  timed "ECDSA verify" rounds fun i => if SecpCt.Ecdsa.verify ecdsa (if i % 2 == 0 then message else sha256 message) compressed then 1 else 0
  timed "ECDSA sign" rounds fun i => match SecpCt.Ecdsa.sign (Secp.toBE32 (scalarAt i)) message (Secp.toBE32 0) with | some s => lastByte s | none => 0
  return 0
