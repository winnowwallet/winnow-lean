/-! # Fee-rate resolution (Wallet/FeePolicy.swift)

Strongest first: an explicit user override, else the median rate observed in the wallet's own confirmed
transactions, else a static preset per priority; the result is clamped from below by the peers' BIP133
`feefilter` floor. Rates are sat/vB as `Float` (Swift's `Double`). Upstream 1cf93fb adds `resolution`, with
an explicit cap on a peer-driven increase and the clamped floor reported, `acceptsRate` and
`seatMajorityFloor`; the pool's aggregation is `WinnowApp.Real.feeFloor`. -/

namespace Winnow.FeePolicy

inductive Priority where
  | low
  | medium
  | high
  deriving Repr, BEq, DecidableEq, Inhabited

def Priority.satPerVByte : Priority → Float
  | .low => 2
  | .medium => 5
  | .high => 12

def Priority.ofString? : String → Option Priority
  | "low" => some .low
  | "medium" => some .medium
  | "high" => some .high
  | _ => none

/-- Median of the samples (`none` when empty): the middle one, or the mean of the two middle ones. -/
def median (samples : Array Float) : Option Float :=
  if samples.isEmpty then none
  else
    let sorted := samples.qsort (· < ·)
    let mid := sorted.size / 2
    some (if sorted.size % 2 == 1 then sorted[mid]! else (sorted[mid - 1]! + sorted[mid]!) / 2)

def maximumSatPerVByte : Float := 10_000
/-- The default cap on an automatic peer-driven increase. -/
def maximumPeerFloorSatPerVByte : Float := 120

/-- A rate the policy can work with: finite, positive and at most `maximumSatPerVByte`. -/
def usable (rate : Option Float) : Option Float :=
  rate.filter fun r => r.isFinite && r > 0 && r ≤ maximumSatPerVByte

/-- Whether a typed rate is one the policy accepts (refuse it where it was typed rather than replace it). -/
def acceptsRate (rate : Float) : Bool := (usable (some rate)).isSome

/-- Only `none` means uncapped; an explicit cap is clamped into `0 … maximumSatPerVByte`, a non-finite one
treated as none. -/
def effectiveCap (cap : Option Float) : Float :=
  match cap with
  | some c => if c.isFinite then min (max c 0) maximumSatPerVByte else maximumSatPerVByte
  | none => maximumSatPerVByte

/-- `Resolution`: the rate, and the reported floor it falls below because of the cap (the caller must get a
new decision or refuse before signing). -/
structure Resolution where
  rate : Float
  clampedFloor : Option Float
  deriving Inhabited, BEq

/-- `resolution(priority:override:estimated:observed:floorSatPerVByte:peerFloorCap:)` (upstream 1cf93fb):
override, else an estimate no lower than the observed median, else the observed median, else the preset;
then at least the peers' floor up to `peerFloorCap` (default 120 sat/vB; `none` uncapped). Unusable
inputs fall through. -/
def resolution (priority : Priority := .medium) (override : Option Float := none) (estimated : Option Float := none)
    (observed : Array Float := #[]) (floor : Option Float := none)
    (peerFloorCap : Option Float := some maximumPeerFloorSatPerVByte) : Resolution :=
  let observedRate := median (observed.filterMap fun r => usable (some r))
  let estimate := (usable estimated).map fun e => max e (observedRate.getD 0)
  let base := (usable override).getD (estimate.getD (observedRate.getD priority.satPerVByte))
  match usable floor with
  | none => { rate := base, clampedFloor := none }
  | some f =>
    let rate := max base (min f (effectiveCap peerFloorCap))
    { rate, clampedFloor := if rate < f then some f else none }

/-- The uncapped rule: never below the reported floor. -/
def resolve (priority : Priority := .medium) (override : Option Float := none) (observed : Array Float := #[])
    (floor : Option Float := none) : Float :=
  (resolution priority override none observed floor none).rate

/-- Lower median across configured seats, missing or unusable reports counting as zero: a floor needs more
than half of the seats behind it. -/
def seatMajorityFloor (reported : Array Float) (seats : Nat) : Option Float :=
  let count := max seats reported.size
  if count == 0 then none
  else
    let values := reported.map (fun r => (usable (some r)).getD 0) ++ Array.replicate (count - reported.size) 0
    let floor := (values.qsort (· < ·))[(count - 1) / 2]!
    if floor > 0 then some floor else none

end Winnow.FeePolicy
