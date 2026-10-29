/-! # Doubles as Swift prints and parses them

Swift's `Double.description` (shortest round-trip digits, closest to the exact value among the shortest;
decimal notation for 1e-4 ≤ |x| ≤ 2^53, else `d.ddde±XX`), the `JSONEncoder` form of it (a trailing
`.0` dropped), `formatted(.number.precision(.fractionLength(2)))` in the en_US locale (half-even on
the shortest decimal, `,` grouping), and a correctly rounded decimal → double conversion (JSON numbers).
All exact, on `Nat`/`Int`. -/

namespace Winnow.SwiftDouble

def two52 : Nat := 2 ^ 52

/-- The exact value of a finite, nonzero |x|: `m · 2^e`. -/
def decompose (x : Float) : Nat × Int :=
  let bits := x.toBits
  let be := ((bits >>> 52) &&& 0x7FF).toNat
  let f := (bits &&& 0xF_FFFF_FFFF_FFFF).toNat
  if be == 0 then (f, -1074) else (f + two52, (be : Int) - 1075)

def isNegative (x : Float) : Bool := x.toBits >>> 63 == 1

/-- A rational `num / den` (both positive). -/
structure Q where
  num : Nat
  den : Nat

/-- `a · 10^k` compared with the rational `q` (k may be negative): `a · 10^k < q`, `=`, `>`. -/
def cmpScaled (a : Nat) (k : Int) (q : Q) : Ordering :=
  if k ≥ 0 then compare (a * 10 ^ k.toNat * q.den) q.num
  else compare (a * q.den) (q.num * 10 ^ (-k).toNat)

/-- floor(log10 q) for q > 0. -/
def floorLog10 (q : Q) : Int := Id.run do
  let ip := q.num / q.den
  if ip ≥ 1 then return (Nat.toDigits 10 ip).length - 1
  let mut j : Nat := 1
  while q.num * 10 ^ j < q.den do j := j + 1
  return -(j : Int)

/-- floor(q / 10^k). -/
def floorDiv (q : Q) (k : Int) : Nat :=
  if k ≥ 0 then q.num / (q.den * 10 ^ k.toNat) else q.num * 10 ^ (-k).toNat / q.den

/-- Shortest round-trip digits of a finite positive double: `(digits, P)` with x ≈ 0.digits × 10^P,
no trailing zeros. -/
def shortest (x : Float) : String × Int := Id.run do
  let (m, e) := decompose x
  -- everything in units of 2^(e-2)
  let s := e - 2
  let toQ (n : Nat) : Q := if s ≥ 0 then ⟨n * 2 ^ s.toNat, 1⟩ else ⟨n, 2 ^ (-s).toNat⟩
  let v := toQ (4 * m)
  let lowerGap := if m == two52 && e > -1074 then 1 else 2
  let lo := toQ (4 * m - lowerGap)
  let hi := toQ (4 * m + 2)
  let inclusive := m % 2 == 0
  let inside (d : Nat) (k : Int) : Bool :=
    match cmpScaled d k lo, cmpScaled d k hi with
    | .gt, .lt => true
    | .eq, .lt => inclusive
    | .gt, .eq => inclusive
    | _, _ => false
  let E := floorLog10 v
  let mut best : Option (Nat × Int) := none
  for n in [1:18] do
    let k := E - n + 1
    let d0 := floorDiv v k
    let c0 := inside d0 k
    let c1 := inside (d0 + 1) k
    if c0 || c1 then
      let pick :=
        if c0 && c1 then
          -- the closer one: compare v - d0·10^k with (d0+1)·10^k - v, i.e. 2v vs (2d0+1)·10^k
          match cmpScaled (2 * d0 + 1) k ⟨2 * v.num, v.den⟩ with
          | .lt => d0 + 1 | .gt => d0 | .eq => if d0 % 2 == 0 then d0 else d0 + 1
        else if c0 then d0 else d0 + 1
      best := some (pick, k)
      break
  let (d, k) := best.getD (0, 0)
  -- strip trailing zeros
  let mut d := d
  let mut k := k
  while d > 0 && d % 10 == 0 do d := d / 10; k := k + 1
  let digits := String.ofList (Nat.toDigits 10 d)
  return (digits, k + digits.length)

def pad2 (n : Nat) : String := if n < 10 then s!"0{n}" else toString n

/-- `Double.description`. -/
def description (x : Float) : String :=
  if x.isNaN then "nan"
  else if x.isInf then (if x > 0 then "inf" else "-inf")
  else
    let sign := if isNegative x then "-" else ""
    if x == 0 then sign ++ "0.0"
    else
      let (D, P) := shortest x.abs
      let n := D.length
      let decimal := P ≥ -3 && x.abs ≤ 9007199254740992.0
      if decimal then
        if P ≤ 0 then sign ++ "0." ++ String.ofList (List.replicate (-P).toNat '0') ++ D
        else if n ≤ P.toNat then sign ++ D ++ String.ofList (List.replicate (P.toNat - n) '0') ++ ".0"
        else sign ++ (D.take P.toNat).toString ++ "." ++ (D.drop P.toNat).toString
      else
        let ex := P - 1
        let mant := if n > 1 then (D.take 1).toString ++ "." ++ (D.drop 1).toString else D
        sign ++ mant ++ "e" ++ (if ex < 0 then "-" else "+") ++ pad2 ex.natAbs

/-- The text `JSONEncoder` writes for a finite double (`description` without a trailing `.0`). -/
def jsonText (x : Float) : String :=
  let d := description x
  if d.endsWith ".0" then (d.dropEnd 2).toString else d

/-- en_US grouping of a decimal integer string. -/
def group (s : String) : String := Id.run do
  let cs := s.toList
  let n := cs.length
  let mut out : List Char := []
  for h : i in [0:n] do
    if i > 0 && (n - i) % 3 == 0 then out := out ++ [',']
    out := out ++ [cs[i]!]
  return String.ofList out

/-- `x.formatted(.number.precision(.fractionLength(2)))` in en_US: the shortest decimal rounded half-even
to two places, the integer part grouped with commas. -/
def formatted2 (x : Float) : String :=
  let sign := if isNegative x then "-" else ""
  if x.isNaN then sign ++ "NaN"
  else if x.isInf then sign ++ "∞"
  else
    let (D, P) := if x == 0 then ("0", 1) else shortest x.abs
    -- value = D × 10^(P - n); scaled by 100: D × 10^(P - n + 2)
    let n := D.length
    let d := D.toNat!
    let sh : Int := P - n + 2
    let cents : Nat :=
      if sh ≥ 0 then d * 10 ^ sh.toNat
      else
        let q := 10 ^ (-sh).toNat
        let fl := d / q
        let r := d % q
        if 2 * r > q then fl + 1 else if 2 * r < q then fl else if fl % 2 == 0 then fl else fl + 1
    let ip := cents / 100
    let fp := cents % 100
    sign ++ group (toString ip) ++ "." ++ pad2 fp

/-- The double nearest `(-1)^neg · N · 10^X` (ties to even), IEEE binary64. -/
def ofDecimal (neg : Bool) (N : Nat) (X : Int) : Float := Id.run do
  let signBit : UInt64 := if neg then 0x8000_0000_0000_0000 else 0
  if N == 0 then return Float.ofBits signBit
  if X > 400 then return Float.ofBits (signBit ||| 0x7FF0_0000_0000_0000)
  if X < -800 then return Float.ofBits signBit
  let num := if X ≥ 0 then N * 10 ^ X.toNat else N
  let den := if X ≥ 0 then 1 else 10 ^ (-X).toNat
  -- q = num/den · 2^-e in [2^52, 2^53)
  let mut e : Int := (num.log2 : Int) - den.log2 - 52
  let quot (e : Int) : Nat × Nat × Nat :=
    -- floor(num / (den·2^e)), remainder, divisor
    if e ≥ 0 then let dv := den * 2 ^ e.toNat; (num / dv, num % dv, dv)
    else let nm := num * 2 ^ (-e).toNat; (nm / den, nm % den, den)
  let mut r := quot e
  while r.1 ≥ 2 ^ 53 do e := e + 1; r := quot e
  while r.1 < 2 ^ 52 do e := e - 1; r := quot e
  if e < -1074 then e := -1074; r := quot e
  let (fl, rem, dv) := r
  let mut m := if 2 * rem > dv then fl + 1 else if 2 * rem < dv then fl else if fl % 2 == 0 then fl else fl + 1
  if m == 2 ^ 53 then m := 2 ^ 52; e := e + 1
  if e > 971 then return Float.ofBits (signBit ||| 0x7FF0_0000_0000_0000)
  if m < 2 ^ 52 then return Float.ofBits (signBit ||| m.toUInt64)
  let biased := (e + 1075).toNat
  return Float.ofBits (signBit ||| (biased.toUInt64 <<< 52) ||| (m - 2 ^ 52).toUInt64)

end Winnow.SwiftDouble
