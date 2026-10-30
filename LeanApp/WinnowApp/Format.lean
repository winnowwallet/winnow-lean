/-! Formatting shared by every screen (Components.swift: `satsText`, `feeRateText`). -/

namespace WinnowApp

/-- Thousands separators, as `Int64.formatted()` gives in en_US: `1234567` → `1,234,567`. -/
def groupDigits (n : Nat) : String :=
  let s := toString n
  let cs := s.toList
  let k := cs.length
  String.ofList <| (cs.zipIdx.flatMap fun (c, i) =>
    if i > 0 ∧ (k - i) % 3 == 0 then [',', c] else [c])

/-- Sats with thousands separators plus the unit. -/
def satsText (amount : Int) : String :=
  (if amount < 0 then "-" else "") ++ groupDigits amount.natAbs ++ " sats"

/-- A sat/vB rate (thousandths) with at most two decimals, trailing zeros trimmed. -/
def feeRateText (milli : Nat) : String :=
  let hundredths := (milli + 5) / 10
  let whole := hundredths / 100
  let frac := hundredths % 100
  let fracText := if frac == 0 then "" else if frac % 10 == 0 then s!".{frac / 10}" else
    s!".{if frac < 10 then "0" else ""}{frac}"
  s!"{groupDigits whole}{fracText} sat/vB"

/-- The first `n` characters and an ellipsis. -/
def shorten (s : String) (n : Nat := 16) : String :=
  if s.length ≤ n then s else String.ofList (s.toList.take n) ++ "…"

end WinnowApp
