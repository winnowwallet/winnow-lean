import Lean.Data.Json.Parser

/-! # JSON text from outside the wallet

`Lean.Json.parse` multiplies a positive exponent out while it reads, so `1e99999999` takes minutes of CPU, and it
keeps a negative one, so `1e-99999999` reaches whoever computes `10 ^ exponent`, where the runtime ends the process
(`Nat.pow exponent is too big`). No value the wallet reads needs either, and a Double's exponent ends in the
hundreds, so a larger one is refused before the parser sees the text. `SwiftJSON` is the wallet's other reader and
has its own bounds.

The `fuzz` executable's JSON targets carry these numbers as tokens, and `Vectors/fuzz` keeps both forms (SEC-040). -/

namespace Winnow.Text

/-- A Double's decimal exponent ends at 308 and its smallest value at about 324 digits down. -/
def maximumJsonExponent : Nat := 400

/-- Whether every number outside a string has an exponent within `maximumJsonExponent`. -/
def jsonExponentsBounded (text : String) : Bool := Id.run do
  let b := text.toUTF8
  let isDigit (x : UInt8) : Bool := 0x30 ≤ x && x ≤ 0x39
  let mut i := 0
  let mut inString := false
  while i < b.size do
    let c := b[i]!
    if inString then
      if c == 0x5C then i := i + 1
      else if c == 0x22 then inString := false
    else if c == 0x22 then inString := true
    else if (c == 0x65 || c == 0x45) && i > 0 && isDigit b[i - 1]! then
      let mut j := i + 1
      if j < b.size && (b[j]! == 0x2B || b[j]! == 0x2D) then j := j + 1
      let mut exponent := 0
      while j < b.size && isDigit b[j]! do
        exponent := exponent * 10 + (b[j]! - 0x30).toNat
        if exponent > maximumJsonExponent then return false
        j := j + 1
    i := i + 1
  return true

/-- `Json.parse`, for text the wallet did not write. -/
def parseJson (text : String) : Except String Lean.Json :=
  if jsonExponentsBounded text then Lean.Json.parse text
  else .error "a number's exponent is out of range"

end Winnow.Text
