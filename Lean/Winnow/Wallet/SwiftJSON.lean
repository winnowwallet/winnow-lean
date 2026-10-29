import Winnow.Wallet.SwiftDouble
import Winnow.Tx.Base64

/-! # JSON as Foundation's `JSONEncoder` / `JSONDecoder` do it

The wallet file is written by `JSONEncoder()` and read by `JSONDecoder()`. This module keeps a JSON
value with its number tokens as text (so integers and doubles are decoded exactly as Swift decodes
them), a strict RFC 8259 parser, and a writer in Foundation's style: `/` escaped as `\/`, `\b \f \n \r
\t`, other control characters as `\u00xx`, everything else literal.

Key order: `JSONEncoder()` without `.sortedKeys` emits a keyed container's keys in hash order, which
Swift seeds per process — the same state is written with a different key order on every launch. The
Lean writer always emits sorted keys (the `.sortedKeys` form of the same bytes).

Decoding failures carry the Swift error's case name: `keyNotFound`, `valueNotFound`, `typeMismatch`,
`dataCorrupted` (`DecodingError`), or a thrown domain error's name. Duplicate keys: the first wins
(as measured on `JSONDecoder`). -/

namespace Winnow.SwiftJSON

inductive JV where
  | null
  | bool (b : Bool)
  | num (text : String)
  | str (s : String)
  | arr (xs : Array JV)
  | obj (kvs : Array (String × JV))
  deriving Inhabited, BEq

/-! ## Parser -/

structure P where
  cs : Array Char
  i : Nat

abbrev PM := StateT P (Except Unit)

def peekC : PM (Option Char) := do let s ← get; return s.cs[s.i]?
def nextC : PM Char := do
  let s ← get
  match s.cs[s.i]? with
  | some c => set { s with i := s.i + 1 }; return c
  | none => throw ()

partial def skipWs : PM Unit := do
  match ← peekC with
  | some ' ' | some '\t' | some '\n' | some '\r' => discard nextC; skipWs
  | _ => pure ()

def expectC (c : Char) : PM Unit := do
  if (← nextC) != c then throw ()

def expectStr (s : String) : PM Unit := s.toList.forM expectC

def hexVal (c : Char) : Option Nat :=
  if '0' ≤ c && c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c && c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else none

def hex4 : PM Nat := do
  let mut v := 0
  for _ in [0:4] do
    let some h := hexVal (← nextC) | throw ()
    v := v * 16 + h
  return v

partial def parseStringBody (acc : String) : PM String := do
  let c ← nextC
  if c == '"' then return acc
  if c.toNat < 0x20 then throw ()
  if c != '\\' then return ← parseStringBody (acc.push c)
  let e ← nextC
  match e with
  | '"' => parseStringBody (acc.push '"')
  | '\\' => parseStringBody (acc.push '\\')
  | '/' => parseStringBody (acc.push '/')
  | 'b' => parseStringBody (acc.push '\x08')
  | 'f' => parseStringBody (acc.push '\x0c')
  | 'n' => parseStringBody (acc.push '\n')
  | 'r' => parseStringBody (acc.push '\r')
  | 't' => parseStringBody (acc.push '\t')
  | 'u' =>
    let u ← hex4
    if 0xD800 ≤ u && u < 0xDC00 then
      expectC '\\'; expectC 'u'
      let l ← hex4
      unless 0xDC00 ≤ l && l < 0xE000 do throw ()
      parseStringBody (acc.push (Char.ofNat (0x10000 + ((u - 0xD800) <<< 10) + (l - 0xDC00))))
    else if 0xDC00 ≤ u && u < 0xE000 then throw ()
    else parseStringBody (acc.push (Char.ofNat u))
  | _ => throw ()

def isDigit (c : Char) : Bool := '0' ≤ c && c ≤ '9'

partial def takeDigits (acc : String) : PM String := do
  match ← peekC with
  | some c => if isDigit c then discard nextC; takeDigits (acc.push c) else return acc
  | none => return acc

def parseNumber : PM String := do
  let mut t := ""
  if (← peekC) == some '-' then discard nextC; t := t.push '-'
  match ← peekC with
  | some '0' => discard nextC; t := t.push '0'
  | some c =>
    if isDigit c then t ← takeDigits t else throw ()
  | none => throw ()
  if (← peekC) == some '.' then
    discard nextC
    let ds ← takeDigits ""
    if ds.isEmpty then throw ()
    t := t ++ "." ++ ds
  if (← peekC) == some 'e' || (← peekC) == some 'E' then
    discard nextC
    t := t.push 'e'
    if (← peekC) == some '+' || (← peekC) == some '-' then t := t.push (← nextC)
    let ds ← takeDigits ""
    if ds.isEmpty then throw ()
    t := t ++ ds
  return t

partial def parseValue (depth : Nat) : PM JV := do
  if depth > 512 then throw ()
  skipWs
  match ← peekC with
  | some '{' =>
    discard nextC; skipWs
    if (← peekC) == some '}' then discard nextC; return .obj #[]
    let mut kvs : Array (String × JV) := #[]
    repeat
      skipWs
      expectC '"'
      let k ← parseStringBody ""
      skipWs; expectC ':'
      let v ← parseValue (depth + 1)
      kvs := kvs.push (k, v)
      skipWs
      match ← nextC with
      | ',' => pure ()
      | '}' => break
      | _ => throw ()
    return .obj kvs
  | some '[' =>
    discard nextC; skipWs
    if (← peekC) == some ']' then discard nextC; return .arr #[]
    let mut xs : Array JV := #[]
    repeat
      xs := xs.push (← parseValue (depth + 1))
      skipWs
      match ← nextC with
      | ',' => pure ()
      | ']' => break
      | _ => throw ()
    return .arr xs
  | some '"' => discard nextC; return .str (← parseStringBody "")
  | some 't' => expectStr "true"; return .bool true
  | some 'f' => expectStr "false"; return .bool false
  | some 'n' => expectStr "null"; return .null
  | some _ => return .num (← parseNumber)
  | none => throw ()

def parseAll : PM JV := do
  let v ← parseValue 0
  skipWs
  if (← peekC).isSome then throw ()
  return v

/-- `JSONSerialization` / `JSONDecoder`: one leading UTF-8 byte-order mark is skipped. -/
def parse? (s : String) : Option JV :=
  let chars := match s.toList with
    | '\uFEFF' :: rest => rest
    | cs => cs
  match parseAll.run ⟨chars.toArray, 0⟩ with
  | .ok (v, _) => some v
  | .error _ => none

/-! ## Writer -/

def hexDigit (n : Nat) : Char := "0123456789abcdef".toList[n]!

def escape (s : String) (escapeSlashes : Bool := true) : String := Id.run do
  let mut out := "\""
  for c in s.toList do
    out := match c with
      | '"' => out ++ "\\\""
      | '\\' => out ++ "\\\\"
      | '/' => if escapeSlashes then out ++ "\\/" else out.push '/'
      | '\x08' => out ++ "\\b"
      | '\x0c' => out ++ "\\f"
      | '\n' => out ++ "\\n"
      | '\r' => out ++ "\\r"
      | '\t' => out ++ "\\t"
      | c => if c.toNat < 0x20 then out ++ "\\u00" |>.push (hexDigit (c.toNat / 16)) |>.push (hexDigit (c.toNat % 16))
             else out.push c
  return out.push '"'

/-- Keys in code-point order (UTF-8 byte order), stable. -/
def sortKV (kvs : Array (String × JV)) : Array (String × JV) :=
  (kvs.toList.mergeSort fun a b => !(b.1 < a.1)).toArray

/-- Compact text with sorted keys. -/
partial def write : JV → String
  | .null => "null"
  | .bool b => if b then "true" else "false"
  | .num t => t
  | .str s => escape s
  | .arr xs => "[" ++ ",".intercalate (xs.toList.map write) ++ "]"
  | .obj kvs => "{" ++ ",".intercalate ((sortKV kvs).toList.map fun (k, v) => escape k ++ ":" ++ write v) ++ "}"

/-- Compact text with sorted keys and `.withoutEscapingSlashes` (the card form). -/
partial def writeUnescaped : JV → String
  | .str s => escape s false
  | .arr xs => "[" ++ ",".intercalate (xs.toList.map writeUnescaped) ++ "]"
  | .obj kvs => "{" ++ ",".intercalate ((sortKV kvs).toList.map fun (k, v) => escape k false ++ ":" ++ writeUnescaped v) ++ "}"
  | v => write v

/-- `[.prettyPrinted, .sortedKeys, .withoutEscapingSlashes]`: two-space indent, `"k" : v`, and an empty
collection as its brackets around a blank line (as measured on Foundation). -/
partial def writePretty (indent : String := "") : JV → String
  | .str s => escape s false
  | .arr xs =>
    let inner := indent ++ "  "
    if xs.isEmpty then "[\n\n" ++ indent ++ "]"
    else "[\n" ++ ",\n".intercalate (xs.toList.map fun x => inner ++ writePretty inner x) ++ "\n" ++ indent ++ "]"
  | .obj kvs =>
    let inner := indent ++ "  "
    if kvs.isEmpty then "{\n\n" ++ indent ++ "}"
    else "{\n" ++ ",\n".intercalate ((sortKV kvs).toList.map fun (k, v) => inner ++ escape k false ++ " : " ++ writePretty inner v) ++
      "\n" ++ indent ++ "}"
  | v => write v

/-! ## Values -/

def ofDouble (x : Float) : JV := .num (SwiftDouble.jsonText x)
def ofInt (n : Int) : JV := .num (toString n)
def ofData (b : ByteArray) : JV := .str (Base64.encode b)

/-! ## Decoding (`Decodable` semantics) -/

abbrev D := Except String

def typeMismatch {α} : D α := throw "typeMismatch"
def dataCorrupted {α} : D α := throw "dataCorrupted"

/-- The exact value of a number token: sign, digits, decimal exponent. -/
def numParts (t : String) : Option (Bool × Nat × Int) := Id.run do
  let neg := t.startsWith "-"
  let body := if neg then (t.drop 1).toString else t
  let (mant, ex) := match body.splitOn "e" with
    | [m, e] => (m, e)
    | _ => (body, "0")
  let exN : Int := match ex.toInt? with
    | some v => v
    | none => match (ex.drop 1).toString.toNat? with | some v => v | none => 0
  let (ip, fp) := match mant.splitOn "." with
    | [a, b] => (a, b)
    | _ => (mant, "")
  let some n := (ip ++ fp).toNat? | return none
  return some (neg, n, exN - fp.length)

/-- An integer in `[lo, hi]` from a number token (`1.0` and `1e2` are integers; a fraction or an
out-of-range value is `dataCorrupted`). -/
def intIn (lo hi : Int) : JV → D Int
  | .num t => do
    let some (neg, n, x) := numParts t | dataCorrupted
    let mag : Option Nat :=
      if n == 0 then some 0
      else if x ≥ 0 then (if x > 40 then none else some (n * 10 ^ x.toNat))
      else if (-x) > 400 then none
      else let q := 10 ^ (-x).toNat; if n % q == 0 then some (n / q) else none
    let some m := mag | dataCorrupted
    let v : Int := if neg then -(m : Int) else m
    unless lo ≤ v && v ≤ hi do dataCorrupted
    return v
  | .null => throw "valueNotFound"
  | _ => typeMismatch

def asUInt32 (v : JV) : D UInt32 := return (← intIn 0 0xFFFF_FFFF v).toNat.toUInt32
def asInt64 (v : JV) : D Int64 := return Int64.ofInt (← intIn (-(2 ^ 63)) (2 ^ 63 - 1) v)
def asInt (v : JV) : D Int := intIn (-(2 ^ 63)) (2 ^ 63 - 1) v

def asDouble : JV → D Float
  | .num t => do
    let some (neg, n, x) := numParts t | dataCorrupted
    let f := SwiftDouble.ofDecimal neg n x
    -- overflow to infinity, or a nonzero literal that rounds to zero, is refused (as measured)
    if f.isInf || (n != 0 && f == 0) then dataCorrupted
    return f
  | .null => throw "valueNotFound"
  | _ => typeMismatch

def asString : JV → D String
  | .str s => pure s
  | .null => throw "valueNotFound"
  | _ => typeMismatch

def asBool : JV → D Bool
  | .bool b => pure b
  | .null => throw "valueNotFound"
  | _ => typeMismatch

/-- `Data` (base64, as `JSONDecoder`'s default `.base64` strategy). -/
def asData (v : JV) : D ByteArray := do
  let s ← asString v
  match Base64.decode? s with
  | some b => pure b
  | none => dataCorrupted

def asArray {α} (f : JV → D α) : JV → D (Array α)
  | .arr xs => xs.mapM f
  | .null => throw "valueNotFound"
  | _ => typeMismatch

/-- A keyed container. -/
def asObject : JV → D (Array (String × JV))
  | .obj kvs => pure kvs
  | .null => throw "valueNotFound"
  | _ => typeMismatch

def lookup (kvs : Array (String × JV)) (k : String) : Option JV := (kvs.find? (·.1 == k)).map (·.2)

def contains (kvs : Array (String × JV)) (k : String) : Bool := (lookup kvs k).isSome

/-- `container.decode(_:forKey:)`. -/
def key {α} (kvs : Array (String × JV)) (k : String) (f : JV → D α) : D α :=
  match lookup kvs k with
  | none => throw "keyNotFound"
  | some .null => throw "valueNotFound"
  | some v => f v

/-- `container.decodeIfPresent(_:forKey:)`. -/
def keyIfPresent {α} (kvs : Array (String × JV)) (k : String) (f : JV → D α) : D (Option α) :=
  match lookup kvs k with
  | none | some .null => pure none
  | some v => some <$> f v

/-- `JSONDecoder().decode(_:from:)`: invalid JSON text is `dataCorrupted`. -/
def decodeText {α} (text : String) (f : JV → D α) : D α :=
  match parse? text with
  | none => dataCorrupted
  | some v => f v

end Winnow.SwiftJSON
