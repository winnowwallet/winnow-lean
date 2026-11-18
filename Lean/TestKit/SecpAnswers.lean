import Lean.Data.Json
import Secp.Bytes
import TestKit.Check

/-! # Every curve operation the wallet uses, against answers computed without it

`Vectors/secp-known-answers.json` is written by `scripts/secp-vectors`: secp256k1 in the plainest form there
is (affine points on Python integers), with none of the wallet's code. It says what each operation must
return for the edges of that operation and a seeded stream of inputs, and where it must refuse.

`check` holds an implementation to every record. The implementation is given as functions of bytes
(`Curve`), so the test says nothing of how the curve is computed: `secpct-test` gives it the wallet's. -/

namespace TestKit.SecpAnswers
open Lean

/-- The curve as the vectors see it: bytes in, bytes out, `none` for a refusal. -/
structure Curve where
  /-- A 32-byte secret's compressed public key. -/
  publicKey : ByteArray → Option ByteArray
  /-- The even y for a 32-byte x. -/
  liftX : ByteArray → Option ByteArray
  /-- A public key of 33 or 65 bytes as its x and y. -/
  parse : ByteArray → Option (ByteArray × ByteArray)
  /-- `t·G + P`, compressed. -/
  pointAdd : (point tweak : ByteArray) → Option ByteArray
  /-- `t·G + lift_x(x)`: its x, and whether its y is odd. -/
  xonlyAdd : (x tweak : ByteArray) → Option (ByteArray × Bool)
  /-- `t·P`, compressed. -/
  pointMul : (point scalar : ByteArray) → Option ByteArray
  /-- The sum of compressed points. -/
  combine : Array ByteArray → Option ByteArray
  /-- `(d + t) mod N`. -/
  secretAdd : (secret tweak : ByteArray) → Option ByteArray
  /-- The same after negating `d` when `d·G` has an odd y. -/
  secretAddXOnly : (secret tweak : ByteArray) → Option ByteArray
  bip340Sign : (secret message aux : ByteArray) → Option ByteArray
  bip340Verify : (key message signature : ByteArray) → Bool
  ecdsaSign : (secret digest aux : ByteArray) → Option ByteArray
  ecdsaVerify : (key digest signature : ByteArray) → Bool

private def bytes? (j : Json) (key : String) : Option ByteArray :=
  match j.getObjVal? key with
  | .ok (.str text) => Secp.ofHex? text
  | _ => none

private def bytes (j : Json) (key : String) : ByteArray := (bytes? j key).getD .empty

private def flag (j : Json) (key : String) : Bool := (j.getObjValAs? Bool key).toOption.getD false

private def records (file : Json) (kind : String) : Array Json := (file.getObjValAs? (Array Json) kind).toOption.getD #[]

private def same (a b : Option ByteArray) : Bool :=
  match a, b with
  | some x, some y => x.data == y.data
  | none, none => true
  | _, _ => false

private def shown (a : Option ByteArray) : String := match a with | some x => Secp.toHex x | none => "refused"

/-- One kind of record: each must give what the file says. The kind must have its records, and both sorts of
them: answers (`answer` names the field that holds one, or the flag that says a signature is good) and
refusals. A file read wrongly would otherwise agree with an implementation that refuses everything. -/
private def each (file : Json) (kind : String) (minimum : Nat) (answer : String) (one : Json → Option String) :
    IO Unit := do
  let rows := records file kind
  let answered := (rows.filter fun r => match r.getObjVal? answer with
    | .ok (.str text) => (Secp.ofHex? text).isSome
    | .ok (.bool good) => good
    | _ => false).size
  check s!"known answers: {kind} has its records, answers and refusals among them"
    (rows.size ≥ minimum && answered ≥ 2 && answered < rows.size) s!"{rows.size}, {answered} answered"
  let mut wrong := 0
  let mut first := ""
  for h : i in [0:rows.size] do
    if let some detail := one rows[i] then
      if wrong == 0 then first := s!"record {i}: {detail}"
      wrong := wrong + 1
  check s!"known answers: {kind}, all {rows.size}" (wrong == 0) s!"{wrong} wrong; {first}"

/-- Holds `c` to every record of the file (run from `Lean/`). -/
def check (c : Curve) (path : String := "Vectors/secp-known-answers.json") : IO Unit := do
  let file ← IO.ofExcept (Json.parse (← IO.FS.readFile path))
  let expect (got want : Option ByteArray) : Option String :=
    if same got want then none else some s!"got {shown got}, want {shown want}"
  each file "publicKey" 30 "public" fun r => expect (c.publicKey (bytes r "secret")) (bytes? r "public")
  each file "liftX" 40 "y" fun r => expect (c.liftX (bytes r "x")) (bytes? r "y")
  each file "parse" 60 "x" fun r =>
    let got := c.parse (bytes r "bytes")
    match expect (got.map (·.1)) (bytes? r "x") with
    | some detail => some detail
    | none => expect (got.map (·.2)) (bytes? r "y")
  each file "pointAdd" 60 "result" fun r => expect (c.pointAdd (bytes r "point") (bytes r "tweak")) (bytes? r "result")
  each file "xonlyAdd" 60 "result" fun r =>
    let got := c.xonlyAdd (bytes r "x") (bytes r "tweak")
    match expect (got.map (·.1)) (bytes? r "result") with
    | some detail => some detail
    | none => if (got.map (·.2)).getD false == flag r "odd" then none else some "the parity of y differs"
  each file "pointMul" 60 "result" fun r => expect (c.pointMul (bytes r "point") (bytes r "scalar")) (bytes? r "result")
  each file "combine" 8 "result" fun r =>
    let points := (records r "points").filterMap fun p => match p with | .str text => Secp.ofHex? text | _ => none
    expect (c.combine points) (bytes? r "result")
  each file "secretAdd" 150 "result" fun r => expect (c.secretAdd (bytes r "secret") (bytes r "tweak")) (bytes? r "result")
  each file "secretAddXOnly" 150 "result" fun r =>
    expect (c.secretAddXOnly (bytes r "secret") (bytes r "tweak")) (bytes? r "result")
  each file "bip340Sign" 30 "signature" fun r =>
    expect (c.bip340Sign (bytes r "secret") (bytes r "message") (bytes r "aux")) (bytes? r "signature")
  each file "bip340Verify" 250 "valid" fun r =>
    if c.bip340Verify (bytes r "key") (bytes r "message") (bytes r "signature") == flag r "valid" then none
    else some s!"want {flag r "valid"}"
  each file "ecdsaSign" 30 "signature" fun r =>
    expect (c.ecdsaSign (bytes r "secret") (bytes r "digest") (bytes r "aux")) (bytes? r "signature")
  each file "ecdsaVerify" 290 "valid" fun r =>
    if c.ecdsaVerify (bytes r "key") (bytes r "digest") (bytes r "signature") == flag r "valid" then none
    else some s!"want {flag r "valid"}"

end TestKit.SecpAnswers
