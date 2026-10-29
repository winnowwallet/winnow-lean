import Lean.Data.Json
import Std.Data.HashMap
import Winnow.Bytes

/-! The oracle's request plumbing: one JSON request per line, one JSON reply. Bytes are hex strings;
64-bit integers are decimal strings (JSON numbers are doubles in the Swift driver). -/

namespace Oracle
open Lean Winnow

abbrev Handler := Json → Except String Json

def str (j : Json) (k : String) : Except String String := j.getObjValAs? String k
def nat (j : Json) (k : String) : Except String Nat := j.getObjValAs? Nat k
def bytes (j : Json) (k : String) : Except String ByteArray := do
  let s ← str j k
  match ofHex? s with
  | some b => pure b
  | none => throw s!"{k}: not hex"
def u64 (j : Json) (k : String) : Except String UInt64 := do
  match (← str j k).toNat? with
  | some n => pure n.toUInt64
  | none => throw s!"{k}: not a decimal string"

def ok (v : Json) : Json := Json.mkObj [("ok", v)]
def err (name : String) : Json := Json.mkObj [("error", Json.str name)]
def hexJ (b : ByteArray) : Json := Json.str (hex b)

/-- One JSON request per line on stdin, one reply per line on stdout, until EOF. Replies: `{"ok":…}` or
`{"error":"<kind>"}` (`unsupported` for an unknown op, `bad-request: …` for malformed arguments). -/
def answer (ops : Std.HashMap String Handler) (line : String) : Json :=
  match Json.parse line with
  | .error e => err s!"bad-json: {e}"
  | .ok j =>
    match j.getObjValAs? String "op" with
    | .error _ => err "bad-json: op"
    | .ok op =>
      match ops[op]? with
      | none => err "unsupported"
      | some h => match h j with
        | .ok r => r
        | .error e => err s!"bad-request: {e}"

partial def loop (ops : Std.HashMap String Handler) (stdin : IO.FS.Stream) (stdout : IO.FS.Stream) : IO Unit := do
  let line ← stdin.getLine
  if line.isEmpty then return
  stdout.putStrLn (answer ops line.trimAscii.copy).compress
  stdout.flush
  loop ops stdin stdout


def run (ops : List (String × Handler)) : IO Unit := do
  loop (Std.HashMap.ofList ops) (← IO.getStdin) (← IO.getStdout)

end Oracle
