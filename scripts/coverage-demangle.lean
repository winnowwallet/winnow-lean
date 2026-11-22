import Lean.Compiler.NameMangling

/-! C symbols to the Lean names they mangle, for scripts/coverage: one symbol a line in, the symbol, a tab and
the name's components (separated by U+001F, numbers as `#n`) out, or nothing after the tab for a symbol that is
not a Lean name. `lean --run scripts/coverage-demangle.lean`, from Lean/ for its toolchain. -/
open Lean

/-- `lp_<package>_<body>` or `l_<body>`: the declaration name the body mangles, as its components. -/
def body? (s : String) : Option Name := do
  if s.startsWith "l_" then return ← Name.demangle? (s.drop 2).copy
  let rest := (← (if s.startsWith "lp_" then some (s.drop 3).copy else none))
  let cs := rest.toList
  for i in [1:cs.length] do
    if cs[i]! == '_' then
      let pkg := String.ofList (cs.take i)
      let body := String.ofList (cs.drop (i + 1))
      if let some (.str .anonymous _) := Name.demangle? pkg then
        if let some n := Name.demangle? body then return n
  none

def parts : Name → List String
  | .anonymous => []
  | .str p s => parts p ++ [s]
  | .num p n => parts p ++ ["#" ++ toString n]

def main : IO Unit := do
  let stdin ← IO.getStdin
  let out ← IO.getStdout
  repeat
    let line ← stdin.getLine
    if line.isEmpty then break
    let sym := line.trimAscii.copy
    match body? sym with
    | some n => out.putStrLn (sym ++ "\t" ++ "\u001f".intercalate (parts n))
    | none => out.putStrLn (sym ++ "\t")
