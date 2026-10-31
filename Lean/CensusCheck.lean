import Winnow.IO
open Winnow Winnow.IO

/-! `census-check <peers.json>`: the census list a build is about to ship, held to the app's own rules
(`CensusCatalog.readFile`, what `CensusCatalog.bundled` reads at launch: at most 4 MiB, schema 1, a strict
date, a positive tip, at least `minimumClearnetEntries` clearnet entries, each network's entry rules).
`scripts/import-census` runs it on the file it writes; CI runs it on the shipped file. Prints the date,
the tip and the validated entries per network; exits 1 when the app would not use the list. -/

def main (args : List String) : IO UInt32 := do
  let [path] := args | IO.eprintln "usage: census-check <peers.json>"; return 2
  match ← (CensusCatalog.readFile path).toBaseIO with
  | .error e =>
    IO.eprintln s!"census-check: {path}: {e}"
    return 1
  | .ok (.error e) =>
    let detail := match e with | .decoding reason => s!" ({reason})" | .invalid _ => ""
    IO.eprintln s!"census-check: {path} is not a list the app would use: {e.name}{detail}"
    return 1
  | .ok (.ok c) =>
    let counts := c.networks.toList.map fun (n, es) => s!"{es.size} {n}"
    IO.println s!"census-check: {path}: {c.date}, tip {c.tip}: {", ".intercalate counts} (at least {CensusCatalog.minimumClearnetEntries} clearnet required)"
    return 0
