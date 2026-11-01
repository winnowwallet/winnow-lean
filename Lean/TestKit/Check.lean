/-! # The tally every test executable keeps, and how it prints

One tally per process (the passes counted, the failures named), `check` to add to it, `runTest` for a named
test that may abort, the unwrapping helpers that abort one (`need`, `needE`) or check a refusal (`refused`), and
`runMain`, the `main` of every executable: it runs the tests, prints the summary line and exits with the verdict.

The executables had three conventions: io-test and backend-test printed an indented `ok`/`FAIL name — detail`
line per check and named the failures in the summary; the unit tests counted passes silently and printed
`FAIL name: detail`; silent-payment-test and ledger-transport-test printed `FAIL name` on standard error with
the counts only. The first is kept, with the passes silent unless the executable asks for them:

* a failure is `  FAIL name — detail` on standard output, flushed at once, so it lands between the lines a long
  run prints (`runTest`'s timings, a regtest flow's progress) and not in another stream;
* a pass prints `  ok   name — detail` only under `runMain`'s `progress`: io-test and backend-test, whose
  checks are the steps of one flow against a node, so the ok lines are the run's progress; the unit tests make
  hundreds of checks (every Wycheproof vector) whose passes would bury the failures;
* the summary `<executable>: P passed, F failed: name, …` names the failures, so a CI log's last line says what
  broke;
* the exit code goes through `IO.Process.exit`: the runtime waits for every task at exit (the app's peer
  pools' monitors, a watchdog), so a `main` that returns can hang. -/

namespace TestKit

structure Tally where
  passed : Nat := 0
  failures : Array String := #[]
  deriving Inhabited

initialize tally : IO.Ref Tally ← IO.mkRef {}
/-- Whether a pass prints its line (`runMain`'s `progress`). -/
initialize progressLines : IO.Ref Bool ← IO.mkRef false
/-- `<EXECUTABLE>_ONLY=<substring>`: `runTest` runs only the tests whose name contains it. -/
initialize onlyTests : IO.Ref (Option String) ← IO.mkRef none

/-- A line on standard output, flushed. -/
def say (s : String) : IO Unit := do IO.println s; (← IO.getStdout).flush

private def line (mark name detail : String) : String :=
  s!"  {mark} {name}{if detail.isEmpty then "" else " — " ++ detail}"

/-- A failure, with what was seen. -/
def fail (name : String) (detail : String := "") : IO Unit := do
  tally.modify fun t => { t with failures := t.failures.push name }
  say (line "FAIL" name detail)

def check (name : String) (ok : Bool) (detail : String := "") : IO Unit := do
  if ok then
    tally.modify fun t => { t with passed := t.passed + 1 }
    if ← progressLines.get then say (line "ok  " name detail)
  else fail name detail

/-! ## Unwrapping -/

/-- How a test shows an error: `name` (the case, what `refused` compares a kind with) and the text an abort or
a `got …` detail carries. -/
class Describe (ε : Type) where
  name : ε → String
  describe : ε → String := name

instance : Describe String := ⟨id, id⟩

/-- What a test's step returns, as an `Except`: a pure `Except ε` or an `ExceptT ε IO` (MAM, WM, RM, …). -/
class Outcome (m : Type → Type) (ε : outParam Type) where
  outcome {α : Type} : m α → IO (Except ε α)

instance : Outcome (Except ε) ε := ⟨fun r => pure r⟩
instance : Outcome (ExceptT ε IO) ε := ⟨ExceptT.run⟩

/-- The value, or the test aborts with `name: <the error>` (`runTest` records it). In IO or a test's own
monad over it (`TM`). -/
def need {m ε α n} [Outcome m ε] [Describe ε] [MonadLiftT IO n] (name : String) (x : m α) : n α :=
  liftM (m := IO) do
    match ← Outcome.outcome x with
    | .ok a => pure a
    | .error e => throw (IO.userError s!"{name}: {Describe.describe e}")

/-- `need` for an error of another module, shown by `render`. -/
def needE {ε α n} [MonadLiftT IO n] (name : String) (render : ε → String) (r : Except ε α) : n α :=
  liftM (m := IO) do
    match r with
    | .ok a => pure a
    | .error e => throw (IO.userError s!"{name}: {render e}")

/-- `needE`'s `render` for an error a test does not show. -/
def unnamed {ε} (_ : ε) : String := "failed"

/-- Expects a failure: of the case `kind` when it is given, and one `matching` accepts. -/
def refused {m ε α} [Outcome m ε] [Describe ε] (name : String) (x : m α) (kind : String := "")
    (matching : ε → Bool := fun _ => true) : IO Unit := do
  match ← Outcome.outcome x with
  | .ok _ => check name false "accepted"
  | .error e => check name ((kind.isEmpty || Describe.name e == kind) && matching e) s!"got {Describe.describe e}"

/-! ## Tests and the executable's main -/

/-- A test that may abort by `throw`ing a message (or by an IO error, a `need`). -/
abbrev TM := ExceptT String IO

/-- Runs a named test: an abort is a failure of the test's name; prints its time. -/
def runTest (name : String) (t : TM Unit) : IO Unit := do
  if let some only ← onlyTests.get then
    unless (name.splitOn only).length > 1 do return
  let start ← IO.monoMsNow
  match ← (try t.run catch e => pure (.error (toString e))) with
  | .ok () => pure ()
  | .error msg => fail name s!"aborted: {msg}"
  say s!"  {name}: {(← IO.monoMsNow) - start} ms"

/-- The `main` of a test executable: runs `body` (an exception is a failure), prints
`<exe>: P passed, F failed[: names]` and exits 0 when nothing failed, else 1. `progress` prints every pass. -/
def runMain (exe : String) (body : IO Unit) (progress := false) : IO UInt32 := do
  progressLines.set progress
  let var := (exe.map fun c => if c == '-' then '_' else c.toUpper) ++ "_ONLY"
  onlyTests.set (← IO.getEnv var)
  try body catch e => fail "exception" (toString e)
  let t ← tally.get
  say s!"{exe}: {t.passed} passed, {t.failures.size} failed{if t.failures.isEmpty then "" else ": " ++ ", ".intercalate t.failures.toList}"
  IO.Process.exit (if t.failures.isEmpty then 0 else 1)

end TestKit
