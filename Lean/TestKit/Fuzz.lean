/-! # Deterministic fuzzing: the harness

The port of upstream's `Tools/Fuzz`. One seed drives everything, so a failure replays from the line it prints:
every iteration takes each target in turn, mutates one of its seed inputs and hands the bytes to the target's
check. A check answers whether the parser took the input, and throws when a result breaks the target's invariant
(`Fuzz.require`). A parser refusing is not a finding.

**What Lean changes from upstream.** Swift trapped on a bad index; compiled Lean does not, so three things stand in
for the trap:

* the run is a child process under `LEAN_ABORT_ON_PANIC=1`, which turns an `Array` `[i]!` or a `panic!` out of
  bounds into an abort. Without it the runtime prints a line and carries on with a default value. A `ByteArray`
  `[i]!` out of bounds never panics at all: it reads 0 (`lean_byte_array_get`), so only a target's invariant can
  see one of those;
* the parent watches the child's marker, which names the case in flight, and kills it when one case stalls for
  `stallSeconds`: a hang is a finding, and a parser takes hostile lengths from a peer;
* a crash can't report itself, so the parent prints the marker's case and the command that replays it.

**A target that accepts nothing tests nothing.** The run refuses to start unless at least one of a target's seeds
parses, and prints how many mutated inputs each target took, so a seed that rots shows up as a failure and a
target that only ever exercises its first refusal shows up in the numbers.

`Vectors/fuzz/<target>/*.bin` are inputs that once broke a parser, replayed first on every run. -/

namespace TestKit.Fuzz

abbrev Rng := IO.Ref UInt64

/-- SplitMix64, upstream's generator. -/
def next (rng : Rng) : IO UInt64 := do
  let state := (← rng.get) + 0x9E3779B97F4A7C15
  rng.set state
  let a := (state ^^^ (state >>> 30)) * 0xBF58476D1CE4E5B9
  let b := (a ^^^ (a >>> 27)) * 0x94D049BB133111EB
  return b ^^^ (b >>> 31)

def index (rng : Rng) (upperBound : Nat) : IO Nat := do
  if upperBound == 0 then return 0
  return (← next rng).toNat % upperBound

/-- A result broke a bound the wallet relies on. -/
def require (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

structure Target where
  name : String
  seeds : Array ByteArray
  /-- Whether the parser took the input; throws on a broken invariant. -/
  check : Rng → ByteArray → IO Bool
  /-- The grammar's own pieces, spliced in by the mutator: a text format refuses nearly every random byte, so
  without them its fuzzing stops at the first refusal. -/
  tokens : Array ByteArray := #[]

/-- The lengths that attack a parser: CompactSize prefixes promising far more than follows. -/
private def bombs : Array ByteArray :=
  #[⟨#[0xFF]⟩, ⟨#[0xFD, 0xFF, 0xFF]⟩, ⟨#[0xFE, 0xFF, 0xFF, 0xFF, 0xFF]⟩,
    ⟨#[0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF]⟩]

private def insertAt (b piece : ByteArray) (at_ : Nat) : ByteArray :=
  b.extract 0 at_ ++ piece ++ b.extract at_ b.size

/-- Upstream's mutator: edits, each a bit flip, a byte overwritten, inserted or removed, a cut tail, a block copied
within the input, or a length bomb; and here also one of the target's `tokens`. Half the inputs take one edit,
since most formats refuse a second. -/
def mutate (source : ByteArray) (rng : Rng) (maximum : Nat) (tokens : Array ByteArray := #[]) : IO ByteArray := do
  let mut b := source.extract 0 maximum
  let one := (← index rng 2) == 0
  let many := 1 + (← index rng 8)
  let edits := if one then 1 else many
  for _ in [:edits] do
    match ← index rng (if tokens.isEmpty then 7 else 10) with
    | 0 =>
      if b.isEmpty then continue
      let i ← index rng b.size
      b := b.set! i (b[i]! ^^^ (1 <<< (← index rng 8)).toUInt8)
    | 1 =>
      if b.isEmpty then continue
      b := b.set! (← index rng b.size) (← next rng).toUInt8
    | 2 =>
      if b.size >= maximum then continue
      b := insertAt b ⟨#[(← next rng).toUInt8]⟩ (← index rng (b.size + 1))
    | 3 =>
      if b.isEmpty then continue
      let i ← index rng b.size
      b := b.extract 0 i ++ b.extract (i + 1) b.size
    | 4 =>
      if b.isEmpty then continue
      b := b.extract 0 (← index rng b.size)
    | 5 =>
      if b.isEmpty || b.size >= maximum then continue
      let start ← index rng b.size
      let length := min (1 + (← index rng (min 32 (b.size - start)))) (maximum - b.size)
      b := insertAt b (b.extract start (start + length)) (← index rng (b.size + 1))
    | 7 | 8 | 9 =>
      let token := tokens[← index rng tokens.size]!
      let room := maximum - b.size
      if room < token.size then continue
      b := insertAt b token (← index rng (b.size + 1))
    | _ =>
      let room := maximum - b.size
      if room == 0 then continue
      let bomb := bombs[← index rng bombs.size]!
      b := insertAt b (bomb.extract 0 room) (← index rng (b.size + 1))
  return b

structure Options where
  iterations : Nat := 1000
  seed : UInt64 := 0x57494E4E4F575055
  target : Option String := none
  maxInput : Nat := 16384
  /-- Where a failing input, and each case before it runs, is written as bytes. -/
  save : Option System.FilePath := none
  deriving Inhabited

private def hexDigit? (c : Char) : Option Nat :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c ∧ c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else none

private def parseNumber? (text : String) : Option Nat :=
  if text.startsWith "0x" then
    (text.drop 2).toString.foldl (fun acc c => do return (← acc) * 16 + (← hexDigit? c)) (some 0)
  else text.toNat?

private def parseOptions : List String → Options → Except String Options
  | [], o => pure o
  | "--iterations" :: v :: rest, o =>
    match parseNumber? v with
    | some n => parseOptions rest { o with iterations := n }
    | none => throw s!"--iterations {v}"
  | "--seed" :: v :: rest, o =>
    match parseNumber? v with
    | some n => parseOptions rest { o with seed := n.toUInt64 }
    | none => throw s!"--seed {v}"
  | "--target" :: v :: rest, o => parseOptions rest { o with target := if v == "all" then none else some v }
  | "--max-input" :: v :: rest, o =>
    match parseNumber? v with
    | some n => parseOptions rest { o with maxInput := n }
    | none => throw s!"--max-input {v}"
  | "--save" :: v :: rest, o => parseOptions rest { o with save := some v }
  | other :: _, _ => throw s!"unknown argument {other}"

private def seedHex (seed : UInt64) : String := "0x" ++ String.ofList (Nat.toDigits 16 seed.toNat)

private def hex (b : ByteArray) : String :=
  b.foldl (fun acc x => acc ++ (String.ofList (Nat.toDigits 16 (x.toNat / 16 % 16) ++ Nat.toDigits 16 (x.toNat % 16)))) ""

private def say (line : String) : IO Unit := do
  let out ← IO.getStdout
  out.putStrLn line
  out.flush

private def replayLine (exe : String) (o : Options) (targets : String) (iteration : Nat) : String :=
  s!"{exe} --target {targets} --seed {seedHex o.seed} --max-input {o.maxInput} --iterations {iteration + 1}"

/-- Runs one check with what a finding needs around it: the input, and what replays it. -/
private def attempt (t : Target) (rng : Rng) (input : ByteArray) (o : Options) (where_ : String) : IO Bool := do
  try t.check rng input
  catch e =>
    IO.eprintln s!"fuzz: FINDING target={t.name} {where_}: {e}"
    if input.size ≤ 4096 then IO.eprintln s!"fuzz: input {hex input}"
    if let some dir := o.save then
      IO.FS.createDirAll dir
      IO.FS.writeBinFile (dir / s!"{t.name}-{seedHex o.seed}.bin") input
    IO.Process.exit 1

/-- `Vectors/fuzz/<target>/*.bin`, replayed under the target's own check. -/
private def replayCorpus (targets : Array Target) (corpus : System.FilePath) (o : Options) : IO Nat := do
  unless ← corpus.isDir do throw (IO.userError s!"no corpus at {corpus}: run from the package directory")
  let rng ← IO.mkRef 0x5749_4E4E_4F57_4655
  let mut replayed := 0
  for entry in (← corpus.readDir) do
    let some t := targets.find? (·.name == entry.fileName)
      | throw (IO.userError s!"{entry.path} names no fuzz target")
    for file in (← entry.path.readDir) do
      if file.path.extension != some "bin" then continue
      discard <| attempt t rng (← IO.FS.readBinFile file.path) o s!"corpus {file.path}"
      replayed := replayed + 1
  return replayed

private structure Tally where
  took : Nat := 0
  slowestMs : Nat := 0
  deriving Inhabited

/-- The run itself, in the child. -/
private def child (all : Array Target) (o : Options) (exe : String) (corpus marker : System.FilePath) : IO UInt32 := do
  let targets : Array Target := match o.target with
    | some n => all.filter fun (t : Target) => t.name == n
    | none => all
  if targets.isEmpty then
    IO.eprintln s!"fuzz: no target {o.target.getD ""}: {all.map Target.name}"
    return 2
  let selection := o.target.getD "all"
  IO.FS.writeFile marker "the corpus\n"
  let replayed ← replayCorpus all corpus o
  let seedRng ← IO.mkRef 1
  for t in targets do
    IO.FS.writeFile marker s!"target={t.name}'s seeds\n"
    let mut anyTaken := false
    for s in t.seeds do
      anyTaken := (← attempt t seedRng s o "a seed") || anyTaken
    unless anyTaken do
      IO.eprintln s!"fuzz: target={t.name}: no seed parses, so its fuzzing would only test refusals"
      return 1
  say s!"fuzz: seed={seedHex o.seed} iterations={o.iterations} max-input={o.maxInput} targets={selection}"
  let rng ← IO.mkRef o.seed
  let mut tallies : Array Tally := targets.map fun _ => {}
  for iteration in [:o.iterations] do
    for h : k in [:targets.size] do
      let t := targets[k]'h.2.1
      IO.FS.writeFile marker s!"target={t.name} iteration={iteration}\n{replayLine exe o selection iteration}\n"
      let seed := t.seeds[← index rng t.seeds.size]!
      let input ← mutate seed rng o.maxInput t.tokens
      if let some dir := o.save then
        IO.FS.createDirAll dir
        IO.FS.writeBinFile (dir / "in-flight.bin") input
      let start ← IO.monoMsNow
      let took ← attempt t rng input o s!"seed={seedHex o.seed} iteration={iteration}: replay: {replayLine exe o selection iteration}"
      let ms := (← IO.monoMsNow) - start
      tallies := tallies.modify k fun c =>
        { took := c.took + (if took then 1 else 0), slowestMs := max c.slowestMs ms }
  for h : k in [:targets.size] do
    let t := targets[k]'h.2.1
    let c := tallies[k]!
    say s!"  {t.name}: took {c.took} of {o.iterations}, slowest {c.slowestMs} ms"
  say s!"fuzz: passed {o.iterations * targets.size} cases and {replayed} corpus inputs (seed {seedHex o.seed})"
  return 0

/-- How long one case may run before the parent calls it a hang. -/
def stallSeconds : Nat := 30

/-- The parent: runs the child under `LEAN_ABORT_ON_PANIC`, watches it, and names what a crash or a hang was. -/
private def parent (args : List String) (exe : String) (marker : System.FilePath) : IO UInt32 := do
  let spawned ← IO.Process.spawn {
    cmd := exe, args := args.toArray
    env := #[("LEAN_ABORT_ON_PANIC", some "1"), ("WINNOW_FUZZ_MARKER", some marker.toString)] }
  let readMarker : IO String := do
    try IO.FS.readFile marker catch _ => pure ""
  let rec watch (last : String) (still : Nat) (fuel : Nat) : IO UInt32 := do
    match fuel with
    | 0 => return 3
    | fuel + 1 =>
      IO.sleep 1000
      if let some code ← spawned.tryWait then return code
      -- an empty read is the child between truncating the marker and writing it, so it moved on
      let now ← readMarker
      if now.isEmpty || now != last then return ← watch now 0 fuel
      if still + 1 < stallSeconds then return ← watch now (still + 1) fuel
      spawned.kill
      IO.eprintln s!"fuzz: FINDING: no progress for {stallSeconds} s in\n{now}"
      return 1
  let code ← watch "" 0 (100 * 24 * 3600)
  if code != 0 && code != 1 && code != 2 then
    IO.eprintln s!"fuzz: FINDING: the run crashed (exit {code}) in\n{← readMarker}"
    return 1
  return code

/-- The `main` of a fuzz executable; `corpus` is relative to the package directory it runs from. -/
def main (targets : Array Target) (corpus : System.FilePath) (args : List String) : IO UInt32 := do
  let options ← match parseOptions args {} with
    | .ok o => pure o
    | .error e =>
      IO.eprintln s!"fuzz: {e}\nusage: fuzz [--iterations N] [--seed N|0xHEX] [--target NAME|all] [--max-input N] [--save DIR]"
      return 2
  let exe := (← IO.appPath).toString
  match ← IO.getEnv "WINNOW_FUZZ_MARKER" with
  | some marker => child targets options exe corpus marker
  | none =>
    let (_, marker) ← IO.FS.createTempFile
    let code ← parent args exe marker
    try IO.FS.removeFile marker catch _ => pure ()
    IO.Process.exit code.toUInt8

end TestKit.Fuzz
