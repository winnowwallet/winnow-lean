import Lean.Data.Json
import WinnowApp.E2E

/-! `oracle-e2e`: the Lean side of `LeanOracle/E2E/main.swift` (lockstep generator
`LeanOracle/gen/f_e2e.py`): the app's test mode (`WinnowApp/E2E.lean`). One JSON request per line on
stdin, one reply per line.

Ops: `e2e.resolve` (the launch environment → inactive, missing entropy, or the mode's fields, the sync
interval in whole milliseconds and the custom signet's magic), `e2e.looksSecret`, `e2e.carriesSeed`,
`e2e.fieldName` (the journal's field-name rule). `e2e.censusKeys` went with the census download. -/

open Lean Winnow WinnowApp

def ok (v : Json) : Json := Json.mkObj [("ok", v)]
def errJ (name : String) : Json := Json.mkObj [("error", .str name)]
def jopt {α} (f : α → Json) : Option α → Json | some a => f a | none => .null
def bad {α} (what : String) : IO α := throw (IO.userError s!"bad-request: {what}")
def strJ (j : Json) (k : String) : IO String :=
  match j.getObjValAs? String k with | .ok s => pure s | .error _ => bad k

def envOf (j : Json) : List (String × String) :=
  match j.getObjVal? "env" with
  | .ok (.obj kvs) => kvs.toList.filterMap fun (k, v) => match v with | .str s => some (k, s) | _ => none
  | _ => []

def describe (m : E2E.Mode) : Json :=
  Json.mkObj
    [ ("runID", .str m.runID), ("peer", jopt .str m.peer), ("challenge", jopt (.str ∘ hex) m.challenge)
    , ("entropy", jopt (.str ∘ hex) m.entropy), ("reset", .bool m.reset), ("clipboard", jopt .str m.clipboard)
    , ("forcedNetwork", jopt (.str ∘ (·.name)) m.forcedNetwork), ("initialTab", jopt .str m.initialTab)
    , ("requireDeviceAuthentication", .bool m.requireDeviceAuthentication), ("advancedMode", .bool m.advancedMode)
    , ("controlFile", jopt .str m.controlFile), ("peerCount", jopt (fun n => toJson n) m.peerCount)
    -- what a sync pass waits, in whole milliseconds (`chooseBackend`'s conversion)
    , ("syncIntervalMs", jopt (fun s => toJson (s * 1000).toUInt64.toNat) m.syncIntervalSeconds)
    , ("storageDirectoryName", .str m.storageDirectoryName), ("keychainService", .str m.keychainService)
    , ("networkMagic", jopt (fun p => .str (hex p.magic)) m.networkParams) ]

def modeOf (entropy : String) : IO E2E.Mode := do
  match E2E.resolve (fun k => [("WINNOW_E2E", "1"), ("WINNOW_E2E_ENTROPY", entropy)].lookup k) with
  | .active m => pure m
  | _ => bad "entropy"

def ops : Std.HashMap String (Json → IO Json) := Std.HashMap.ofList
  [ ("e2e.resolve", fun j => do
      let env := envOf j
      return ok <| match E2E.resolve (fun k => env.lookup k) with
        | .inactive => .str "inactive"
        | .missingPinnedEntropy => .str "missingPinnedEntropy"
        | .active m => describe m)
  , ("e2e.looksSecret", fun j => do return ok (.bool (E2E.looksSecret (← strJ j "value"))))
  , ("e2e.carriesSeed", fun j => do return ok (.bool ((← modeOf (← strJ j "entropy")).carriesThisRunsSeed (← strJ j "value"))))
  , ("e2e.fieldName", fun j => do return ok (.bool (E2E.refusesFieldName (← strJ j "key")))) ]

def answer (line : String) : IO Json := do
  match Json.parse line with
  | .error e => return errJ s!"bad-json: {e}"
  | .ok j =>
    match j.getObjValAs? String "op" with
    | .error _ => return errJ "bad-json: op"
    | .ok op =>
      match ops[op]? with
      | none => return errJ "unsupported"
      | some h =>
        try h j catch e =>
          let m := toString e
          return errJ (if m.startsWith "bad-request" then m else s!"bad-request: {m}")

partial def loop (stdin stdout : IO.FS.Stream) : IO Unit := do
  let line ← stdin.getLine
  if line.isEmpty then return
  stdout.putStrLn (← answer line.trimAscii.copy).compress
  stdout.flush
  loop stdin stdout

def main : IO Unit := do loop (← IO.getStdin) (← IO.getStdout)
