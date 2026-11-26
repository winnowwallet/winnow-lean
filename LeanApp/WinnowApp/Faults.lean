import Lean.Data.Json
import Std.Data.HashMap

/-! # Failures a journey asks for (test mode)

In test mode (a Debug build launched with `WINNOW_E2E=1`) the runner's control file (`WINNOW_E2E_CONTROL_FILE`,
which the journeys' Paste buttons also read) may name failures:

    {"faults": [{"id": "…", "point": "store.write", "times": 1, "message": "…"}]}

`Faults.check point` throws the first one left for `point`, or for a point that begins it (a fault for
`store.write` is every store's; one for `store.write.multisig-accounts.json` that file's alone): each `id` `times`
times (once when not given), with `message` or "A failure the journey asked for (<point>)." Outside test mode no
control file is named and `check` returns at once: nothing here acts in a Release build.

The points, each where the operation would fail on a phone, before it changes anything:

* `store.write.<file>`: a records store's write (`RecordsSeal.writeAtomically`: people, labels, multisig
  accounts, signers, the device's records);
* `broadcast`: a payment's broadcast, the wallet's or a multisig account's, before any peer is given it;
* `feeRate`: working out a fee rate;
* `receive.fresh`: a fresh receive address;
* `export`: writing the backup file;
* `peers.reset`: resetting and shuffling the peers;
* `payment.details`: loading a payment's details. -/

namespace WinnowApp.Faults
open Lean

initialize controlFile : IO.Ref (Option System.FilePath) ← IO.mkRef none
/-- How many times each fault (by `id`) has been taken. -/
initialize taken : IO.Ref (Std.HashMap String Nat) ← IO.mkRef {}

/-- The control file of a test-mode launch; none outside test mode. -/
def arm (path : Option String) : IO Unit := controlFile.set (path.map System.FilePath.mk)

/-- Whether `fault` (a point the journey named) is for `point`. -/
def covers (fault point : String) : Bool := point == fault || point.startsWith (fault ++ ".")

/-- Throws the failure the journey asked for at `point`, if one is left there. -/
def check (point : String) : IO Unit := do
  let some path ← controlFile.get | return
  let text ← try IO.FS.readFile path catch _ => return
  let .ok j := Json.parse text | return
  for f in ((j.getObjValAs? (Array Json) "faults").toOption.getD #[]) do
    let some id := (f.getObjValAs? String "id").toOption | continue
    let some fault := (f.getObjValAs? String "point").toOption | continue
    unless covers fault point do continue
    let times := (f.getObjValAs? Nat "times").toOption.getD 1
    let mine ← taken.modifyGet fun m =>
      let n := m.getD id 0
      if n < times then (true, m.insert id (n + 1)) else (false, m)
    if mine then
      throw (IO.userError ((f.getObjValAs? String "message").toOption.getD s!"A failure the journey asked for ({point})."))

end WinnowApp.Faults
