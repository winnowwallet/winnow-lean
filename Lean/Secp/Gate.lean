import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! # The axiom gate commands

* `#assert_axioms <name>` fails the build unless the theorem depends on nothing beyond the three
  standard axioms (`propext`, `Quot.sound`, `Classical.choice`). A `sorry` elaborates to the axiom
  `sorryAx`, so it cannot hide. It logs `<name> OK, axioms: [...]`.
* `#assert_all_axioms <ns>…` applies the same check to every theorem whose root namespace is one of
  the given ones, auto-generated lemmas included, and logs one line
  `all theorems OK: <k> checked under <ns>`.

The assumption that `P` is prime is a hypothesis (`[Spec.FieldP]`), not an axiom, so the gate
does not let it through: a theorem that needs it says so in its statement. -/

namespace Secp.Gate
open Lean

def allowedAxioms : Array Name := #[``propext, ``Quot.sound, ``Classical.choice]

end Secp.Gate

open Lean Elab Command in
elab "#assert_axioms " id:ident : command => do
  let n ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
  let axs ← liftCoreM <| collectAxioms n
  for a in axs do
    unless Secp.Gate.allowedAxioms.contains a do throwError "{n} depends on disallowed axiom {a}"
  logInfo m!"{n} OK, axioms: {axs.toList}"

open Lean Elab Command in
elab "#assert_all_axioms" nss:ident+ : command => do
  let roots : Array Name := nss.map (·.getId)
  let env ← getEnv
  let thms : Array Name := env.constants.fold (init := #[]) fun acc n ci =>
    match ci with
    | .thmInfo _ => if roots.contains (privateToUserName n).getRoot then acc.push n else acc
    | _ => acc
  let thms := thms.qsort Name.lt
  let mut offenders : Array String := #[]
  for n in thms do
    let axs ← liftCoreM <| collectAxioms n
    for a in axs do
      unless Secp.Gate.allowedAxioms.contains a do offenders := offenders.push s!"{n} depends on {a}"
  let where_ := ", ".intercalate (roots.toList.map toString)
  unless offenders.isEmpty do
    throwError "disallowed axiom in {offenders.size} theorem(s) under {where_}: {offenders.toList}"
  logInfo m!"all theorems OK: {thms.size} checked under {where_}"
