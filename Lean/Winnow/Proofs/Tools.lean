import Lean.Elab.Term

/-! # What the proofs about the wallet share

`body%`, and the few facts about `Except` that every proof about a function in the `Except` monad rewrites
with. Nothing here is about Bitcoin. -/

namespace Winnow.Proofs

open Lean Elab Term Meta in
/-- `body% f [c₁, …] [x₁, …]`: the definition of `f` with each constant `cᵢ` replaced by the term `xᵢ`; with
no constants, `f`'s definition itself.

A proof tool, in no statement that is kept. The kernel has no notion of "do not unfold": when a proof step
leaves it comparing two `match`es on `pointOfSecret d`, it evaluates `pointOfSecret d`, a 256-step ladder on a
symbolic number, and does not come back. So a function that calls the curve is reasoned about in two steps:
a lemma about `body% f [pointOfSecret, …] [pos, …]`, where the callees are variables and any simplification is
cheap to check, and then `rw [f_def]; exact lemma …`, which the kernel checks by seeing that the two terms are
the same term. -/
elab "body% " f:ident "[" cs:ident,* "]" "[" xs:term,* "]" : term => do
  let fn ← realizeGlobalConstNoOverload f
  let info ← getConstInfo fn
  let cns ← cs.getElems.mapM (realizeGlobalConstNoOverload ·)
  let xes ← xs.getElems.mapM (elabTerm · none)
  return info.value!.replace fun e => match e with
    | .const n _ => (cns.idxOf? n).map (xes[·]!)
    | _ => none

theorem throw_eq {ε α : Type} (e : ε) : (throw e : Except ε α) = .error e := rfl
theorem pure_eq {ε α : Type} (a : α) : (pure a : Except ε α) = .ok a := rfl
theorem ok_bind {ε α β : Type} (a : α) (f : α → Except ε β) : (Except.ok a >>= f) = f a := rfl
theorem error_bind {ε α β : Type} (e : ε) (f : α → Except ε β) :
    ((Except.error e : Except ε α) >>= f) = .error e := rfl

end Winnow.Proofs
