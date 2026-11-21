import Winnow.Proofs.Gate

/-! # `WinnowProofs`: Build-time proof target for Winnow

Part of `defaultTargets` in `Lean/lakefile.toml` so `lake build` verifies every theorem and checks the
axiom gate (`Winnow/Proofs/Gate.lean`), while runtime libraries (`WinnowCore`, `Winnow`, `WinnowApp`)
never import it. -/
