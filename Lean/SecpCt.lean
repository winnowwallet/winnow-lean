import SecpCt.Gate

/-! # SecpCt: secp256k1 as it runs

The only implementation of the curve here: field, scalars, points, reading keys, tweaks, BIP 340 and ECDSA,
on machine words, with no branch on a secret and no table looked up by one (`SecpCt/Word.lean` says how).
What it is proved against is `Secp`: the curve as specified (`Secp/Curve/Spec.lean`) and signing as BIP 340
and ECDSA give it (`Secp/Signing.lean`). `SecpCt/Gate.lean` lists the theorems.

This root imports the gate, so building the library checks every proof. Code that runs imports
`SecpCt.Keys`, `SecpCt.Schnorr` or `SecpCt.Ecdsa`, and none of the proofs. -/
