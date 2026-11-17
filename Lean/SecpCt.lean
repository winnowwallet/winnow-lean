import SecpCt.Gate

/-! # SecpCt: signing that does the same work whatever the key is

Field, scalars, points, BIP 340 and ECDSA on machine words, with no branch on a secret and no table looked up
by one (`SecpCt/Word.lean` says how). `Secp` is the reference: what `SecpCt` returns is proved to be what
`Secp` returns (`SecpCt/Gate.lean` lists the theorems), so `Secp`'s own proofs about the curve as specified
carry over to it.

This root imports the gate, so building the library checks every proof. Code that signs imports
`SecpCt.Schnorr` or `SecpCt.Ecdsa`, and none of the proofs. -/
