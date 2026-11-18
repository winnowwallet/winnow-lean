# Bug and security reports

Report bugs, including security vulnerabilities, in a
[public GitHub issue](https://github.com/winnowwallet/winnow-lean/issues/new).
Include the affected version, steps to reproduce, expected and actual behavior,
and relevant logs or a minimal example.

Do not include recovery words, private keys, credentials, or personal wallet data.

Reports and fixes are tracked publicly. The
[findings register](docs/security/findings.md) records security findings and
their disposition; its entries from SEC-039 on are the Lean app's. The other
files in [docs/security](docs/security/README.md) are dated records of the Swift
app's audits. What the Lean app is checked by is in
[docs/testing.md](docs/testing.md) and [PORT.md](PORT.md).

## Timing side channels

Winnow's cryptography is written in Lean.

Its secp256k1 code is one implementation, `Lean/SecpCt`: the field, scalars,
points, reading keys, tweaks, BIP340 and ECDSA, on machine words. Everything the
app does on the curve runs on it: signing, deriving keys (BIP32), Taproot
tweaks, sending silent payments and checking signatures. It is written so that
what is done with a secret is the same work whatever the secret is. The
multiplication of a key or a nonce, the sums and negations of keys and the
arithmetic of a signature have no branch on a secret and no table looked up by
one. What is public (the tweak of a public derivation, a signature being
checked) is handled plainly. The rest of the wallet reaches it through
`Lean/Winnow/Keys/Secp256k1.lean`, where a secret key is a type that is never a
`Nat` and cannot be printed or compared.

Each operation is proved against the curve as specified
(`Lean/SecpCt/Gate.lean`: 605 theorems, no axiom beyond Lean's three, assuming
only that P is prime). The proofs are about the source. The compiled code is
held to answers computed without it (`Lean/Vectors/secp-known-answers.json`, by
`scripts/secp-vectors`; the vectors of BIP340, BIP32, BIP341 and BIP352;
signatures OpenSSL made) and to Bitcoin Core on regtest. Nothing that ships is a
second implementation to compare with. A signature is still verified before it
leaves, by code that shares the field and point arithmetic with the signing it
checks; what that check accepting means is itself proved (`verify_sound`,
`Ecdsa.verify_sound`).

What the proofs and tests say is that the answers are right. That the timing
does not depend on a key is a property of compiled code, and it has been checked
only for another build of this source (Linux on x86-64, under Valgrind with the
key marked as unknown), not for the builds this app ships (arm64, with Lean's
own runtime, whose byte arrays and reference counts the code uses). So the app
does not rely on it, and the list below is what it relies on for every
signature.

The AES code behind backup encryption (`Lean/Winnow/Crypto/AES.lean`,
`AESGCM.lean`) is not constant-time: it looks up tables by secret bytes. It is
checked by published test vectors and against CryptoKit, so its answers are
right; only its timing can leak.

That is an acceptable risk for this app because of how it is used:

- Signing is rare and the user approves each payment on screen. Nothing outside
  the app can ask it to sign, so no one can collect the many timed signatures a
  timing attack needs.
- There is no remote oracle: no peer or server can make the app sign, derive a
  key or decrypt. The app does no secret-key work on what peers send it (it
  sends silent payments but does not scan for them).
- BIP340 nonces are derived from the key, the message and fresh auxiliary
  randomness for each signature, so even signing the same message again does not
  repeat a nonce. ECDSA nonces are made the same way under tags of their own
  (`Lean/Secp/Signing.lean`), not by RFC 6979, so a key used for both kinds of
  signature never has one nonce in both.
- The app runs sandboxed on the user's own device (iOS's app sandbox; the App
  Sandbox on the Mac). Another app cannot run code in its process, and code that
  can measure its cache timing closely enough is already past the sandbox.
- With a Ledger, the Ledger signs on the device; Winnow's own key is only one of
  the multisig signers.
- The backup key is used rarely: when a backup is written or restored.

Do not reuse this code where those conditions do not hold: in servers, signing
services, shared or multi-tenant hosts, or anything that signs, derives keys,
encrypts or decrypts on someone else's request. Use a constant-time library
such as libsecp256k1 or the platform's hardware AES there.
