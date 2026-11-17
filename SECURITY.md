# Bug and security reports

Report bugs, including security vulnerabilities, in a
[public GitHub issue](https://github.com/winnowwallet/winnow/issues/new).
Include the affected version, steps to reproduce, expected and actual behavior,
and relevant logs or a minimal example.

Do not include recovery words, private keys, credentials, or personal wallet data.

Reports and fixes are tracked publicly. The
[findings register](docs/security/findings.md) records security findings and
their disposition. What the wallet claims, and what it does not, is in
[docs/security](docs/security/README.md).

## Timing side channels

Winnow's cryptography is written in Lean and, but for one part described below,
is not constant-time. The
secp256k1 code (`Lean/Secp`, used for BIP340 signing, Taproot tweaks,
BIP32 key derivation and checking ECDSA signatures) computes with Lean's `Nat`, which is backed by GMP and
takes time that depends on the numbers, and its scalar multiplication picks a
precomputed multiple for each 4-bit window of the scalar, so it branches on and
indexes by the scalar's bits. The AES code behind backup encryption
(`Lean/Winnow/Crypto/AES.lean`, `AESGCM.lean`) looks up tables by secret bytes.
All of it is checked by proofs, published test vectors and lockstep tests against
libsecp256k1 and CryptoKit, so its answers are right; only its timing can leak.

One part is checked by tests rather than proofs: the scalar multiplication,
lift_x and point addition the app runs (`Lean/Secp/Fast.lean`, four unboxed
limbs and window tables). The proofs are about the slower definitions they stand
in for (`@[implemented_by]` in `Lean/Secp/Keys.lean` and
`Lean/Winnow/Keys/Secp256k1.lean`); `crypto-test` compares the two on edge and
random inputs, and BIP340's vectors and every other test run through the fast
path.

One part is written to do the same work whatever the key is: `Lean/SecpCt`, the
field, scalars, points, BIP340 and ECDSA on machine words, with no branch on a
secret and no table looked up by one. The app signs with it in one place, the
ECDSA signature a SegWit v0 multisig account takes
(`Lean/Winnow/Wallet/SegwitMultisigAccount.lean`). It is proved to return what
`Lean/Secp` returns (`Lean/SecpCt/Gate.lean`: 493 theorems, no axiom beyond Lean's
three, assuming only that P is prime), and `secpct-test` and `fuzz` hold the
compiled code to the same. What the proofs and tests say is that its answers are
right. That its timing does not depend on the key is a property of compiled code,
and has been checked only for another build of this source (Linux on x86-64,
under Valgrind with the key marked as unknown), not for the builds this app
ships (arm64, with Lean's own runtime, whose byte arrays and reference counts it
uses). Nothing here relies on it: the key that signs is still derived with
`Lean/Secp` (BIP32), and the list below is what the app relies on for every
signature, this one included.

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
  (`Lean/Secp/Ecdsa.lean`), not by RFC 6979, so a key used for both kinds of
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
