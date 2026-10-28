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

Winnow's cryptography is written in Lean and is not constant-time. The
secp256k1 code (`Lean/Secp`, used for ECDSA and BIP340 signing, Taproot tweaks
and BIP32 key derivation) computes with Lean's `Nat`, which is backed by GMP and
takes time that depends on the numbers, and its scalar multiplication branches on
each bit of the scalar. The AES code behind backup encryption
(`Lean/Winnow/Crypto/AES.lean`, `AESGCM.lean`) looks up tables by secret bytes.
All of it is checked by proofs, published test vectors and lockstep tests against
libsecp256k1 and CryptoKit, so its answers are right; only its timing can leak.

That is an acceptable risk for this app because of how it is used:

- Signing is rare and the user approves each payment on screen. Nothing outside
  the app can ask it to sign, so no one can collect the many timed signatures a
  timing attack needs.
- There is no remote oracle: no peer or server can make the app sign, derive a
  key or decrypt. The app does no secret-key work on what peers send it (it
  sends silent payments but does not scan for them).
- BIP340 nonces are derived from the key, the message and fresh auxiliary
  randomness for each signature, so even signing the same message again does not
  repeat a nonce.
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
