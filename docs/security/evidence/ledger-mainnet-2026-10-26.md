[Back to evidence README](README.md)

# Ledger Nano X co-signing on mainnet, 2026-10-26

The first spend a physical Ledger co-signed from a Winnow multisig account.
The owner ran it by hand on mainnet with internal TestFlight build 0.8.14
(106), cut from `d8b95e3` on the `ledger-on-main` branch (#255). No test
drives a Ledger: `LedgerTests` and the device simulator show that the phone's
client is consistent with Ledger's published vectors, not that a device
agrees. This record is the evidence that one did.

- **Revision:** `d8b95e3` (#255), build 0.8.14 (106) in the internal
  TestFlight group.
- **Device:** a Ledger Nano X over Bluetooth, firmware and Bitcoin app
  updated the same day (versions not recorded).
- **Account:** a 2-of-2 with no recovery leaf,
  `tr(<NUMS xpub>/<0;1>/*, sortedmulti_a(2, [6824f543/86'/0'/0']…/<0;1>/*, [5992698d/87'/0'/0']…/<0;1>/*))`:
  the phone's key and the Ledger's, built with "Pair a Ledger" in Advanced
  mode and approved on the device, which gave the record its registration.
- **Funding:** 100,000 sats to the account's first address,
  `bc1p43whj6u5hgavmhjgcgk7gckv2e42sq4ry4p9ewvs3jnu0nmp6h0sa04z3w`, in
  [`e87664a2…`](https://mempool.space/tx/e87664a20b6fd66b073d42572338c08be9608a216d20139483769abff81d4f96)
  output 12, block 973269.
- **Spend:**
  [`6d2b391e…`](https://mempool.space/tx/6d2b391e7bdabcb69a133e49ae40ee54f956be8057edc7974742ad3a0d85c589),
  block 973281, 2026-10-26 19:31 UTC. The PSBT was created, signed by the
  phone and by the Ledger, finalized and broadcast in the app's "New or
  pasted PSBT" screen, the only spend path in this build.

## The witness

One input, four items:

| Item | Bytes | What it is |
|---|---|---|
| 0 | 64 | BIP340 signature, `SIGHASH_DEFAULT` |
| 1 | 64 | BIP340 signature, `SIGHASH_DEFAULT` |
| 2 | 70 | `<key> OP_CHECKSIG <key> OP_CHECKSIGADD OP_2 OP_NUMEQUAL`: the `sortedmulti_a(2, …)` leaf, keys in sorted order |
| 3 | 33 | the control block: `c1` (leaf version `c0`, output parity 1) and the 32-byte NUMS internal key; no Merkle path, so the tree has this one leaf |

Version 2, locktime 973280 (the tip when the PSBT was built), sequence
`0xfffffffd`, 196.5 vB, 985 sats in fees. Outputs: 12,323 sats to a
destination outside the account and 86,692 sats of change to the account's
first change address (`/1/0`), which the app then showed as its coin.

## What it shows

- The Ledger registered the policy Winnow built (the NUMS xpub as the
  internal key, both signer keys on `/<0;1>/*`) and signed the leaf the phone
  asked it to sign. A 2-of-2 script-path spend cannot complete without a
  signature under the Ledger's key, and the network accepted it.
- Both signatures verified on the phone before it kept them (SEC-036); the
  finalized witness is what the chain checked.
- Not shown here: a 2-of-3, a recovery leaf, declining on the device, and
  signet. Those remain the manual checks in
  [docs/testflight-what-to-test.txt](../../testflight-what-to-test.txt).

The addresses and transactions above are public. No recovery words, keys or
backup files were involved in making this record.
