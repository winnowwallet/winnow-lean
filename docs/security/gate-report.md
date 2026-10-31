# Limited-mainnet gate report

This is an August 2026 audit record. References to Silent Payments and its tweak
index describe the implementation reviewed then; those features have since been
removed. Historical findings and their evidence are retained below.

**Decision: GO — recorded 2026-09-14 by the project owner.** Mainnet has been
the shipped default since v0.6.0 (2026-09-06) and the app has been on the App
Store since 2026-09-12; on 2026-09-14 the owner recorded the mainnet decision
as GO on that basis. Everything below this line is the August record that
recommended NO-GO, retained unchanged as history: it says what was evidenced
then and what a person still had to decide, and that person has now decided.

What the decision does not change. The independent human audit named
throughout this register as the strongest remaining confidence artifact is
still outstanding. The agent-driven
[independent review of 2026-09-14](independent-review-2026-09-14.md) — one
High, seven Medium, twenty-two Low, three informational, none Critical — is
tracked as issues #98–#130. Its [dated tracker](independent-review-2026-09-14.md#tracker)
records subsequent fixes and decisions; the observations concern the reviewed
revision. The GO is the owner’s decision, not a claim of a completed human audit.
For current automated release checks, use the [CI runbook](../../.github/internal/ci-release.md).

---

*The August 2026 record, as written:*

**Decision: NO-GO.** This report does not authorize a mainnet release, and it
is not an approval. It records what is now evidenced, what is not, and what a
person still has to decide.

| | |
|---|---|
| Reported at | `main`, `4fb8ec9` |
| Landed | the epic's three review waves merged; the remaining findings closed since, ending with the reorg rollback |
| Package tests | 492 in 82 suites |
| App tests | 116, 0 failures |
| Findings | 23 recorded, 23 fixed, **0 open** |
| Invariants | 12 total: 1 evidence complete, 11 partial, **all blocked release** |
| Last revised | 2026-08-23 |

## Why this is NO-GO

One reason now, where there were three.

**The evidence that needs hardware and external systems does not exist yet.**
A Bitcoin Core node for the differential corpus cross-check, independent
wallets for mixed-implementation PSBT fixtures,
a physical device for Keychain and screenshot behaviour, and sustained signet
runs. None of it can be produced by reading code, and none of it has been
produced.

The other two reasons have since been resolved, and are recorded here rather
than quietly dropped:

- **All findings are closed.** `SEC-016` — the wallet not rolling back after a
  reorg, the one Medium on the money path — was the last of the
  twenty-three to close. `SEC-005` and `SEC-017` were fixed earlier in the epic.
- **Independent review: dispositioned by the owner, 2026-08-23.** The epic
  required a reviewer that is not an agent working inside this project. The
  reviews were performed by a separate model (K3) reading the code directly,
  and it argued against its own earlier conclusions more than once — it
  withdrew a characterisation of the retry-counter clamp when shown the blast
  radius, and it found the defect that the ordering invariant in the rollback
  was violated by the code stating it. The project owner accepts that lane as
  satisfying the independence requirement.

  The limitation is recorded so the reader can weigh it: the reviewer was
  driven by the same agent that wrote the code, which chose what to submit and
  how to frame it. That shapes what a reviewer looks at. It is a materially
  stronger check than self-review and it is not the same thing as an
  uninvolved auditor — engaging one remains open follow-up work.

**Eleven of twelve invariants remain partial**, and the residue is not
incidental. What is missing needs things this pass could not reach: a Bitcoin
Core node for the differential corpus cross-check, independent wallets for
mixed-implementation PSBT fixtures (#58), a physical device for Keychain and
screenshot behaviour, and sustained signet runs. The cfcheckpt majority rule
is no longer among them: it is exercised on a 1,001-block fixture (`SEC-021`).

## What is now evidenced

Fourteen findings fixed, including four found and fixed during this pass on the
authorization path itself:

| | |
|---|---|
| SEC-007 | `SendPreview.authorizes` — the last gate before broadcast — verified fee, change and inputs but **never the payment outputs**. A build paying a different script, paying one satoshi, or omitting the recipient entirely was authorized. |
| SEC-018 | The same gate never inspected silent payments at all, and did not require the reviewed outputs to exhaust the actual ones. Fixed; the residual is that the app cannot bind a derived script to the reviewed `sp1…` code without the input keys. |
| SEC-019 | Signer independence was proved by sampling one derivation coordinate. Two expressions over one account key could differ there and collide at a later address, making a threshold-2 vault impossible to finalize. Fixed by pinning the accepted descriptor shape. |
| SEC-020 | A vault's Taproot internal key was never checked, so a tampered record could carry a real key and spend a k-of-n alone. Fixed. |
| SEC-008 | `send` and `bumpFee` are `@MainActor` but release the actor at every await, so a second entry could interleave. The only protection was a disabled button. |
| SEC-009 | `Vault.init` accepted a policy repeating a signer. `tr(musig(K,K))` presented as 2-of-2 while being spendable by whoever held K alone. |
| SEC-010 | The recursive-descent descriptor parser had no depth bound; ~1,000 levels of nesting terminated the process by signal, from a path read at startup. |

Plus SEC-013, which fixes open bug #81: peer, explorer and tweak-index settings
crossed a network switch, and manual peers are dialed first — so a signet node
left configured spent a mainnet pool's opening attempts on a peer that rejects
the handshake.

Full detail, with the exact commands and their results, is in
`findings.md` and `invariant-matrix.md`.

## On the strength of the evidence

Every claim here rests on a test that was **observed failing** before it was
accepted — against a deliberately mutated implementation, or against the
pre-fix code. That discipline is the reason to trust the numbers, and twice it
caught tests that would otherwise have been counted as evidence while checking
nothing:

- A fee-rate bound test asserted "some `CoinSelectionError`". Removing the
  bound still threw, as a *different* case, so the mutation killed nothing. The
  bound had no test defending it.
- A peer-disagreement test asserted "some `FilterSyncError`", and the mutation
  again killed nothing — which revealed that the cfcheckpt majority rule
  **never engages below height 1000**, and the defence actually exercised was
  the cfheaders cross-check. That gap is recorded rather than papered over.

A mutation that kills no test means the test is weak, not that the code is
safe. Both assertions were tightened; both now fail against their mutation.

## Two decisions that were yours — both now made

Neither is a defect. Both are judgement calls that were made explicit rather
than left implicit, and either could reasonably have been decided the other
way. Both were accepted by the owner on 2026-08-23, with the reasoning and the
residual exposure recorded here rather than resolved by silence.

**The single-peer eclipse — decided by the owner, 2026-08-23: accept.** With
one peer there is nobody to compare against, so a self-consistent lying
filter-commitment chain is accepted and the user has no indication of it.
Failing closed would strand anyone whose network reaches one peer, and that
was judged the worse outcome: a wallet that refuses to sync is a wallet nobody
can use, and the eclipse it protects against requires an attacker already
positioned to be that one peer.

The mitigation is therefore *peer diversity rather than refusal* — reaching
more independent peers cheaply, so the one-peer case is rare instead of
tolerated. That work — source-diverse peer slots with cross-source
agreement, and addrman-style scoring with /16 diversity — is tracked, and
this decision makes it the response to the risk rather than an
alternative to it. Current behaviour
stays pinned by test as *documented*, and is now also *endorsed, with a named
mitigation*.

**Clipboard reach — decided by the owner, 2026-08-23: accept.** Descriptors and
PSBTs may still cross to another device via Universal Clipboard. A descriptor
carries xpubs, so whoever holds it can derive every address the vault will ever
use.

Interchange is kept because pasting a watch-only descriptor into Bitcoin Core is
the workflow those buttons exist for, and the alternative costs the user a file
transfer for the one operation that most wants to be easy. The mitigation
already in place is expiry: interchange material does not sit on the clipboard
indefinitely. Forcing local-only remains a one-line change to
`ClipboardPolicy.interchange` if the workflow cost is ever judged worth paying.

What the reader should weigh: this accepts that a descriptor can reach any
device signed into the same Apple account, which is a real exposure and not a
theoretical one. It is accepted because the material is watch-only — it reveals
every address, and it spends nothing.

## What a GO would require

1. ~~An **independent** reviewer — not an agent in this project — on one exact
   integration commit, with findings remediated or dispositioned.~~
   **Dispositioned by the owner, 2026-08-23**, with the limitation recorded
   above.
2. ~~SEC-016 resolved: a wallet rollback consuming `lastReorg`, or an explicit,
   written acceptance of the risk.~~ **Done** — fixed on `main`.
3. ~~SEC-005 and SEC-017 closed, or dispositioned with an owner and a date.~~
   **Done** — both fixed.
4. **Done — closed 2026-08-28.** Producing this condition's evidence found
   five defects that no amount of reading would have surfaced (`SEC-024`
   through `SEC-028`), and its last three legs closed on the phone itself:
   locked-Keychain enforcement and the hidden app-switcher card on
   2026-08-27, and the soak reading the owner accepted as sufficient on
   2026-08-28 — a day resident at 68.4 MB, an order of magnitude under the
   mid-sync launch peak. The per-leg detail below stands as the record.

   - *Node-backed differential runs:* the fixture had been **unrunnable**, its
     BIP325 challenge key lost with a workstation. It is rebuildable from the
     repository now (`scripts/signet-fixture`), and rebuilding it from genesis
     exposed three defects invisible on an established chain. The corpus is a
     seeded sweep cross-checked field-by-field against Core rather than three
     hand-written transactions.
   - *Mixed-wallet PSBT fixtures:* **done for script-path.** Bitcoin Core holds
     one key of three in a `tr(NUMS, sortedmulti_a(2,…))` vault and co-signs a
     spend that confirms — #58's acceptance bar. The envelope conversion every
     Core exchange forces is proven lossless. **MuSig2/BIP390 reaches round 1 and stops:** Core
     contributes a BIP373 nonce, but keys it by the tweaked output key
     where we key by the root aggregate, so neither side can consume the
     other's. Named, pinned by test, and not inferred from the
     script-path result.
   - *Device Keychain and screenshot checks:* the simulator half is done and
     the claims are observations now rather than readings. **The Keychain
     half of the hardware evidence now exists.** On 2026-08-27, on the
     owner's passcoded phone running the v0.5.3 instrument, the in-app
     check recorded the wallet key readable while unlocked (the control),
     then refused while locked — samples
     `5s 0 · 5s 0 · 10s 0 · 15s −25308 (locked) · 20s −25308 (locked)`,
     where −25308 is `errSecInteractionNotAllowed` and the early zeros are
     reads that beat the lock landing: the transition itself, captured.
     The reading is
     [`evidence-device-lock-2026-08-27.png`](evidence-device-lock-2026-08-27.png).
     The app-switcher half followed the same day: the switcher shows
     Winnow's card with the system's hidden treatment — an eye-slash and
     "Winnow is hidden", no balance, no addresses, the snapshot withheld
     rather than staled —
     [`evidence-app-switcher-2026-08-27.png`](evidence-app-switcher-2026-08-27.png),
     cropped to the wallet's own card. Still outstanding from the phone:
     a soak reading long enough to speak about days.
   - *Sustained signet:* two runs, the second 90 minutes with 88 at chain tip,
     timeseries committed. It found `SEC-024` within the first hour. A third
     run starting at tip holds resident size between 13 MB and 36 MB. That
     is 110 minutes of at-tip observation, which supports a claim about
     hours and not about days — and days will need the `node-e2e` runner,
     because two multi-hour attempts were killed by the environment here.
     That runner exists now. On 2026-08-25 the dedicated fixture VM ran
     the full node-backed battery to green — package tests, differential
     suite, and the complete UI e2e
     ([run 32866916504](https://github.com/winnowwallet/winnow/actions/runs/32866916504)). It was
     the first run anywhere to execute the UI leg: every earlier green
     had skipped those steps for want of Xcode on the VM, and the first
     real execution surfaced three defects in the tests themselves that
     a skipped step had been reporting as passing — a spend staged
     against a coin no chain contained, an assertion on a label the UI
     no longer renders, and backgrounding invariants that raced the
     scene phase instead of exercising it. The days-long observation now
     has a machine to run on; it has not run yet. The phone, meanwhile,
     has started answering the same question at first hand: on 2026-08-28
     the v0.5.3 instrument read **1d 1h resident, 68.4 MB** —
     [`evidence-soak-day1-2026-08-28.png`](evidence-soak-day1-2026-08-28.png).
     The two ~580 MB readings that raised the memory question were both
     taken a minute after launch, mid-sync; a day of residence settles an
     order of magnitude lower, so the launch figure was the sync burst,
     not the resting footprint. On 2026-08-28 the owner accepted this
     reading as the soak evidence — the two macOS runs bound the hours,
     the phone bound a day at rest, and the depth of the question does not
     grow with more calendar.

   What is left is genuinely the hardware: on-device Keychain enforcement,
   screenshot and lifecycle behaviour, and runs long enough to speak about days.
   Crash-during-write is deliberately **not** among them — every store writes
   atomically or through the fsync-ordered append path, and the consequences of
   a damaged file are already evidenced by the storage-corruption, append,
   quarantine and rollback-marker suites. A racy process-kill test would add
   noise, not evidence.
5. ~~The two judgement calls decided, or recorded as open.~~ **Done** — the
   single-peer eclipse and the clipboard reach were both dispositioned by the
   owner on 2026-08-23, and both are written up above with their reasoning.

**Every numbered condition is now closed.** The last of them needed a
person and hardware, and that is what closed it. What stands between this
report and a different verdict is no longer evidence production: it is the
independent audit the owner has chosen to pursue before mainnet — named
throughout this register as the strongest remaining confidence artifact —
and the owner's decision itself.

## Human decision required

This report recommends **NO-GO** and does not make the decision. The mainnet
release decision belongs to the project owner, on evidence, not to the process
that produced this document.
