[Back to main README](../../README.md)

# Security claims and their evidence

The findings register, invariant matrix, gate reports, audit manifest, and device
captures explain which wallet properties have been examined and what remains open.
They keep past decisions tied to observations rather than undocumented confidence.
These reports are historical snapshots, not a live issue backlog or current
release checklist. Older “open” or “blocked release” rows must be read with
the dated follow-ups, not treated as new requirements.

## The Lean app (0.9.x)

Note of 2026-11-17. Winnow 0.9.x is the wallet rewritten in Lean 4. The Swift
app these reports were written about ended with 0.8.13 and stays in
[winnowwallet/winnow](https://github.com/winnowwallet/winnow). This repository
holds no Swift source, so the `Sources/…`, `Tests/…`, `AppTests/…`, `UITests/…`
and `Tools/…` paths, the Swift suite names and the `swift test` and `xcodebuild`
commands in the reports name things that are not in this tree.

What this directory holds now:

- **Dated records of the Swift app's audits**: the audit manifest, the gate
  report, the invariant matrix, the independent review of 2026-09-14, the review
  of winnow#87, the device captures and the files under `evidence/`. `SEC-001`
  to `SEC-038`, every `IR-` item, and every commit hash, branch name and
  issue or pull-request number dated before 2026-10-31 refer to
  winnowwallet/winnow (`census#N` to its census repository). A statement in them is about the Swift code at the
  revision it names. The device observations (the Keychain under lock, the app
  switcher, the day of resident memory, the Ledger Nano X on mainnet) were made
  with the Swift app.
- **The [findings register](findings.md)**, which is still added to. `SEC-039`
  onward are findings in this repository, and a bare `#N` in those rows is a
  winnow-lean number.

Where the Lean app's checks and claims are:

- [The testing guide](../testing.md): what CI runs today (the Lean test
  executables, five suites against a regtest Bitcoin Core, the eleven UI journeys,
  the fuzzer) and what they do not cover.
- [SECURITY.md](../../SECURITY.md): how to report, and what is and is not
  claimed about the curve code (`Lean/SecpCt`) and timing.
- [PORT.md](../../PORT.md): how each ported part was verified and where the
  port departs from the Swift app.
- [The suite map](test-suite-map.md): where a Swift suite named in a record is
  carried in the Lean tree, when it is.

No audit target has been frozen for the Lean code (see the 2026-11-17 note in
the [audit manifest](audit-manifest.md)). Notes dated 2026-11-17 in the
[invariant matrix](invariant-matrix.md) and the
[independent review](independent-review-2026-09-14.md) say where a recorded
disposition is known not to describe the Lean app.

## The records

[The audit manifest](audit-manifest.md) identifies evidence,
while [the findings register](findings.md) records results and
the gaps known at each date. [The testing guide](../testing.md) explains what the
Lean app's suites cover and their limits.
Raw [soak observations](evidence/README.md) remain separate from
the interpretation written in the reports.

[The independent review of 2026-09-14](independent-review-2026-09-14.md) is
the first pass by a reviewer that wrote none of the code — an agent engaged by
the owner, not yet the uninvolved human auditor the gate report names as open.
Its findings are tracked as GitHub issues winnow#98–winnow#130 and fixed on one branch
(winnow#137, with the census side in census#15); the review's tracker table
records what was fixed, accepted, or left to the owner. [The gate report](gate-report.md) records the owner's mainnet
decision of 2026-09-14 above the August record it revises.

Changes made to the Swift app after those reports, which the Lean app keeps:
the embedded Tor client is removed, and since winnow#181 peer connections can
instead go through the user's own Tor and I2P SOCKS gateways
([peer gateways](../peer-gateways.md); `Lean/Winnow/IO/Gateways.lean`). Since
October 13 each build bundles the census list current when it was built
(`scripts/import-census`) and the app downloads none. The Swift app's CI (from
September 18: hosted Apple silicon, one iPhone journey and focused lower-level
suites) ended with that app; for today's checks see
[the testing guide](../testing.md). The
[CI runbook](../../.github/internal/ci-release.md) covers the workflow and the
release steps, and keeps the Swift app's CI as history.
[Issue #164](https://github.com/winnowwallet/winnow/issues/164) is closed: its
selected signing/tooling items were completed, and the owner declined the
remaining proposals. Historical follow-ups are not a commitment to resume them.

Preserve tested revisions and provenance when
adding newer observations; do not silently turn an old result into current status.
Tests, logs, and physical-device observations support particular claims, not a
blanket assertion that the wallet has completed independent review.
