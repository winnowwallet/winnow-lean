[Back to main README](../../README.md)

# Security claims and their evidence

The findings register, invariant matrix, gate reports, audit manifest, and device
captures explain which wallet properties have been examined and what remains open.
They keep past decisions tied to observations rather than undocumented confidence.
These reports are historical snapshots, not a live issue backlog or current
release checklist. Older “open” or “blocked release” rows must be read with
the dated follow-ups, not treated as new requirements.

[The audit manifest](audit-manifest.md) identifies evidence,
while [the findings register](findings.md) records results and
the gaps known at each date. [The testing policy](../testing.md) explains suite limits.
Raw [soak observations](evidence/README.md) remain separate from
the interpretation written in the reports.

[The independent review of 2026-09-14](independent-review-2026-09-14.md) is
the first pass by a reviewer that wrote none of the code — an agent engaged by
the owner, not yet the uninvolved human auditor the gate report names as open.
Its findings are tracked as GitHub issues #98–#130 and fixed on one branch
(winnow#137, with the census side in census#15); the review's tracker table
records what was fixed, accepted, or left to the owner. [The gate report](gate-report.md) records the owner's mainnet
decision of 2026-09-14 above the August record it revises.

As of September 18, current checks use hosted Apple silicon, one iPhone
journey and focused lower-level suites; Intel, broad UI and differential jobs
are retired. The embedded Tor client is removed; since #181 peer connections can instead go through the user's own Tor and I2P SOCKS gateways ([peer gateways](../peer-gateways.md)). Since October 13 each build
bundles the census list current when it was built and the app downloads none. See the
[CI runbook](../../.github/internal/ci-release.md), [peer guide](../../Sources/WalletCore/Network/Peers/README.md)
and [suite map](test-suite-map.md).
[Issue #164](https://github.com/winnowwallet/winnow/issues/164) is closed: its
selected signing/tooling items were completed, and the owner declined the
remaining proposals. Historical follow-ups are not a commitment to resume them.

Preserve tested revisions and provenance when
adding newer observations; do not silently turn an old result into current status.
Tests, logs, and physical-device observations support particular claims, not a
blanket assertion that the wallet has completed independent review.
