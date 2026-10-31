# Retired mainnet launch-recording plan

The original August launch plan is retired. Current automated integration and
website media use the [single private-signet journey](../../UITests/README.md),
with automatically mined confirmations and disposable test keys. No real-money
recording or physical-device measurement is required by that workflow.

The old plan assumed one particular development node, promised unconfirmed
payment timings, and overstated recovery from words alone. Those instructions
must not be reused. Winnow recovery needs both recovery words and the wallet
backup file. See the
[current backup guide](../../docs/import.html).

[CI and release operations](ci-release.md) is the current runbook. The
[original plan at its last pre-retirement revision](https://github.com/winnowwallet/winnow/blob/9cca3fc579b38a4e24868416e0b8cd1b8241f1e2/.github/internal/mainnet-test-plan.md)
remains in Git history for context, not as an instruction to spend funds or a
claim about the current app.
