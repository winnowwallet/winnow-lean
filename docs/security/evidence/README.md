[Back to main README](../../../README.md)

# Retained network-soak observations

The two JSONL files retain public-signet observations from 2026-08-24, including
a scan and a run already at the tip. They let a reviewer inspect the measurements
behind historical network findings rather than relying only on a summary.

[The audit manifest](../audit-manifest.md) and
[findings register](../findings.md) provide context.
Preserve their original contents and interpretation.

Note of 2026-11-17: every record in this directory was made with the Swift
app (winnowwallet/winnow). The soak driver and its debugging runbook
(`Tools/Debug`), and the scripts the gateway record names, are not in this
repository, and this tree has no soak tool. For a new observation, keep the
revision, command, network, time interval and resulting data together, and
add a new dated record instead of overwriting these files.
They are historical evidence, not a live health check or an automated test fixture.

[Live gateways, 2026-09-29](live-gateways-2026-09-29.md) records a manual run of
the Swift app's `scripts/check-live-gateways` and independent SOCKS, mirror and handshake
checks through the project's Tor and I2P gateways.

[Ledger on mainnet, 2026-10-26](ledger-mainnet-2026-10-26.md) records the
first spend a physical Ledger Nano X co-signed from a Winnow 2-of-2 account,
with the transaction's witness. It was made with the Swift app's build 0.8.14.
