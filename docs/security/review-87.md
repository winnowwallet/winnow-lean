# Review of loperanger7’s Winnow patches

> Historical integration report for the revisions named below. Tor, the
> differential suite, Intel CI, and the broad UI suite described here were
> subsequently retired. See the [current testing policy](../testing.md) and
> [test-suite map](test-suite-map.md); the measurements below remain unchanged.

Reviewed and merged 2026-09-14 in [PR #87](https://github.com/winnowwallet/winnow/pull/87). The inventory covers all ten PRs authored by loperanger7 in `winnowwallet/winnow`; none were found in `winnowwallet/census`. Several PR branches included unrelated shared history. Integration preserves the individual authored commits instead of importing their entire branch diffs.

| Patch | Disposition | Implementation and evidence |
| --- | --- | --- |
| [#75](https://github.com/winnowwallet/winnow/pull/75) | Already in #87; absent from the September 14 baseline | BIP39 NFKD for both seed inputs. Japanese and ligature vectors, strict separator rejection, and an added compatibility-space validation/seed agreement test. |
| [#76](https://github.com/winnowwallet/winnow/pull/76) | Ported | Explicit file protection on wallet creation/save/import, header full saves, and peer persistence. Tests mark the containing directory with a different class and check creation, replacement, and append. The suite also runs in the app test target; platforms that do not record protection classes report a named skip. |
| [#77](https://github.com/winnowwallet/winnow/pull/77) | Ported | One master-key load per signing operation, verified signatures for every input, and a 100,000-vbyte standardness limit. Selection checks estimated size; sends, fee bumps, and finalized vault spends check actual size. This is default relay policy, not a consensus rule. |
| [#78](https://github.com/winnowwallet/winnow/pull/78) | Existing behavior retained; missing regressions ported | Non-witness transaction bytes survive commit, confirmation, replacement, and reopen. Legacy history without raw bytes remains readable. |
| [#79](https://github.com/winnowwallet/winnow/pull/79) | Ported and completed | Unsolicited backlog bounded by count and wire-payload bytes. Stalled event subscribers receive a conservative slot budget using the largest accepted payload; teardown releases the backlog. Real loopback tests cover floods, oversized messages, honest bursts, and a stalled subscriber. This is a payload-retention bound, not a total-RSS guarantee. |
| [#80](https://github.com/winnowwallet/winnow/pull/80) | Already in #87; absent from baseline | BIP32 depth exhaustion throws. Descriptor origins are bounded; wallet account keys leave room for chain/index derivation before storage is written. Impossible PSBT derivation entries are ignored without aborting signing for a valid entry. |
| [#81](https://github.com/winnowwallet/winnow/pull/81) | Ported | A completed transport handoff remains recorded after disconnect and reload. Old records default to no handoff. This does not prove peer acceptance, retention, propagation, or confirmation. |
| [#82](https://github.com/winnowwallet/winnow/pull/82) | Ported and completed | Library regtest parameters and `bcrt` address handling, including no difficulty retargeting. The existing descriptor `network: HDKey.Network` API remains compatible; `bitcoinNetwork:` distinguishes signet/regtest. The shipping network picker remains mainnet/signet. |
| [#83](https://github.com/winnowwallet/winnow/pull/83) | Ported and completed | Check each proposed batch against checkpoint commitments before fetching filters; reject wrong checkpoint counts before callbacks. Prune while retaining boundaries, recent headers, and the original anchor. Deep rollback reconstructs headers from a surviving pin without replaying earlier payment callbacks. Chunk requests, bounded runs, and height arithmetic have regression tests. |
| [#86](https://github.com/winnowwallet/winnow/pull/86) | Not applicable | The author [withdrew it](https://github.com/winnowwallet/winnow/pull/86#issuecomment-5615329447): its `KnownTransaction.outputs` field does not exist upstream. Current history stores bounded bundle entries and optional raw transaction bytes; no downstream field was added merely to carry this patch. |

## Integration decisions

Current organization main was merged into #87 before porting the remaining fixes. The receive-address label branch (#96) is also included so the combined changes are tested together. The merge retains Tor routing, census controls, people flows, iPad navigation and sheet scrolling, and real background/foreground helpers. Backup screens keep #87’s file-ready summary and never display exported JSON or recovery words. UI assertions inspect the actual staged file and verify its removal after replacement, dismissal, and backgrounding.

A rejected checkpoint comparison has no payment callbacks or saved progress from that batch. A later filter, network, or callback error can happen after an earlier chunk delivered matches; the batch frontier is saved only after all chunks finish. Self-consistent filters are not authenticated by proof-of-work headers: agreement across peers and retained pins is the available check, and a sole surviving peer is a degraded mode.

The descriptor API compatibility repair and regtest retargeting control were added during review. A regtest key uses testnet extended-key versions while its address uses `bcrt`; these are different concepts.

## Verification

All 12 checks passed on integration revision `67c4d2ea104c97fcf1add55bc76c6ac5c60c2aa1` before merge commit `966fa93947b5038733f035b317053edddcea508c`. Merging current organization main produced exactly the tested source tree.

The [package and app workflow](https://github.com/winnowwallet/winnow/actions/runs/34845887449) passed package checks on both Apple silicon and Intel, with 645 reported tests across 69 suites and opt-in/platform-specific skips reported separately. The app result contains 176 passes, zero failures, and five explicit simulator protection-attribute skips. All five protection-attribute cases also passed on a physical iPad Pro (11-inch, 2nd generation), with zero skips, using a separate app identifier that preserved the TestFlight wallet.

The [Node integration workflow](https://github.com/winnowwallet/winnow/actions/runs/34845887510) passed all 26 Bitcoin Core differential tests across 10 suites and the complete ordered UI suite on both iPhone and iPad. Each UI result contains 22 passes (the host-process probe and all 21 journeys), zero failures, and one explicitly opt-in live Tor test skipped. This is evidence for the fixture-driven Tor states and routing checks, not a new real-network Tor measurement. Both devices passed receive-label persistence, backup export, two-device signing, peer reset, and catalog refresh/failure recovery. Logs, result bundles, and captured screenshots are attached to that run.

The hosted route tests passed with positive packet-capture controls and no direct destination/DNS packets from the routed probes. The 9,000-case deterministic fuzz smoke test and production first-party warning gate passed. All nine file digests in the generated build provenance, plus its Git revision, matched the reviewed source. Local validation also passed all 24 script tests with checksum-verified cloc 2.10, lint, website links, LFS integrity, and release policy. The [website workflow](https://github.com/winnowwallet/winnow/actions/runs/34845887485) passed; public screenshots are actual captures stored with Git LFS.

Earlier hosted runs exposed two header fixtures that stopped replying after 2-second waits and a large-chain filter fixture that reached its assertion without a connected peer. Tests now require each expected request and a completed handshake, with a 30-second transport/setup window under concurrent fixture mining. Production timeout/retry policies, exact errors, checkpoint-mismatch checks, recovered-chain assertions, and bounded-retry assertions remain unchanged. Both final hosted package runs passed with these corrections. The iPad backup harness also now verifies that the share popover has actually closed before continuing.

## Other superseded work

The remaining preparatory [#91](https://github.com/winnowwallet/winnow/pull/91) and [#92](https://github.com/winnowwallet/winnow/pull/92) were checked against current code. Their bounded `getaddr` crawl, endpoint filtering, overlay catalog, and census-driven generation are already incorporated through reviewed ports. The original branch heads are not ancestors of main; this conclusion comes from comparing their individual changes with the implementation and fixtures. The [generator runbook](https://github.com/winnowwallet/winnow/blob/966fa93947b5038733f035b317053edddcea508c/Tools/Generate/README.md) now describes the shared census validator, provenance, Tor candidates, and the separate census/crawl limits. These PRs require no additional production-code merge.

## Primary references

- [BIP39](https://github.com/bitcoin/bips/blob/master/bip-0039.mediawiki): NFKD seed inputs.
- [BIP32](https://github.com/bitcoin/bips/blob/master/bip-0032.mediawiki): serialized one-byte depth.
- [BIP157](https://github.com/bitcoin/bips/blob/master/bip-0157.mediawiki): checkpoint intervals, filter-header checks, and peer comparison limitations.
- [Bitcoin Core policy](https://github.com/bitcoin/bitcoin/blob/master/src/policy/policy.h): `MAX_STANDARD_TX_WEIGHT`.
- [Bitcoin Core chain parameters](https://github.com/bitcoin/bitcoin/blob/master/src/kernel/chainparams.cpp): regtest parameters.
