Connect Winnow's native screen redesign to the LeanNative renderer update

Winnow's reviewed screen changes were still local, while the supporting renderer was submitted separately. This companion app branch applies those views and pins the renderer they need, so the app source can be pulled and built together with the renderer change.

> **DEPENDENCY / HANDOFF NOTE:** This PR uses the exact head of [LeanNative/leannative#106](https://github.com/LeanNative/leannative/pull/106), `2272264d1ee7ff51331ea4c2280f52b00480dd8a`. The Lake requirement and lockfile, CI reusable workflow and release reusable workflow all use that same revision. All four references temporarily use the published `LonnieRae/leannative` fork: GitHub Actions cannot resolve a reusable workflow through the upstream repository while this commit exists only on the unmerged fork branch (the initial app PR #129 exposed that restriction). This is the same immutable renderer commit used for the local builds below. Review the renderer and app together; merge the renderer first. After the renderer merges, restore `LeanNative/leannative` in all four app files, use its final upstream SHA (which may differ after a squash), and rerun CI before merging this PR. Do not merge the app against the old renderer.

The app uses orange and neutral colors, square actions, consistent insets and clearer tap targets. Home places the iCloud backup status before Receive and Send. First Receive shows an optional backup reminder, with a direct Continue to Receive action; dismissing it records only that the prompt was shown for this wallet/network and never marks a backup complete. Saved recipients, Share my card, iCloud backup, Send, signers, protection and multisig screens use the revised layouts. Account screens retain their QR codes, addresses, Ledger checks and payment restrictions; co-signer tools sit in an expandable section. The existing nearby-Ledger popup is retained. Home Activity spacing is explicit.

The source keeps the production `WinnowLean` target, `com.btcswift.app` identity and `WinnowApp` entry point. No wallet-core or real-backend implementation changes are included. The private Winnow Review catalog, review targets, website-only fixtures, simulator identities, generated Xcode projects and build output are excluded. The H1 “Glassy, soft” icon is independently reviewable in [winnowwallet/winnow-lean#128](https://github.com/winnowwallet/winnow-lean/pull/128); this PR does not include that icon change. The launch website is [winnowwallet/website#46](https://github.com/winnowwallet/website/pull/46).

Tests follow the revised backup wording and first-Receive flow. Journey helpers dismiss the optional backup reminder and open Co-signer tools before looking for its controls. CI now builds and runs `home-presentation-test` alongside the existing suites.

Validation on the app branch with the pinned renderer:

- `lake build WinnowApp home-presentation-test records-test cloud-backup-test ios-project journeys` passes.
- `home-presentation-test`: 56 checks pass.
- Selected existing cloud-screen/shell checks: 49 pass; selected records/model checks: 1,065 pass. These are focused checks, not claims that the complete records and cloud executables ran locally.
- The production `WinnowLean` Debug target builds for the iOS simulator. It was generated from the app manifest using the pinned renderer shell; existing Lean 4.35 simulator libraries and the existing public census fixture were reused locally.
- Native Home and shared-signature layouts were inspected with the same compiled app views in a separate inert local harness; that harness is excluded from this PR.
- `scripts/check-core` and `git diff --check` pass. Wallet core, real backend and production boot code are unchanged.

Full CI, regtest/native journeys, Release builds, physical Ledger discovery/pairing/signing, live iCloud recovery, installed-wallet upgrades and complete accessibility coverage remain to be validated before shipping. The local checks do not establish those results.

Based on main `f0ada0bef6cee1761f99d118cfce8570a9e25cc7`. Fork branch: `LonnieRae:codex/native-ui-20261120`. One commit, with no AI coauthor trailer. This replaces the initial app companion #129 with a resolvable workflow reference; it does not reopen the previously closed PR #100. The original branch remains preserved.
