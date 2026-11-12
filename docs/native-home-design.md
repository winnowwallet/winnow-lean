# Native Home presentation

The Home design is implemented in Lean and the native UIKit renderer. The HTML review is a visual
reference; it is not bundled into the app or displayed in a web view.

The app change is based on the one-mode app in PR #99. It needs [LeanNative PR #89](https://github.com/LeanNative/leannative/pull/89),
branch `LonnieRae/leannative:codex/native-callout-style`, which adds `Html.callout` and optional primary-button
colour assets. The Lake files and CI workflow must point to the same reviewed framework revision.
After that dependency is merged upstream, update all three pins together.

## What changes

- Primary buttons use `BrandOrange` (`#F7931A`) with `ButtonInk` (`#172127`) in both appearances.
  Text contrast is 7.12:1. Other actions use ink in light mode and orange in dark mode.
- Buttons have the same 10 pt corner radius in both appearances. Warning cards have a 3 pt orange
  left rule, neutral fill, square left corners and 10 pt right corners. Text uses the system font
  and keeps Dynamic Type.
- Offline and syncing balances say “Last known balance.” Connection failure and privacy exposure
  remain distinct, tappable warnings. The latest PR #99 warning → explanation → Settings flow is
  preserved; Retry remains on the Sync settings screen. Test coins have their own badge above the balance.
- Receive and Send precede the protection prompts. Offline Send still opens the existing form;
  signing and broadcast validation are unchanged.
- Protection and missing-backup information use the same callout component, with body-size text.
  The Ledger explanation distinguishes pairing from moving coins into an account requiring both keys.
  The multiparty explanation no longer promises that shared signing eliminates coercion.

Thresholds, dismissal persistence, routing, Bluetooth scanning and wallet operations are unchanged.
The primary-button palette and corner radius are shared across the app; the callout layout is applied
to Home only. This is the first native screen pass, not a claim that every HTML screen has been ported.

## Review and validation

Run from `LeanApp/`:

```sh
lake build WinnowApp home-presentation-test records-test multisig-app-test
lake exe home-presentation-test
lake exe records-test
lake exe multisig-app-test
```

`home-presentation-test` checks the rendered control identifiers and dispatches their existing messages,
the stale-balance label, warning text, test-coin labeling, action order, thresholds, backup access and
permanent dismissal. CI runs it alongside the existing app tests and native journeys.

Before merging, inspect the actual iOS build in light and dark mode at default and accessibility text
sizes: offline + direct routing, syncing, synced, hardware threshold, both protection cards and missing
backup. Check wrapping, scrolling, VoiceOver reading order, and all buttons. The existing Debug-only
`WINNOW_LEAN_SAMPLE=1` launch environment reproduces the supplied 13,790,000-sat offline screenshot;
it uses sample data and cannot make real payments. Use Settings → Appearance to compare both modes.

The companion framework includes a native UI test that changes a callout to a plain column and back
in both appearances, checking control dispatch and the measured padding. UIKit compilation, that UI
test and visual parity require Xcode; passing Lean tests alone does not establish them.
