# Documentation

For using Winnow, start with the [wallet README](../README.md) and
[user guides](https://winnowwallet.com).

Developer guides in this repository:

- [Architecture](architecture.md): the two Lake packages, what each library
  holds, the shell and its capabilities, keys, networking, accounts and backup.
- [Testing](testing.md): local checks, suite coverage and evidence limits.
- [CI and releases](../.github/internal/ci-release.md): validation, TestFlight
  publishing and recovery of interrupted uploads.
- [CloudKit backup](../CloudKit/README.md): encryption, Apple setup and
  validation still needed on devices.
- [Security records](security/README.md): dated reports, claims and evidence.
- [Out-of-band private payments](out-of-band-payments.md): the proposal for a card per person
  (issue #94), the constructions it was compared with, and what is built so far.

These guides describe the Lean app. The CI and release guide keeps the Swift
app's CI at its end, under "History (Swift app)". [PORT.md](../PORT.md) records
how the port was done and checked.

The app bundles `mobile.html`, `read-side.html`, `write-side.html`,
`import.html` and `site.css` for offline use
([`Project.lean`](../LeanApp/WinnowApp/Project.lean)). Changes here affect that
app copy.

Two text files here are release notes:

- `testflight-what-to-test.txt` is TestFlight's What to Test.
  [`release.yml`](../.github/workflows/release.yml) sends it with each tagged
  build, and refuses one over 4,000 characters.
- `appstore-whats-new.txt` is the App Store's What's New text. `release.yml`
  does not read it, and nothing else in this repository does. It is still the
  Swift app's note and is to be rewritten for the first Lean App Store
  submission.

The public website, blog, generator and deployment are maintained in
[winnowwallet/website](https://github.com/winnowwallet/website). Review guide
changes in both locations when they should reach both readers. Wallet CI
normalizes and retains journey evidence without deploying the website.
