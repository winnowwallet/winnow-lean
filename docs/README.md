# Documentation

For using Winnow, start with the [wallet README](../README.md) and
[user guides](https://winnowwallet.com).

Developer guides in this repository:

- [Architecture](architecture.md): source ownership, module dependencies and
  directory map.
- [Testing](testing.md): local checks, suite coverage and evidence limits.
- [CI and releases](../.github/internal/ci-release.md): validation, TestFlight
  publishing and recovery of interrupted uploads.
- [CloudKit backup](../CloudKit/README.md): encryption, Apple setup and
  validation still needed on devices.
- [Security records](security/README.md): dated reports, claims and evidence.

The architecture, testing and CI guides were written for the Swift app; for the Lean port's
layout, checks and status see [PORT.md](../PORT.md).

The app bundles `mobile.html`, `read-side.html`, `write-side.html`,
`import.html` and `site.css` for offline use. Changes here affect that app copy.

The public website, blog, generator and deployment are maintained in
[winnowwallet/website](https://github.com/winnowwallet/website). Review guide
changes in both locations when they should reach both readers. Wallet CI
normalizes and retains journey evidence without deploying the website.
