[Back to evidence README](README.md)

# The Keychain's user-presence access control on a device, 2026-11-18

`SEC-060` in the [findings register](../findings.md) puts the wallet secret's
Keychain item behind an access control that requires the person. A simulator
cannot show that this holds: its Keychain accepts the access control and then
gives the value to any read. This record is the run on an iPhone that shows it.

**What was run is LeanNative's demo app, not Winnow.** The demo's
`keychain-user-presence` self-test exercises the same shell capability, with
the same requests, that Winnow's key store makes
(`LeanApp/WinnowApp/Real/Shell.lean`). Winnow itself has not been run on a
device with this change; see "Not shown" below.

- **Device:** iPhone 17 Pro Max (iPhone18,2), iOS 27.2 (24B119), with a
  passcode and Face ID.
- **Revision:** LeanNative/leannative `cf2b0f9bb37f8acb80aec67cf9d4e1a9d6e75922`
  (LeanNative/leannative#100), clean tree. That branch was then squashed into
  one commit, `fa0c7d84ad47a0e43fe8ee54a81dd8186454144e`, which this app is
  pinned at; both have the same tree,
  `3da2118d958f49f016ce9f4b22802bce921fc7b8`, so the source that ran is the
  source that is pinned.
- **Command:** `DEVICE=… DEVELOPMENT_TEAM=… HAND_SECONDS=60 framework/native/ci/device-run <out>`,
  started 2026-11-18T13:04:49Z, Xcode 27.2 (27B52), a Debug build signed for
  development. Face ID was answered once for the self-test.

## The self-test's lines, as the device printed them

```text
selftest: keychain-user-presence add: ok added, access userPresence
selftest: keychain-user-presence attributes: ok userPresence true, accessible (not said), synchronizable false
selftest: keychain-user-presence attributes before protect: ok userPresence false, accessible whenUnlockedThisDeviceOnly, synchronizable false
selftest: keychain-user-presence protect: ok changed true
selftest: keychain-user-presence protect again: ok changed false
selftest: keychain-user-presence attributes after protect: ok userPresence true, accessible (not said), synchronizable false
selftest: keychain-user-presence set over it: failed status -25308 (-25308)
selftest: keychain-user-presence set asking for it: failed status -50 (-50)
selftest: keychain-user-presence add synchronizable: failed status -50 (-50)
selftest: keychain-user-presence get without a context: failed status -25308 (-25308)
selftest: keychain-user-presence get of the upgraded item without a context: failed status -25308 (-25308)
selftest: keychain-user-presence get with a context that never was: failed status -25308 (-25308)
selftest: keychain-user-presence auth with keep: ok a context kept
selftest: keychain-user-presence get with the context: ok the value it was given
selftest: keychain-user-presence second get with the same context: ok the value it was given
selftest: keychain-user-presence auth.end: ok ended
selftest: keychain-user-presence get after auth.end: failed status -25308 (-25308)
selftest: keychain-user-presence cleanup: ok nothing left
selftest: keychain-user-presence: PASS: flag applied: yes; flag read back: yes; in-place upgrade worked: yes; unauthenticated read refused: yes (-25308); authenticated read with a kept context after ONE prompt: yes; second read under the same context with no second prompt: yes; refused again after auth.end: yes (-25308); set and synchronizable refusals: yes; left nothing behind: yes
```

Status `-25308` is `errSecInteractionNotAllowed`; `-50` is `errSecParam`. The
self-test prints no values.

## What this shows

- An item added with the access control is stored, and a read of it with no
  authentication is refused without a prompt.
- An item stored without it is upgraded in place by one update
  (`protect: ok changed true`), and is then refused without authentication.
  A second upgrade changes nothing (`protect again: ok changed false`). This
  is what `KeyStore.upgradeProtection` does to a wallet stored by an earlier
  build each time it opens.
- One Face ID prompt covers two reads under the authentication the shell
  kept, and a read after that authentication is ended is refused again.
- An id that names no kept authentication satisfies nothing.

## The run before it

A first run the same day at LeanNative `b563ab7` showed the same refusals and
the same single prompt, and failed two steps:

```text
selftest: keychain-user-presence: FAIL: flag applied: yes; flag read back: NO; in-place upgrade worked: NO; unauthenticated read refused: yes (-25308); authenticated read with a kept context after ONE prompt: yes; second read under the same context with no second prompt: yes; refused again after auth.end: yes (-25308); set and synchronizable refusals: yes; left nothing behind: yes
```

On a device the Keychain gives nothing of a protected item to a query that
allows no interaction, not even its attributes, so the shell could not read
back that an item was protected and a second `protect` failed with `-25308`.
In this app that would have journaled `keychain.protectionUpgradeFailed` at
every open after the first. The shell now reads that refusal, while the device
is unlocked, as the item being protected already; the run above is of that
source.

## Not shown

- Winnow itself on a device with this change: that an existing wallet's item
  is upgraded when it opens, and that creating a wallet, sending, bumping a
  fee, signing for a multisig account and showing the phrase each ask once.
  The headless `feeBumpReplaceConfirm` journey does these against a fake
  shell that refuses as the device did.
- A phone upgraded from the Swift app, whose item already carries the access
  control.
- A device with no passcode, where storing the item is expected to fail.
- A kept authentication ending at its time limit or when the app goes to the
  background; the self-test ends it explicitly.
