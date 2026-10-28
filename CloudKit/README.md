# iCloud wallet backup

Winnow automatically uploads an encrypted wallet backup when iCloud is
available. It is enabled by default in Simple and Advanced modes. Simple shows
**Backing up**, **Backed up** or **Not backed up**; Advanced holds the persistent
backup switch, manual export and recovery words. The wallet remains usable
without an Apple Account, and changing interface mode preserves the preference.

Keep a current manual file and recovery words. A successful save date confirms
that CloudKit accepted ciphertext. It does not establish that the wrapping key
has synchronized or that recovery has been verified on another device. See the
[manual backup guide](../docs/import.html) for the available file-import route
and its limits.

## Contents and ownership

The backup includes this phone's recovery phrase, wallet descriptor, tracked
funds, payment history and address counters. Its app context
also includes saved people and payment cards, sender names, receive-address
labels, display name and interface mode. Watch-only and xprv-only wallets use manual files because
this automatic format requires a mnemonic. Peer and explorer endpoints stay
device-local. Manual file export does not include the extra app context.

The implementation lives in the app:

- [CloudWalletBackup](../Sources/WinnowApp/CloudWalletBackup.swift) encodes and
  authenticates the encrypted envelope.
- [CloudBackupController](../Sources/WinnowApp/CloudBackupController.swift) owns
  preferences, preparation, retries, account binding and successful-save state.
- [ICloudBackupStore](../Sources/WinnowApp/ICloudBackupStore.swift) writes private
  CloudKit records and provides a separate wrapping-key store.

WalletCore owns the wallet import format and the contact-card rules; it has no
CloudKit dependency.

## Encryption and update behavior

The phrase and wallet state are sealed separately with AES-256-GCM. App context
is inside the authenticated wallet ciphertext. The random wrapping key uses a
separate synchronizable iCloud Keychain service, accessible while unlocked.
CloudKit stores ciphertext with a backup ID, network and save date. The local
signing key retains its device-only, user-presence access controls.

Access to the cloud ciphertext and its wrapping key is sufficient to recover
the backed-up signing secret. This adds trust in Apple Account and iCloud
Keychain security and recovery. No phrase or plaintext wallet bundle is written
to the upload staging file.

Initial preparation uses device authentication. Existing wallets initialize at
a foreground opportunity, with at most one backup authentication per foreground
session; an unavailable Apple Account does not itself prompt. Automatic updates
reuse the encrypted phrase and export fresh public wallet state after refresh,
without rereading the signing key. Pending sends defer updates, so the displayed
save date can lag.

The opt-out is stored separately from upload configuration. Failures retry in
the foreground with backoff from 60 seconds up to five minutes. The first
available account is pinned before upload; later account changes cannot
overwrite that copy. Failure, cancellation, a wallet switch or an account
mismatch cannot advance the successful-save date. Backup records have independent
IDs; the feature is not live multi-device wallet synchronization.

Version 2 includes authenticated app context. Version 1 remains readable and
lacks that context; an automatic update can upgrade it without rereading the
phrase. The envelope is bounded to 32 MiB and app context to 10 MiB, with tighter
structural bounds in individual stores. Validation precedes changes to wallet
or Keychain state.

Disabling automatic updates keeps the existing cloud copy. Deleting the local
wallet also leaves that copy.

## Apple setup

The app entitlement names `iCloud.com.btcswift.app`. Associate that container
with the `com.btcswift.app` App ID and refresh signing profiles through automatic
signing. Provisioning and production schema deployment are Apple account
operations; an unsigned build does not establish their completion.

[schema.ckdb](schema.ckdb) is authored schema source. Import it into development,
then deploy through [CloudKit Console](https://icloud.developer.apple.com/).
Listing records requires the `___recordID` query index, network query index and
save-date sort index. The app uses the private database; do not grant public
database access.

With an authorized management token stored securely in the local Keychain:

```sh
xcrun cktool import-schema --team-id 2858MX5336 \
  --container-id iCloud.com.btcswift.app --environment development \
  --file CloudKit/schema.ckdb
```

Keep management tokens, signing keys and user backup contents out of source,
command arguments and CI logs. Apple documents
[schema deployment](https://developer.apple.com/documentation/cloudkit/deploying-an-icloud-container-s-schema)
and [iCloud configuration](https://developer.apple.com/documentation/xcode/configuring-icloud-services).

## Validation

[AppTests/CloudWalletBackupTests.swift](../AppTests/CloudWalletBackupTests.swift)
checks encrypted round trips, restored signing material, counters, updates,
tampering, wrong keys and bounded decoding in the iOS app test host. It is no
longer a SwiftPM package suite. Other app tests use in-memory cloud and key
stores for defaults, retries, account changes, cancellation and persistent
opt-out. See the [testing guide](../docs/testing.md) for commands and CI evidence.

Actual CloudKit transport, provisioning, account behavior and wrapping-key
synchronization require physical-device validation. End-to-end two-device
restore evidence is still outstanding. Use disposable test wallets and signet
funds for that work, and retain the device configuration, revision and result
before expanding recovery guidance.
