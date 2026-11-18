# iCloud wallet backup

Winnow automatically uploads an encrypted wallet backup when iCloud is
available. It is on by default. Settings → Backup shows **Backing up**,
**Backed up** or **Not backed up** and holds the backup switch, the backup file
and the recovery words; while nothing is backed up, the home offers a backup
file instead. The wallet remains usable without an Apple Account.

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
IDs, one per device; the wallet itself is not synchronized between devices. Its
multisig accounts and signers are: see [Your other devices](#your-other-devices).

Version 2 includes authenticated app context. Version 1 remains readable and
lacks that context; an automatic update can upgrade it without rereading the
phrase. The envelope is bounded to 32 MiB and app context to 10 MiB, with tighter
structural bounds in individual stores. Validation precedes changes to wallet
or Keychain state.

Disabling automatic updates keeps the existing cloud copy. Deleting the local
wallet also leaves that copy.

## Your other devices

Multisig accounts and signers (paired Ledgers, saved keys) follow a person
between their devices through these same records. Nothing else is stored for
it: no new record type, no new key, no schema change. Each device's wallet box
already lists its accounts and signers; a device keeps in step by opening the
wallet boxes of the other backups on its network, with their keys from iCloud
Keychain, and taking what it lacks. It never opens another backup's phrase box,
so no key or recovery phrase reaches a device this way. A device whose wallet
is a different one shows an account it took as watch-only; one restored from the
same backup holds the same key and signs.

The rules are [DeviceSync](../Lean/Winnow/Wallet/DeviceSync.lean) (what one
device does with what another's backup says, with no file or network in it);
the app's side is [Real/DeviceSync](../LeanApp/WinnowApp/Real/DeviceSync.lean).

- **What follows.** An account's descriptor, name, address counters, the
  Ledger's registration of it, and a payment awaiting signatures; a signer's
  keys and name. An account arrives with the other device's coins and history,
  current to the block that device had scanned; the receiving device scans the
  blocks between that one and its own itself before it watches the account, and
  shows it as catching up until then.
- **What does not.** The wallet's own key and coins, peer and explorer
  settings, and a payment already broadcast but not yet confirmed (the other
  device sees it when a block takes it).
- **Stamps.** The backup's app context carries, for each account and signer,
  when it was added, removed, renamed, registered or its draft changed, and on
  which device (`sync`). The later change wins; address counters take the
  highest; two copies of one payment are combined, so signatures made on two
  devices add up. A device never stamps behind a stamp it has seen, so two
  clocks that disagree do not reorder changes one device made after seeing the
  other's.
- **Removal.** Only the app's own Remove removes elsewhere; a deleted wallet or
  a file set aside removes nothing. A removal that reaches a device still
  seeing coins or a payment in the account is not followed there: that device
  keeps the account and the others take it back.
- **Older backups.** One written before this carries no stamps. Its accounts
  and signers are still taken, as added at the beginning of time, so a removal
  made since beats them, and its names never replace a device's own.
- **When.** There is no push: the app's shell has CloudKit's records and no
  subscriptions. A device looks when it comes to the foreground and then about
  once a minute while open, and saves its own backup a few seconds after a
  change. A backup already read is not downloaded again until it is saved
  again.
- **Off.** With automatic backup off for a wallet, without an Apple Account, or
  under a different account than the one the backup is bound to, nothing is
  read and nothing follows; the wallet works as before. A backup whose key has
  not arrived from iCloud Keychain is passed over until it has.

Limits worth knowing. A device's backup waits while a payment from its own
wallet is unconfirmed, and so does what the others can take from it. Stale backups of installs that are gone stay in iCloud
(nothing here deletes a record) and are read once each. An account whose
arriving copy is older than the first header the receiving device holds waits
for the other device to save a newer one. Two devices that build payments from
the same account at the same moment each see the other's only after a look; the
later one wins and the earlier is replaced.

Validation: `device-sync-test` holds the rules case by case and runs two and
three phones over one in-memory iCloud; `backend-test`'s `devicesFlow` runs two
on regtest, where the second finds a coin paid after the first one's backup by
its own scan and a payment gathers its signatures across both. Real iCloud
between two real devices has not been tried by any test.

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
