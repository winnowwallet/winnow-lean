# Winnow

Winnow is a Bitcoin wallet for iPhone and iPad, also available on Apple silicon
Mac as an iPad app. It receives and sends bitcoin and saves recipients. This
build signs with this phone's key, alone or as one signer of a k-of-n multisig
account. It is written in Lean 4: the wallet, the networking and the app's
model, update and view, compiled to C and rendered by LeanNative's generic native
shell; the curve arithmetic behind every key and signature is one secp256k1,
`Lean/SecpCt`, proved against the curve as specified in `Lean/Secp`.

[App Store](https://apps.apple.com/app/id6801502501) ·
[TestFlight](https://testflight.apple.com/join/83djpNE7) ·
[User guides](https://winnowwallet.com) ·
[Report a bug](https://github.com/winnowwallet/winnow-lean/issues)

> **Port status.** The Lean port follows upstream through 0.8.21
> (winnowwallet/winnow#259, with #256) and adds what upstream does not have:
> SegWit v0 multisig accounts, a card for one person, and one secp256k1
> implementation proved against the curve as specified. The sections below
> describe this version (0.9.x); [PORT.md](PORT.md) lists what the Lean code has
> reached and how each part is verified.


## Using the wallet

Winnow starts on mainnet with one home: your balance, Receive, Send, your
multisig accounts, activity and backup status. Open a payment to see its block
and fee and save its recipient; choose saved recipients from the Send form,
whose fee controls are folded under Fee. Settings holds the rest: Network
(sync, peers and routing, the block explorer, chain verification, and signet
for trying a development build with test funds), Security (hardware wallets
and keys, multisig accounts) and Backup (iCloud, a backup file, the recovery
words).

Receive is one page: the wallet's address at once, and under it "From one
person", where a name gives that person an address of their own and a card. The
card is a code made for them and holds neither of the wallet's keys; a Winnow
that saves it pays a new address each time, and Activity names what they pay as
theirs ([PORT.md](PORT.md#not-from-upstream-a-card-per-person-issue-94-2026-11-14)).

As the balance grows the home suggests more protection: at 0.1 BTC a Ledger,
at 0.5 BTC an account with other people's keys (each card can be dismissed).
With Bluetooth allowed, a Ledger in range while Winnow is open brings a card
whose Set up pairs it, creates a 2-of-2 of this phone and the Ledger (or a
2-of-3 with a recovery key), registers it on the Ledger and has you compare the
first receive address on both screens.

Multisig accounts are raw k-of-n accounts: a
`tr(NUMS, sortedmulti_a(k, …))` descriptor in, addresses and PSBTs out, signed
by any k signers in any order with no rounds between them. "New multisig
account" builds one from this phone, other Winnows' keys and a Ledger, for
example a 2-of-3 of two phones and a Ledger, with an optional recovery path: a
coin that has not moved for a chosen number of blocks can then be spent by
fewer of the same signers, or by a separate recovery key. A Ledger (Bitcoin
app 2.1.2 or later; 2.2.1 for a recovery path) can be a signer: Winnow pairs with it
over Bluetooth, registers the account on it, and asks it to sign after it shows
the payment on its own screen ([Ledger signer](Lean/Winnow/Ledger)).
"Join an account" also takes a SegWit v0 account, `wsh(sortedmulti(k, KEY, …))`: the
kind for a wallet one of whose keys is a single fixed public key that signs only
with ECDSA and derives nothing (a key held in a cloud key service), the others
extended keys like this phone's. Winnow shows its addresses, finds its coins, and
checks and signs a PSBT pasted from whoever builds its payments, then broadcasts
once enough signatures verify. It builds no payment from such an account itself,
and a Ledger cannot sign for one from Winnow.
There are no MuSig2 accounts, cosigner cards or shared-savings screens. A backup carrying a MuSig2
account from the shared-account Winnow is refused rather than restored without
those funds.

## Connections and privacy

Winnow connects to Bitcoin peers and matches compact block filters on your
device. It does not send your address watch list to a wallet-history server.
Direct peers can still observe your IP address, requests and relay traffic.
The app syncs while open and during short background checks scheduled by iOS;
new payments may appear at the next sync.

You can use your own filter-serving node or route peer connections through Tor
and I2P SOCKS gateways on your Tailscale network. Winnow bundles no Tor or I2P
client. See [peer gateway setup](docs/peer-gateways.md). Explorer links open an
external website after a privacy warning; they do not supply wallet balances.

## Backups

Keep a current manual backup file and your recovery words. The default file
excludes the words and restores a watch-only wallet. To restore signing through
the file-import screen, the file must include the recovery phrase; that screen
has no separate word entry. Winnow scans forward from a backup's recorded
height, so words alone do not reconstruct its past transaction history.

Automatic iCloud backup is enabled by default when available. It saves an
encrypted copy containing this phone's signing secret and wallet state. A
successful save date confirms an upload. Keep the manual file and words as
well. The
[backup guide](docs/import.html) explains the formats and their limits.

Multisig accounts and paired Ledgers follow you between your devices through
those backups. While Winnow is open, each device reads the encrypted backups
your other devices keep under the same Apple Account and takes what it lacks: an
account joined on the Mac appears on the phone, with its name, its addresses and
a payment awaiting signatures; a Ledger paired on one is listed on the other. A
removal travels too, except to a device that still sees coins in the account,
which keeps it and puts it back. No key or recovery phrase travels this way: a
device whose wallet is a different one shows the account as watch-only, and a
device restored from the same iCloud backup signs. It needs automatic iCloud
backup on; with it off, or iCloud away, the app works as before. See
[how devices keep in step](CloudKit/README.md#your-other-devices).

**Profiles.** A device can keep several profiles for a network. A profile is one
key and what it holds: its own coins, history, contacts, signers and backup, in a
directory of its own, and the multisig accounts its key is in. The home names the
open profile; tapped, it lists them, switches, renames, and adds one more (a new
one, one restored from its iCloud backup, or one from a backup file). The name
travels with the profile's backup to the person's other devices. The home lists
only the open profile's accounts and counts only its money; the others are folded
under "Watching", each saying where it signs. One sync serves every profile on the
network: the chain, peers and scan are the network's, every profile is scanned for
in every pass, and switching is instant. A device that was off takes what another
of the person's devices scanned further, once its own chain has the block that
device's backup names, and scans only the rest. On a payment of an account whose
other key is another profile's here, "Switch to … and sign" hands the payment to
that profile, which opens and signs with its own key. Keeping two profiles on one
device means that device alone can sign for both.

## Layout

- `Lean/`: the wallet in Lean 4 (`Winnow/`): keys, transactions, PSBTs, descriptors, k-of-n
  multisig accounts, silent payments, the Ledger signer, the wallet, compact-filter sync, peers, mempool windows and the broadcaster, over libuv TCP.
  `SecpCt/` is secp256k1 as it runs, the only implementation: field, points, keys, tweaks, BIP340 and ECDSA on
  machine words, doing the same work whatever a secret is. `Secp/` is what it is proved against: the curve as
  specified and signing as the BIPs give it, with bytes, SHA-256 and DER beside them. `WinnowCore.lean` is the core library, the part of `Winnow/` that
  transaction review needs (hashes and the curve, BIP32, transactions, PSBTs and sighashes, descriptors, spend
  review, the header chain) with no seed phrases, Unicode tables, coin selection, wallet naming or I/O;
  `scripts/check-core` holds its import closure to an allowed list. `TestKit/` is what the test executables
  share: the tally, the test keys, a regtest bitcoind, a fake peer. `IOTest.lean` (`io-test`) runs the network
  layer against a disposable regtest bitcoind.
- `LeanApp/`: the app: `WinnowApp/` holds the model, update, views and commands (Elm-style, LeanNative),
  `WinnowApp/Real/` the backend, `WinnowApp/E2E.lean` the Debug-only test mode, `WinnowApp/Project.lean`
  the app's manifest: LeanNative generates the Xcode project from it (`lake exe ios-project` writes the XcodeGen
  spec) and refuses a capability the app uses without its usage text or entitlement. `ios/` keeps only the
  asset catalog (the icon and the accent colour). The project links the Lean-generated C with LeanNative's native shell (renderer, C shim, capabilities:
  Keychain, device authentication, clipboard, HTTPS, paths). The shell is Objective-C printed from Lean
  at build time into `ios/build/native-shell/`, never checked in; the app compiles no Swift at all.
- `docs/`: the website and the papers the app bundles.
- [PORT.md](PORT.md): how the port was done and verified, and what differs from the Swift original
  (not in this repository or its history; it remains upstream in winnowwallet/winnow).

## Build & test

```sh
cd LeanApp
lake build backend-test records-test        # Lean toolchain leanprover/lean4:v4.35.0 (elan)
./.lake/build/bin/backend-test               # end to end against a fresh regtest bitcoind
./.lake/build/bin/records-test
cd ..
scripts/build-ios Debug                      # the app for the simulator, from a clean checkout
scripts/journeys                             # the UI journeys (Lean) against a regtest fixture (--wire: headless)
scripts/coverage                             # how much of each Lean function CI's suites run (build them first)
```

`scripts/coverage` recompiles each module's generated C with clang's coverage (Xcode's), links the test programs
as Lake does, runs CI's suites and the headless journeys, and computes Lean-level branch coverage and CRAP for
every function and declaration: `build/coverage/lean-coverage.json`. It counts decision outcomes (`if`/`switch`
arms, or entry for straight-line functions) while leaving out C codegen noise — reference-count reuse checks and
join points (`v_isShared`, `v_resetjp`, `v_reusejp`), redundant entry/condition headers, monadic `←` error-exit
pass-throughs, boxed/reduced-arity trampolines, static constant initializers, and pure library specializations —
and OR-merges peeled recursive loop clones. A declaration Lean inlined everywhere is marked `inlined`, not unrun.
`scripts/coverage <suite>` runs one suite again and keeps the others' counts; `--report [suite ...]` remakes the
report from existing profiles (all suites, or only those named).

LeanApp pins the LeanNative framework by git (`LeanApp/lakefile.toml`); `lake` fetches it into
`LeanApp/.lake/packages/leannative`.
`scripts/build-ios <Debug|Release> [iossim|ios]` runs LeanNative's
`framework/native/ci/build-ios` with Winnow's names: it builds WinnowApp, gathers the generated C, prints the
Objective-C shell, writes the Xcode project from the manifest (XcodeGen 2.46.0) and builds it. Simulator builds are ad-hoc signed (an unsigned app has no
Keychain entitlement). `backend-test --fixture <dir>` leaves a funded regtest node running for manual
simulator runs. Tests find Bitcoin Core through `WINNOW_BITCOIND` / `WINNOW_BITCOIN_CLI`, Homebrew or the
PATH; CI sets the first two to the pinned release `scripts/install-bitcoin` downloads.

### UI tests

The UI journeys are Lean, run on the Mac: `LeanApp/Journeys.lean` holds them as named steps of what a
person does on each screen, `LeanApp/Journeys/Screens.lean` those screens (create the wallet, fill the Send
form, build an account, set the recovery delay: the controls and the driver mechanics), and
`LeanApp/Journeys/Host.lean` the other side (the fixture's node through `bitcoin-cli`, Bitcoin Core wallets as
co-signers, backend-test's silent payment receiver). Controls are named by `LeanApp/WinnowApp/Ids.lean`, the
same definitions the views give their nodes (`Html.identified`), so a control a journey names but no view has
does not compile. Each journey launches the app in test mode on the regtest node of `backend-test --fixture`
and checks the app against the node; a step that cannot be done fails with its name, the driver's reason and
what was on screen, and the log shows each step's time:

- `createReceiveSendConfirm`: create a wallet, receive from the node, review and send a payment the
  node accepts, see it confirm;
- `multisigTwoOfThreeWithRecovery`: a 2-of-3 with two Bitcoin Core wallets, built in the app; the
  first address is Core's, the phone and both Cores sign, Core accepts a witness with exactly two
  signatures; after the one-day delay the phone alone spends on the recovery path;
- `ledgerPairVerifySpend`: pair test mode's simulated Ledger, have it verify the receive address,
  and spend with the phone's and the Ledger's signatures;
- `ledgerCardTwoOfTwo`: test mode's simulated Ledger advertising brings the nearby card over the home; Set up
  pairs it, creates the 2-of-2 of this phone and the Ledger, registers it and shows the first receive address
  on both; the node pays that address and the account sees the coin;
- `shippedCensus`: the census peer list the build ships shows in Settings on mainnet;
- `silentPaymentSend`: pay a BIP352 code; the node's transaction pays the one output backend-test's
  receiver (written from the BIP's receiving side) finds, and the receipt shows its address;
- `feeBumpReplaceConfirm`: send at a low rate, then bump the fee from the unconfirmed payment's screen;
  Core checks that the replacement spends the same coins, pays more fee, and is the one that confirms;
- `spentElsewhere`: the same recovery phrase on another device spends the phone's coins; a review whose coin
  has gone fails when the owner signs and Send can be used again, a payment the node refuses is found out from
  the block that confirms the other spend, and a coin that spend did not take comes back;
- `retryAfterNoPeers`: the node goes off the network while Winnow is in the background; Home says Offline, its
  alert leads to Settings → Network → Sync, and with the node back Retry there reconnects and the wallet finds
  a payment the node sends;
- `cardForOnePerson`: the wallet makes a card for one person; the node, holding only the card's text, derives
  its first two addresses and pays each, and Activity names both as received from that person;
- `accountFollowsDevices`: two launches with two seeds and one directory standing in for iCloud are two
  devices of one person; an account built and paid on the first shows on the second by itself, watch-only,
  with the balance its own scan confirms;
- `twoWalletsOneDevice`: Settings → Profiles adds a second profile beside the first; the second builds a 2-of-2
  of the two, the node pays it, its payment is signed by the open profile, handed to the other with "Switch to
  … and sign", signed there, and broadcast;
- `torOnly`: Settings → Peers and routing puts the wallet on Tor alone (the node's onion name as its peer,
  Manual routing, the fixture's SOCKS5 gateway), and a payment from the node is found through the gateway;
- `peerFailures`: the wallet's one peer is the fixture's proxy in front of the node, which drops every
  connection and then stalls on an open one; Home says so each time, and the wallet finds the next payment once
  the peer serves again;
- `reorgBackToPending`: a confirmed payment's block is replaced by a longer chain without it; the payment is
  pending again with its change still counted, and confirms again in the new chain.

And three that fail on purpose, each where a failure happens on a phone, then try again
(`LeanApp/Journeys/Failures.lean`):

- `capabilityFailures` (headless only: LeanNative's `failNext` has the fake shell fail a capability): the person
  cancels the authentication before creating, before the recovery phrase and before a backup file with it; the
  Keychain refuses the new wallet's key, the read of the phrase and the delete;
- `backendFailures`: a fresh address, a label's save, the backup file and resetting the peers fail;
- `paymentFailures`: a payment's broadcast and its fee bump's fail, and the node is given nothing.

Winnow's own failures are test mode's (`LeanApp/WinnowApp/Faults.lean`): the control file the Paste buttons read
names them (`Run.fail point`: `store.write.<file>`, `broadcast`, `feeRate`, `receive.fresh`, `export`,
`peers.reset`, `payment.details`), and `Faults.check` throws one where the operation would fail, before it changes
anything. Outside test mode, which only a Debug build resolves, none is named. Headless, `coverage.json` beside
`journeys.json` says which of the app's messages and commands the journeys never sent or ran, and which failure
screens (`host.failed.<context>`) they never showed.

They run two ways, both LeanNative's runners with `scripts/ui-fixture` as their hooks (a regtest node; a SOCKS5 gateway in front of it for .onion and .i2p names,
`scripts/socks-gateway`; and a proxy in front of it a journey tells to pass, drop or stall, `scripts/peer-proxy`). `scripts/journeys --wire`
(LeanNative's `wire-journeys`) runs them against the app itself, headless: the journeys executable
runs the app as a child of itself with a fake shell (LeanNative's `LEANNATIVE_DRIVER=wire`: a Keychain in a file,
paths under the evidence directory, no network, no Bluetooth) and finds each element in the app's view tree, so
they run against the fixture's node with no simulator; CI runs this in the `lean` job. What
it does not test is the renderer and real touches, which the simulator run does.
`scripts/journeys` runs them as CI does in the `app` job: LeanNative's `ui-tests` on a throwaway simulator (or `UI_SIMULATOR`)
with the journeys as `UI_JOURNEY`, and `scripts/ui-fixture` starting the node before and collecting the app's
test-mode journals after; it keeps the result bundle, a screen recording, the screenshots, `journeys.json`
(each journey's result and time) and the journals. `scripts/journeys silentPaymentSend` runs only the journeys
named.

### CI and TestFlight

`.github/workflows/ci.yml` calls LeanNative's reusable `ios-app` workflow on every pull request that is ready for
review and changes more than the docs, on every push to main, and by hand, in three jobs on GitHub's own macOS runners (free for a public repository; a fork's pull request
gets them too) that start at once and each build the Lean from the cache; every long step prints its progress as it
goes. Every run is the same, full run:

| job | what |
|---|---|
| `lean` | builds `Lean/` and `LeanApp/` (every proof) and the test executables, imports the census list, then runs at the same time: `scripts/check-core`, `scripts/secp-vectors --check`, census-check on that list, the scripts' tests, multisig-test, ledger-test, silent-payment-test, card-keys-test, crypto-test, segwit-test, secpct-test, fuzz, records-test, multisig-app-test, ledger-transport-test, cloud-backup-test, device-sync-test, and `scripts/ci-regtest`'s five suites as five lines, each against its own disposable regtest bitcoind: io-test, backend-test, multisig-differential (9 cases, six of them nested), card-regtest and segwit-regtest; and every journey headless, the twenty (LeanNative's `wire-journey`), with `coverage.json` among the evidence |
| `app` (three at once) | the same build and census import; Debug for the simulator, checked for Swift; fourteen of the journeys split across the three, four or five each (`ui-journey-shards`; `scripts/ui-fixture` as the hooks); the three that fail on purpose, `torOnly`, `peerFailures` and `reorgBackToPending` run headless only |
| `media` | once both parts pass, the website's media from their evidence (LeanNative's `journey-media`: one video, the journeys in order) |
| `release` | the same build and census import; Debug and Release for the simulator and Release for devices, each checked for Swift, and that Release ignores test mode (LeanNative's `test-mode-env`) |

`.github/workflows/release.yml` calls LeanNative's release workflow (`ios-release.yml`, at the pinned commit):
a `vMAJOR.MINOR.PATCH` tag finds a successful full CI run (main's push or one by hand: not a pull
request's) on the same tree, then archives the app as `com.btcswift.app` (team 2858MX5336, the identity of the
Swift app it replaces), checks the archive and the exported IPA, uploads it and adds it to TestFlight's internal
group. Every step is LeanNative's `leannative-release` (Lean), which LeanNative's README describes. It uses the
repository's secrets `ASC_KEY_ID`, `ASC_ISSUER_ID`, `ASC_PRIVATE_KEY`, `DEV_CERT_P12` and
`DEV_CERT_P12_PASSWORD`. Dispatched by hand it does everything but the upload: the build, signing, the archive
and export with their checks, and a read-only App Store Connect call.

The public website is maintained in
[winnowwallet/website](https://github.com/winnowwallet/website). This repository
contains the app's offline guides and engineering records. The
[roadmap](https://winnowwallet.com/roadmap) tracks proposed work separately from current behavior.

## License

Winnow is available under the [MIT License](LICENSE).
