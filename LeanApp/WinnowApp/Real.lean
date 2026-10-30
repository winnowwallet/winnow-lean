import WinnowApp.Real.Base
import WinnowApp.Real.Stack
import WinnowApp.Real.Wallet
import WinnowApp.Real.Send
import WinnowApp.Real.Peers
import WinnowApp.Real.BackgroundSync
import WinnowApp.Real.Shell
import WinnowApp.Real.Assemble
import WinnowApp.Real.Full
import WinnowApp.Real.MultisigStore
import WinnowApp.Real.CloudBackup
import WinnowApp.Real.CloudApp

/-! # `Backend.real` (aggregator): AppModel's wallet and network logic over the Lean WalletCore

| Module | AppModel.swift |
|---|---|
| `Real/Base.lean` | the state (one `Core` under a `Std.Mutex`), `Deps`, `Hooks`, `AppError` texts (:52–96) |
| `Real/Stack.lean` | stack build/teardown, rollback marker, phase ticker, sync loop, `syncOnce` (:569–1006) |
| `Real/Wallet.lean` | open, create, adopt, import, export, reveal, destroy, receive, `refresh` (:470–1476) |
| `Real/Send.lean` | fee rate, previews, send, fee bump, payment details, mempool windows (:899, :1539–1892, :2191) |
| `Real/Peers.lean` | scene phase start/stop, reconnect, retry, the census line, peers, reset (:553, :2586–2665) |
| `Real/BackgroundSync.lean` | background chain checks: `BackgroundSyncRun`, `runBackgroundSync` (BackgroundSyncScheduler.swift) |
| `Real/Shell.lean` | the shell's `keychain.*` and `http.get` capabilities as `KeyStore IO` and `HttpFetch` |
| `Real/Assemble.lean` | the core fields of the `Backend` record (`Backend.coreWithEnv`) |
| `Real/Records*.lean` | people and labels (PeopleStore, ReceiveAddressLabelStore, AppModel) |
| `Real/Full.lean` | `Backend.real`: both halves joined through `Hooks` |
| `Real/CloudBackup.lean` | the iCloud backup's controller, CloudKit store and iCloud Keychain keys (CloudBackupController.swift, ICloudBackupStore.swift) |
| `Real/CloudApp.lean` | AppModel's iCloud flows: preparation, updates, restore; `Backend.realWithCloud` |

Differences from AppModel, all forced by the Lean app's shape:

* The Lean app starts networking only for a ready wallet, so `createWallet` / `importBundle` build a
  stack themselves when none exists (AppModel's `buildStackIfNeeded` also requires the scene to be
  active, and the stack would already be up during onboarding). A wallet created before networking
  starts dates at the local header tip.
* The stage, the backup-pending flag and the device-authentication gate live in the Model and in
  `perform` (`authenticated`); the backend does not repeat them.
* The fee floor is read from the connected peers when a rate is resolved (AppModel reads the value
  its last `refresh` stored). -/
