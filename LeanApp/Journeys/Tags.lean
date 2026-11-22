import WinnowApp.Main
import LeanNative.TagDeriving

/-! The tags of the app's messages and commands, for the record its headless journeys keep (LeanNative's
`Native.Tagging`; the journeys' `coverage.json` names the messages and commands they never sent). Derived here,
in the journeys executable, because deriving needs `Lean`, which the app that ships never imports. The outcome and
place types come first, so that a message holding one is tagged by it: `host.booted.restored`, `openSheet.send`. -/

namespace WinnowApp

deriving instance LeanNative.Tag for BootResult, Done, Sheet, Route, NetworkPage, Confirm, PasteTarget,
  LedgerSetupStep, HomeWarning, ClipPolicy, WalletFail, PaymentFail, SettingsFail, PeopleFail, MultisigFail, FailTarget

deriving instance LeanNative.Tag for Host, SendMsg, ReceiveMsg, HomeMsg, SettingsMsg, BackupMsg, PeopleMsg,
  SignerMsg, MultisigMsg, LedgerCardMsg, CloudMsg, Msg, Cmd

/-- Targets where a cancelled device prompt or in-flight operation is handled distinctly from a failure. -/
def cancellableTargets : Array FailTarget :=
  #[.wallet .create, .wallet .importWallet, .wallet .cloudRestore, .wallet .unlock,
    .settings .exportBundle, .settings .reveal, .people .personCard, .multisig (.collect 0)]

/-- A message's tag, `Host.failed` by its typed target (plus `.cancelled` when cancelled). -/
def msgTag : Msg → String
  | .host (.failed _ target true _) => "host.failed." ++ LeanNative.Tag.tag target ++ ".cancelled"
  | m => LeanNative.Tag.tag m

/-- The app, naming what it handles in the record of a run. -/
def taggedApp : LeanNative.Native.App Model Msg Cmd Host :=
  { app with tagging :=
      { msg := some msgTag, cmd := some LeanNative.Tag.tag,
        allMsgs := LeanNative.Tag.all (α := Msg) ++ cancellableTargets.map fun t => "host.failed." ++ LeanNative.Tag.tag t ++ ".cancelled",
        allCmds := LeanNative.Tag.all (α := Cmd) } }

end WinnowApp
