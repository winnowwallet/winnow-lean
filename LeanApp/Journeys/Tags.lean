import WinnowApp.Main
import LeanNative.TagDeriving

/-! The tags of the app's messages and commands, for the record its headless journeys keep (LeanNative's
`Native.Tagging`; the journeys' `coverage.json` names the messages and commands they never sent). Derived here,
in the journeys executable, because deriving needs `Lean`, which the app that ships never imports. The outcome and
place types come first, so that a message holding one is tagged by it: `host.booted.restored`, `openSheet.send`. -/

namespace WinnowApp

deriving instance LeanNative.Tag for BootResult, Done, Sheet, Route, NetworkPage, Confirm, PasteTarget,
  LedgerSetupStep, HomeWarning, ClipPolicy

deriving instance LeanNative.Tag for Host, SendMsg, ReceiveMsg, HomeMsg, SettingsMsg, BackupMsg, PeopleMsg,
  SignerMsg, MultisigMsg, LedgerCardMsg, CloudMsg, Msg, Cmd

/-- The contexts `Model.fail` routes a failure by, each to a screen (a collection's epoch left out): which
failures a run showed, by where they were shown. -/
def failedContexts : Array String :=
  #["onboarding", "create", "create.cancelled", "import", "import.cancelled", "cloudRestore",
    "cloudRestore.cancelled", "receive", "label", "send", "rate", "settings", "peers", "delete", "open", "catalog",
    "payment", "feeBump", "export", "export.cancelled", "reveal", "reveal.cancelled", "personCard",
    "personCard.cancelled", "person", "recipients", "multisigAdd", "multisigBuild", "multisigAccount",
    "accountSpend", "ledgerPair", "signerKeys", "signer", "multisigOverview", "collect", "collect.cancelled"]

/-- A message's tag, `Host.failed` by its context: `host.failed.feeBump`, `host.failed.collect`. -/
def msgTag : Msg → String
  | .host (.failed _ context _) =>
    "host.failed." ++ ".".intercalate ((context.splitOn ".").filter fun p => p.isEmpty || !p.all Char.isDigit)
  | m => LeanNative.Tag.tag m

/-- The app, naming what it handles in the record of a run. -/
def taggedApp : LeanNative.Native.App Model Msg Cmd Host :=
  { app with tagging :=
      { msg := some msgTag, cmd := some LeanNative.Tag.tag,
        allMsgs := (LeanNative.Tag.all (α := Msg)).filter (· != "host.failed") ++ failedContexts.map ("host.failed." ++ ·),
        allCmds := LeanNative.Tag.all (α := Cmd) } }

end WinnowApp
