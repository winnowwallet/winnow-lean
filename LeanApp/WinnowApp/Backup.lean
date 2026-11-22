import WinnowApp.Common
import WinnowApp.Ids

/-! BackupSection.swift (the backup file and the recovery words, on the home's Back up page and in
Settings → Backup), ExportBundleView, RevealPhraseView, and CloudBackupView.swift (CloudBackupView, the
automatic-backup controls, and CloudRestoreView, onboarding's restore from iCloud). Both results are sensitive: each request carries a
fresh epoch, and an answer counts only while that epoch is current and the app is active. -/

namespace WinnowApp
open LeanNative

/-- Start a sensitive operation: a new epoch, so an older answer can never land. -/
def Model.beginEpoch (m : Model) : Model := { m with epoch := m.epoch + 1 }

def Model.export (m : Model) : Model × List Cmd :=
  let m := m.beginEpoch
  let name := s!"winnow-{m.settings.network.name}-{m.walletID.getD "wallet"}.json"
  ({ m with exportState := { m.exportState with busy := true, error := none, file := none }, confirm := none },
   m.discardExport ++ [.exportBundle m.generation m.epoch m.exportState.includeMnemonic name])

def stepBackup (msg : BackupMsg) (m : Model) : Model × List Cmd :=
  match msg with
  | .openExport => (({ m with exportState := {} }.beginEpoch).present .exportBundle, [])
  | .setIncludeMnemonic b =>
    -- any change resets the export (`resetExport`): the old file must not be shared as the new one
    ({ m.beginEpoch with exportState := { includeMnemonic := b } }, m.discardExport)
  | .createExport =>
    if m.exportState.busy then (m, []) else
    if m.exportState.includeMnemonic then ({ m with confirm := some .exportWithPhrase }, []) else m.export
  | .confirmExport => m.export
  | .reveal =>
    if m.reveal.revealing || m.walletID.isNone then (m, []) else
    let m := m.beginEpoch
    ({ m with reveal := { revealing := true } }, [.revealPhrase m.generation m.epoch])
  | .copyPhrase =>
    ({ m with reveal := { m.reveal with copied := true } }, [.copy (" ".intercalate m.reveal.words) .recoveryPhrase])

/-- CloudBackupView and CloudRestoreView. -/
def stepCloud (msg : CloudMsg) (m : Model) : Model × List Cmd :=
  match msg with
  | .openBackup => if m.walletID.isNone then (m, []) else (m.present .cloudBackup, [])
  | .setAutomatic b => (m, [.setAutomaticCloud b])
  | .openRestore =>
    -- `.task { await model.discoverCloudBackups() }`
    ({ m with onboarding := { m.onboarding with restoring := false, restored := false, restoreError := none } }.present .cloudRestore,
     [.discoverCloud])
  | .restore id =>
    if m.onboarding.restoring || m.walletID.isSome then (m, []) else
    ({ m with onboarding := { m.onboarding with restoring := true, restoreError := none } },
     [.restoreCloud m.generation m.settings.network id])
  | .checkAgain => if m.onboarding.restoring || m.cloud.busy then (m, []) else (m, [.discoverCloud])

/-! ## View -/

/-- The iCloud backup's state in a word or two, for the Settings row: "Backed up 5 min ago", "Off",
"Not available" (a build without the iCloud entitlement). -/
def cloudRowStatus (c : CloudStatus) : String :=
  if c.issue == some .unavailableInBuild then "Not available"
  else if !c.automaticEnabled then "Off"
  else if c.statusTitle == "Backed up" then
    match c.lastSavedAgo with | some ago => s!"Backed up {ago} ago" | none => "Backed up"
  else c.statusTitle

/-- Settings → Backup: the iCloud backup, the backup file and the recovery words. The texts are a deliberate
departure from upstream (PORT.md, user 2026-10-28). -/
def backupSection (m : Model) : H :=
  .section "Backup" "iCloud backup keeps this wallet automatically. A backup file is a copy you keep yourself."
    ([.identified Ids.cloudBackupRow
       (.row [navLink "iCloud backup" (if m.walletID.isNone then none else some (.cloud .openBackup)) (symbol := "icloud"), .spacer,
              .identified Ids.cloudBackupRowStatus (Html.tone .secondary (body (cloudRowStatus m.cloud)))])] ++
     [ .identified Ids.exportBundleButton (Html.symbol "doc.badge.arrow.up" (.button "Save a backup file" .plain (if m.walletID.isNone then none else some (.backup .openExport)))) ] ++
     [.identified Ids.revealPhraseButton
       (Html.symbol "key" (.button "Show recovery phrase" .plain (if m.walletID.isNone || m.reveal.revealing then none else some (.backup .reveal))))] ++
     (if m.hasSheet .revealPhrase then [] else errorRows m.reveal.error))

/-- Home's Backup section: compact iCloud backup status. Actionable issues and off-state link to iCloud
backup settings; transient offline retries stay quiet; manual backup files stay in Settings → Backup. -/
def beginnerBackupSection (m : Model) : H :=
  let c := m.cloud
  let icon := if c.statusTitle == "Backed up" then "checkmark.icloud"
              else if !c.automaticEnabled || c.issue == some .unavailableInBuild then "icloud.slash"
              else "icloud"
  let actionable := match c.issue with
    | some i => if i.isTransient then none else some i
    | none => none
  let showLink :=
    c.issue != some .unavailableInBuild &&
    (!c.automaticEnabled || actionable.isSome || c.statusTitle == "Not backed up")
  .section "Backup" ""
    ([ .identified Ids.cloudBackupStatus (Html.symbol icon (body c.statusTitle)) ] ++
     (match c.lastSavedText with | some t => [caption s!"Last saved {t}"] | none => []) ++
     (match actionable with | some i => [caption i.message] | none => []) ++
     (if showLink then
       [.identified Ids.homeCloudBackupButton (navLink "iCloud backup" (some (.cloud .openBackup)) (symbol := "icloud"))]
      else []))

/-- CloudBackupView (Settings → Backup → iCloud backup): the switch and the state. -/
def cloudBackupSheet (m : Model) (inner : List H) : H :=
  let c := m.cloud
  formSheet "iCloud backup" (some .closeSheet) [closeBar "Close"]
    [ .section "" "Includes this phone’s signing key, wallet history, saved people and labels. Updates while Winnow is open."
         ([ .identified Ids.automaticCloudBackupToggle (.toggle "Automatic iCloud backup" c.automaticEnabled fun b => .cloud (.setAutomatic b))
          , .identified Ids.cloudBackupStatus (.labeled "Status" (cloudRowStatus c)) ] ++
          (match c.lastSavedText with | some t => [.labeled "Last saved to iCloud" t] | none => []) ++
          (match c.issue with | some i => [caption i.message] | none => []))
     , .section "Your other devices" "Multisig accounts and paired Ledgers follow you: each device reads the others’ backups while Winnow is open and takes what it lacks. A device none of whose wallets holds one of an account’s keys shows it as watch-only. Keys and recovery words never travel this way."
         (match c.devicesNote with
          | some t => [.identified Ids.cloudDevicesNote (caption t)]
          | none => [.identified Ids.cloudDevicesNote (caption (if c.automaticEnabled then "Not checked yet." else "Off while automatic backup is off."))])
     , .section "" ""
         [ body "Restore using the same Apple Account with iCloud and Passwords & Keychain enabled. Access to the cloud backup and its synchronized key can restore spending access."
         , body "Turning this off leaves existing copies in iCloud." ] ] inner (largeTitle := true)

/-- A saved backup as the restore list names it: which wallet, where that could be read, and when it was saved. -/
def restoreLabel (b : CloudBackupInfo) : String :=
  match b.walletID with
  | some wallet => s!"Wallet {wallet} · {b.savedAtText}"
  | none => b.savedAtText

/-- CloudRestoreView: choose a saved backup; restoring never replaces a wallet already on this phone. -/
def cloudRestoreSheet (m : Model) (inner : List H) : H :=
  let c := m.cloud
  let o := m.onboarding
  formSheet "Restore from iCloud" (some .closeSheet) [closeBar "Close"]
    ((if o.restored || m.walletID.isSome then
       [.section "" ""
         ([ body "Your wallet is restored. Keep Winnow open to check for newer payments and finish this device’s automatic backup." ] ++
          (match c.restoreNotice with | some n => [body n] | none => []) ++
          [ .button "Continue" .primary (some .finishOnboarding) ])]
      else
       [.section "Choose a saved backup" "Use the same Apple Account and enable Passwords & Keychain. Backups may take time to appear on a new device. Restoring never replaces a wallet already on this phone."
         ((c.available.map fun b =>
             .identified (Ids.cloudRestoreBackupButton b.id)
               (Html.symbol "icloud.and.arrow.down" (.button (restoreLabel b) .plain (if o.restoring then none else some (.cloud (.restore b.id)))))) ++
          (if c.available.isEmpty && !c.busy then [body "No backup found for this network yet."] else []) ++
          [ .button "Check again" .plain (if o.restoring || c.busy then none else some (.cloud .checkAgain)) ])]) ++
     (if o.restoring || c.busy then [.progress (if o.restoring then "Restoring wallet…" else "Checking iCloud…")] else []) ++
     (match o.restoreError with | some e => [caption e] | none => []) ++
     (match c.issue with | some i => [caption i.message] | none => [])) inner (largeTitle := true)

def exportSheet (m : Model) (inner : List H) : H :=
  let e := m.exportState
  formSheet "Backup file" (some .closeSheet) [closeBar "Close"]
    ([ .section "" "Without the recovery phrase the file restores your history but not the ability to spend."
         ([ .identified Ids.exportExplanation (body "Saves a file you can keep in Files or send to yourself. Restore it from Restore from a file.")
          , .toggle "Include recovery phrase" e.includeMnemonic (fun b => .backup (.setIncludeMnemonic b))] ++
          (if e.includeMnemonic then [body "This file includes your phone’s signing key. Keep it as private as your recovery words."] else [])) ] ++
     (match e.error with | some err => [.section "" "" (errorRows (some err))] | none => []) ++
     (match e.file with
      | some file =>
        [.section "Backup ready" ""
          [ body (if e.includeMnemonic then "Includes your recovery words. Keep this file private."
                  else "Recovery words are not included. Keep them separately.")
          , .share "Save or share backup" file (file := true) ]]
      | none => [.section "" "" [.button "Create backup file" .primary (if e.busy then none else some (.backup .createExport))]]))
    inner

/-- Two words per row, numbered, like the reveal grid; nothing but a notice while the screen is recorded or
mirrored (records-test's `backupScreens`). -/
def wordGrid (words : List String) (captured : Bool := false) : H :=
  if captured then
    .row [.icon "record.circle", body "Hidden while the screen is being recorded or mirrored."] else
  let numbered := words.zipIdx.map fun (w, i) => s!"{i + 1}. {w}"
  let rec pairs : List String → List H
    | a :: b :: rest => .row [body a, .spacer, body b] :: pairs rest
    | [a] => [.row [body a]]
    | [] => []
  .col (pairs numbered)

/-- RevealPhraseView: the words and Copy (records-test's `backupScreens`). -/
def revealSheet (m : Model) (inner : List H) : H :=
  formSheet "Recovery phrase" (some .closeSheet) [closeBar "Close"]
    [ .section "" "These words are this phone's signing key. Keep them private. Winnow cannot restore from the words alone; use iCloud backup or a backup file for your history."
         [wordGrid m.reveal.words m.captured]
     , .section "" "Copying is less private than paper. The clipboard item stays on this device and expires after two minutes."
         [.button (if m.reveal.copied then "Copied for 2 minutes" else "Copy recovery phrase") .plain (some (.backup .copyPhrase))] ]
    inner

end WinnowApp
