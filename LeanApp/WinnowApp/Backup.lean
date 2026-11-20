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

/-- A durable acknowledgment is not evidence of a saved recovery copy. -/
def Model.backupPromptKey (m : Model) : String :=
  m.settings.network.name ++ ":" ++ m.walletID.getD ""

/-- Preserve the original Receive action after the optional explanation. -/
def Model.receiveNow (m : Model) : Model × List Cmd :=
  ({ m with receive := ({} : Receive) }.present .receive, [.receiveAddress m.generation false])

def Model.beginReceive (m : Model) : Model × List Cmd :=
  if m.walletID.isNone || m.stage != .ready || !m.sheets.isEmpty then (m, []) else
  if m.cloud.statusTitle == "Backed up" || m.settings.backupPromptShownFor.contains m.backupPromptKey then
    m.receiveNow
  else
    let s := { m.settings with backupPromptShownFor := m.settings.backupPromptShownFor ++ [m.backupPromptKey] }
    ({ m with settings := s }.present .backupIntro, [.saveSettings s])

def stepBackup (msg : BackupMsg) (m : Model) : Model × List Cmd :=
  match msg with
  | .reviewOptions =>
    if !m.hasSheet .backupIntro then (m, []) else
    let (m, cs) := m.closeSheet .backupIntro
    ({ m with routes := m.routes ++ [.backup] }, cs)
  | .receiveWithoutReview =>
    if !m.hasSheet .backupIntro then (m, []) else
    let (m, cs) := m.closeSheet .backupIntro
    let (m, receive) := m.receiveNow
    (m, cs ++ receive)
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
  if c.message == some cloudMissingEntitlementText then "Not available"
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

/-- The visible Home reminder describes iCloud only. Manual exports do not provide a verified
save receipt, and opening or dismissing a backup screen must never mark the wallet backed up. -/
def beginnerBackupSection (m : Model) : H :=
  let c := m.cloud
  let title := if c.statusTitle == "Backed up" then "iCloud backup saved"
    else if c.busy || c.statusTitle == "Backing up" then "iCloud backup in progress"
    else if c.message == some cloudMissingEntitlementText then "iCloud backup unavailable"
    else if !c.automaticEnabled then "iCloud backup is off"
    else "iCloud backup incomplete"
  let subtitle := if c.statusTitle == "Backed up" then
      (c.lastSavedAgo.map fun ago => "Last saved " ++ ago ++ " ago.").getD "Review your backup options."
    else if c.busy || c.statusTitle == "Backing up" then "Keep Winnow open while it saves."
    else "Keep a recovery copy before adding Bitcoin."
  .identified Ids.backupButton
    (Html.decor { callout := true, fullWidth := true, symbol := "icloud", subtitle, accessory := "Review" }
      (.button title .plain (some (.home .openBackup))))

/-- A one-time first-Receive explanation. Continue to Receive continues to Receive; Home retains the status.
The medium sheet can expand to large for Dynamic Type. -/
def backupIntroSheet (m : Model) (inner : List H) : H :=
  .sheet "Backup" (some .closeSheet)
    ([closeBar "Close",
      Html.decor { spacing := 16 } (.col
        [Html.decor { symbol := "key", pointSize := 26 } (.text "Before you move more Bitcoin" .title),
         body "You can receive now. Consider waiting until your iCloud backup is complete before moving a larger balance.",
         Html.callout [Html.decor { pointSize := 15 } (body (if m.cloud.statusTitle == "Backed up" then "iCloud backup is now saved. You can also keep a recovery copy yourself." else "iCloud backup hasn’t completed. A completed backup helps you recover this wallet if you lose your phone."))],
         .identified Ids.backupIntroReview (Html.decor { fullWidth := true } (.button "Review backup options" .primary (some (.backup .reviewOptions)))),
         .identified Ids.backupIntroNotNow (Html.decor { fullWidth := true, underlined := true } (.button "Continue to Receive" .plain (some (.backup .receiveWithoutReview))))])] ++ inner)
    false .medium

/-- CloudBackupView (Settings → Backup → iCloud backup): the switch and the state. -/
def cloudBackupSheet (m : Model) (inner : List H) : H :=
  let c := m.cloud
  .sheet "iCloud backup" (some .closeSheet)
    ([closeBar "Close", Html.decor { spacing := 24 } (.col
      [ Html.callout
          ([.identified Ids.cloudBackupStatus (Html.symbol "icloud" (.text (cloudRowStatus c) .headline))] ++
           (match c.lastSavedText with | some t => [caption ("Last saved to iCloud: " ++ t)] | none => []) ++
           (match c.message with | some t => [body t] | none => []))
      , Html.decor { spacing := 10 } (.col
          [ .identified Ids.automaticCloudBackupToggle (.toggle "Automatic backup" c.automaticEnabled fun b => .cloud (.setAutomatic b))
          , caption "Saves this phone’s key, wallet history, saved people and labels." ])
      , Html.decor { spacing := 8 } (.col
          [ .text "Restoring your wallet" .headline
          , body "Use the same Apple Account, with iCloud and Passwords & Keychain on."
          , .disclosure "How backup and recovery work" (m.isExpanded "backup.details") (Msg.setExpanded "backup.details")
              [body "Updates while Winnow is open, after pending payments confirm. Access to the cloud backup and its synchronized key can restore spending access."] ])
      , Html.decor { spacing := 8 } (.col
          [ .text "Keep another recovery copy" .headline
          , body "Keep a backup file too. Turning backup off leaves existing iCloud copies." ]) ])] ++ inner)

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
             Html.symbol "icloud.and.arrow.down" (.button b.savedAtText .plain (if o.restoring then none else some (.cloud (.restore b.id))))) ++
          (if c.available.isEmpty && !c.busy then [body "No backup found for this network yet."] else []) ++
          [ .button "Check again" .plain (if o.restoring || c.busy then none else some (.cloud .checkAgain)) ])]) ++
     (if o.restoring || c.busy then [.progress (if o.restoring then "Restoring wallet…" else "Checking iCloud…")] else []) ++
     (match o.restoreError with | some e => [caption e] | none => []) ++
     (match c.message with | some t => [caption t] | none => [])) inner (largeTitle := true)

/-- The home's Back up page (its "Save a backup file" while iCloud has not backed up): the Backup section
(records-test's `backupScreens`). -/
def backupScreen (m : Model) (overlays : List H) : H :=
  .screen "Back up" (some (.home .pop)) ([.list [backupSection m]] ++ overlays)

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
    [ .section "" "These words are this phone's signing key. Keep them private. Winnow cannot restore from the words alone; save a backup file for your history."
         [wordGrid m.reveal.words m.captured]
     , .section "" "Copying is less private than paper. The clipboard item stays on this device and expires after two minutes."
         [.button (if m.reveal.copied then "Copied for 2 minutes" else "Copy recovery phrase") .plain (some (.backup .copyPhrase))] ]
    inner

end WinnowApp
