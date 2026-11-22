import LeanNative.Html
import WinnowApp.Model
import WinnowApp.Pure

/-! What every area shares: routing a failure to the screen that asked, closing sheets (each sheet
forgets its state, sensitive ones bump the epoch), and the small view pieces Winnow's Components.swift
provides (copyable identifiers and text blocks, warned explorer links, technical disclosures). -/

namespace WinnowApp
open LeanNative

abbrev H := Html Msg

/-- The staged file goes whenever the export is reset (`staging.remove()`): toggling the phrase, closing the
sheet, a new export, the app leaving the foreground. -/
def Model.discardExport (m : Model) : List Cmd :=
  match m.exportState.file with
  | some f => [.removeExport f]
  | none => []

def caption (s : String) : H := .text s .caption
def body (s : String) : H := .text s .body
/-- A warning, wherever the app shows one: a filled symbol in the warning colour beside its text at body
size in the label colour. Small grey text beside an untinted symbol read as a footnote. -/
def warningRow (text : String) (icon : String := "exclamationmark.triangle.fill") (tone : LeanNative.Tone := .warning) : H :=
  .row [Html.tone tone (.icon icon), body text]
def errorRows : Option String → List H
  | some e => [warningRow e]
  | none => []
/-- An address, a txid, a key: monospaced small text, wrapped at any character. -/
def literal (s : String) : H := Html.mono (caption s)

/-! ## Failures -/

/-- Failures for wallet lifecycle and sync operations. -/
def Model.failWallet (m : Model) (target : WalletFail) (cancelled : Bool) (message : String) : Model :=
  match target with
  | .create | .importWallet =>
    { m with onboarding := { m.onboarding with busy := false, error := if cancelled then none else some message } }
  | .cloudRestore =>
    if cancelled then { m with onboarding := { m.onboarding with restoring := false } }
    else { m with onboarding := { m.onboarding with restoring := false, restoreError := some message } }
  | .openWallet =>
    -- the wallet could not be opened at all: the screen that says so has Retry, where "Opening wallet…" has none
    if m.stage == .loading then { m with stage := .storageDamaged message }
    else { m with status := { m.status with lastSyncError := some message } }
  | .delete => { m with confirm := some (.deleteFailed message) }
  | .unlock => if cancelled then m else { m with status := { m.status with lastSyncError := some message } }
  | .sync => { m with status := { m.status with lastSyncError := some message } }

/-- Failures for receiving, sending, payment details, and fee bumps. -/
def Model.failPayment (m : Model) (target : PaymentFail) (message : String) : Model :=
  match target with
  | .receive => { m with receive := { m.receive with error := some message, changing := false } }
  | .label => { m with labelEditor := { m.labelEditor with saving := false, error := some message } }
  | .send => { m with send := { m.send with error := some message, reviewing := false, sending := false }, spendingInFlight := false }
  | .rate => { m with send := { m.send with resolvedRateMilli := none } }
  | .payment => { m with payment := { loading := false, error := some message } }
  | .feeBump => { m with feeBump := { m.feeBump with error := some message, bumping := false }, spendingInFlight := false }

/-- Failures for Settings and manual backup screens. -/
def Model.failSettings (m : Model) (target : SettingsFail) (cancelled : Bool) (message : String) : Model :=
  match target with
  | .peers => { m with settingsDraft := { m.settingsDraft with error := some message, resettingPeers := false } }
  -- the census line is read from the shipped list; a failure leaves it unset
  | .catalog => m
  | .exportBundle =>
    if cancelled then { m with exportState := { m.exportState with busy := false, error := none } }
    else { m with exportState := { m.exportState with busy := false, error := some message, file := none } }
  | .reveal => { m with reveal := { m.reveal with revealing := false, error := if cancelled then none else some message } }

/-- Failures for people and person cards. -/
def Model.failPeople (m : Model) (target : PeopleFail) (cancelled : Bool) (message : String) : Model :=
  match target with
  | .personCard =>
    if cancelled then { m with shareCard := { m.shareCard with making := false } }
    else { m with shareCard := { m.shareCard with making := false, error := some message } }
  | .person => { m with person := { m.person with saving := false, inferring := false, error := some message } }
  | .recipients => { m with recipientsError := some message }

/-- Failures for multisig accounts, signers, Ledger pairing, and signature collection. -/
def Model.failMultisig (m : Model) (target : MultisigFail) (cancelled : Bool) (message : String) : Model :=
  match target with
  -- the overview keeps what it last showed
  | .overview => m
  | .add => { m with multisigAdd := { m.multisigAdd with saving := false, error := some message } }
  | .build => { m with multisigBuild := { m.multisigBuild with creating := false, error := some message } }
  | .account => { m with multisigAccountError := some message }
  | .spend => { m with payment := { m.payment with error := some message } }
  | .ledgerPair => { m with ledgerPair := { m.ledgerPair with pairing := false, error := some message } }
  | .signerKeys => { m with signerKeys := { m.signerKeys with saving := false, error := some message } }
  | .signer => { m with signerDetail := { m.signerDetail with error := some message } }
  | .collect epoch =>
    -- the collection step's `run`: only the current operation's failure shows (`accepts(token)`)
    let m := { m with spendingInFlight := false }
    if epoch != m.collect.epoch || !m.active then m
    else { m with collect := { m.collect with busy := false, error := if cancelled then none else some message } }

/-- Route a backend failure to the state of the screen that asked (`target`), clearing that screen's busy
flags (records-test's `failuresReachTheirScreens`, one case per target; the journey `spentElsewhere` signs a
review whose coin has gone). -/
def Model.fail (m : Model) (target : FailTarget) (cancelled : Bool := false) (message : String) : Model :=
  match target with
  | .wallet t => m.failWallet t cancelled message
  | .payment t => m.failPayment t message
  | .settings t => m.failSettings t cancelled message
  | .people t => m.failPeople t cancelled message
  | .multisig t => m.failMultisig t cancelled message

/-! ## Sheets -/

/-- Forget what a sheet held when it goes away (the SwiftUI view's @State dies with it). -/
def Model.forgetSheet (m : Model) : Sheet → Model × List Cmd
  | .receive => ({ m with receive := {}, labelEditor := {}, shareCard := {} }, [.stopWatchingAddress])
  | .send => ({ m with send := {}, expanded := ((m.expanded.erase "send.details").erase "send.fee").erase "send.review" }, [])
  | .feeBump => ({ m with feeBump := {} }, [])
  | .addPerson => ({ m with person := {} }, [])
  | .labelEditor => ({ m with labelEditor := {} }, [])
  | .exportBundle => ({ m with exportState := {}, epoch := m.epoch + 1 }, m.discardExport)
  | .revealPhrase => ({ m with reveal := {}, epoch := m.epoch + 1 }, [])
  | .papers => ({ m with paper := none }, [])
  | .shareCard => ({ m with shareCard := {} }, [])
  | .savedRecipients => ({ m with recipientsError := none }, [])
  | .importWallet => ({ m with onboarding := { m.onboarding with importText := "", importReport := none } }, [])
  | .signerPicker => ({ m with multisigBuild := { m.multisigBuild with pickInto := none, pasteError := none } }, [])
  -- CloudRestoreView's `onDisappear`: `cancel()` (the controller's operations end)
  | .cloudRestore => ({ m with onboarding := { m.onboarding with restoring := false, restoreError := none } }, [.suspendCloud])
  | .cloudBackup | .readSide | .bluetoothIntro | .wallets => (m, [])
  | .renameWallet => ({ m with renameDraft := "", renameBusy := false, renameError := none }, [])
  -- the nearby card: a setup left (Not now, or after a failure) starts again from its first step
  | .ledgerNearby => ({ m with ledgerSetup := none }, [])

/-- Close the sheets from index `i` up (an outer sheet takes the ones it presented with it). -/
def Model.closeFrom (m : Model) (i : Nat) : Model × List Cmd :=
  let closing := m.sheets.drop i
  let m0 := { m with sheets := m.sheets.take i, confirm := none }
  closing.reverse.foldl (fun (acc : Model × List Cmd) s =>
    let (m', cs) := acc.1.forgetSheet s
    (m', acc.2 ++ cs)) (m0, [])

/-- Close `s` (and whatever it presented). -/
def Model.closeSheet (m : Model) (s : Sheet) : Model × List Cmd :=
  match m.sheets.idxOf? s with
  | some i => m.closeFrom i
  | none => (m, [])

def Model.closeTop (m : Model) : Model × List Cmd :=
  if m.sheets.isEmpty then (m, []) else m.closeFrom (m.sheets.length - 1)

/-- Sheets that never survive a background transition (BackupSection, ExportBundleView,
RevealPhraseView, the onboarding import sheet); records-test's `backupScreens` backgrounds each of them, and
the iCloud backup sheet, which stays. -/
def Sheet.isSensitive : Sheet → Bool
  | .importWallet | .exportBundle | .revealPhrase => true
  | _ => false

/-! ## View pieces (Components.swift) -/

/-- `h` with a UI-test identifier (`Html.identified`); none when `id` is empty. -/
def withId (id : String) (h : H) : H := if id.isEmpty then h else .identified id h

/-- `CopyableIdentifier`: shown short when asked, copied whole; "Copied" for two seconds. -/
def copyableIdentifier (m : Model) (key value : String) (abbreviated := false) (label := "Copy") : H :=
  let shown := if abbreviated && value.length > 20 then String.ofList (value.toList.take 16) ++ "…" else value
  .row [literal shown, .spacer, .button (if m.copied == some key then "Copied" else label) .plain (some (.copy key value))]

/-- `CopyableTextBlock`: the text (`id` its UI-test identifier), Copy and Share. -/
def copyableBlock (m : Model) (key text : String) (id := "") : H :=
  .col [withId id (literal text),
        .row [.button (if m.copied == some key then "Copied" else "Copy") .plain (some (.copy key text)), .share "Share" text]]

/-- `WarnedExplorerLink`: the warning comes before anything is opened. -/
def explorerButton (title url exposedItem : String) : H :=
  Html.symbol "safari" (.button title .plain (some (.openExplorer url exposedItem)))

/-- A raw address or id, folded behind a title. -/
def technical (m : Model) (key title : String) (content : List H) : List H :=
  [.disclosure title (m.isExpanded key) (Msg.setExpanded key) content]

/-- A sheet's own close control (SwiftUI's cancellation toolbar item): the system Close button at the
navigation bar's leading end, `label` what VoiceOver says, `id` its UI-test identifier. -/
def closeBar (label : String) (id : String := "") : H :=
  .toolbar [withId id (.button label .cancel (some .closeSheet))] .cancel

/-- A sheet as SwiftUI's `NavigationStack { Form { … } }`: its toolbars, its content as one grouped list
(sections, and any other node as a row of its own), then what it presents (`inner`). -/
def formSheet (title : String) (onDismiss : Option Msg) (bar content inner : List H) (largeTitle := false)
    (size : SheetSize := .large) : H :=
  .sheet title onDismiss (bar ++ [.list content] ++ inner) largeTitle size

/-- A button that opens a screen or a sheet (a `NavigationLink`): in a list its row is the link, with a
disclosure chevron. -/
def navLink (label : String) (action : Option Msg) (symbol := "") : H :=
  Html.decor { chevron := true, symbol } (.button label .plain action)

end WinnowApp
