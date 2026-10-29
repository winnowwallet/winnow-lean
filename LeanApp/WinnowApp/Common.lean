import ElmLean.Html
import WinnowApp.Model
import WinnowApp.Pure

/-! What every area shares: routing a failure to the screen that asked, closing sheets (each sheet
forgets its state, sensitive ones bump the epoch), and the small view pieces Winnow's Components.swift
provides (copyable identifiers and text blocks, warned explorer links, technical disclosures). -/

namespace WinnowApp
open ElmLean

abbrev H := Html Msg

/-- The staged file goes whenever the export is reset (`staging.remove()`): toggling the phrase, closing the
sheet, a new export, the app leaving the foreground. -/
def Model.discardExport (m : Model) : List Cmd :=
  match m.exportState.file with
  | some f => [.removeExport f]
  | none => []

def caption (s : String) : H := .text s .caption
def body (s : String) : H := .text s .body
def errorRows : Option String → List H
  | some e => [.row [Html.tone .warning (.icon "exclamationmark.triangle"), body e]]
  | none => []
/-- An address, a txid, a key: monospaced small text, wrapped at any character. -/
def literal (s : String) : H := Html.mono (caption s)

/-! ## Failures -/

/-- Route a backend failure to the state of the screen that asked (`context`). -/
def Model.fail (m : Model) (context message : String) : Model :=
  -- a cancelled authentication prompt: revealing the phrase treats it as a decision (no error)
  if context == "create.cancelled" || context == "import.cancelled" then { m with onboarding := { m.onboarding with busy := false, error := none } } else
  -- a declined prompt or a cancelled restore says nothing (`catch is CancellationError { }`)
  if context == "cloudRestore.cancelled" then { m with onboarding := { m.onboarding with restoring := false } } else
  if context == "cloudRestore" then
    let shown := if message == "Winnow.CancellationError" then none else some message
    { m with onboarding := { m.onboarding with restoring := false, restoreError := shown } } else
  if context == "reveal.cancelled" then { m with reveal := { m.reveal with revealing := false, error := none } } else
  let cancelled := context.endsWith ".cancelled"
  let context := if cancelled then (context.dropEnd 10).copy else context
  if context.startsWith "collect." then
    -- the collection step's `run`: only the current operation's failure shows (`accepts(token)`)
    let m := { m with spendingInFlight := false }
    if (context.drop 8).toString.toNat? != some m.collect.epoch || !m.active then m else
    { m with collect := { m.collect with busy := false, error := if cancelled then none else some message } }
  else
  match context with
  | "onboarding" | "create" | "import" => { m with onboarding := { m.onboarding with busy := false, error := some message } }
  | "receive" => { m with receive := { m.receive with error := some message, changing := false } }
  | "label" => { m with labelEditor := { m.labelEditor with saving := false, error := some message } }
  | "send" => { m with send := { m.send with error := some message, reviewing := false, sending := false }, spendingInFlight := false }
  | "rate" => { m with send := { m.send with resolvedRateMilli := none } }
  | "settings" | "peers" => { m with settingsDraft := { m.settingsDraft with error := some message, resettingPeers := false } }
  | "delete" => { m with confirm := some (.deleteFailed message) }
  -- the census line is read from the shipped list; a failure leaves it unset
  | "catalog" => m
  | "payment" => { m with payment := { loading := false, error := some message } }
  | "feeBump" => { m with feeBump := { m.feeBump with error := some message, bumping := false }, spendingInFlight := false }
  | "export" => { m with exportState := { m.exportState with busy := false, error := some message, file := none } }
  | "reveal" => { m with reveal := { m.reveal with revealing := false, error := some message } }
  | "card" => { m with shareCard := { card := none, error := some message } }
  | "person" => { m with person := { m.person with saving := false, inferring := false, error := some message } }
  | "recipients" => { m with recipientsError := some message }
  | "multisigAdd" => { m with multisigAdd := { m.multisigAdd with saving := false, error := some message } }
  | "multisigBuild" => { m with multisigBuild := { m.multisigBuild with creating := false, error := some message } }
  | "multisigAccount" => { m with multisigAccountError := some message }
  | "accountSpend" => { m with payment := { m.payment with error := some message } }
  | "ledgerPair" => { m with ledgerPair := { m.ledgerPair with pairing := false, error := some message } }
  | "signerKeys" => { m with signerKeys := { m.signerKeys with saving := false, error := some message } }
  | "signer" => { m with signerDetail := { m.signerDetail with error := some message } }
  -- the overview keeps what it last showed
  | "multisigOverview" => m
  | _ => { m with status := { m.status with lastSyncError := some message } }

/-! ## Sheets -/

/-- Forget what a sheet held when it goes away (the SwiftUI view's @State dies with it). -/
def Model.forgetSheet (m : Model) : Sheet → Model × List Cmd
  | .receive => ({ m with receive := {}, labelEditor := {} }, [.stopWatchingAddress])
  | .send => ({ m with send := {} }, [])
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
  | .cloudBackup | .readSide => (m, [])

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
RevealPhraseView, the onboarding import sheet). -/
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

/-- A raw address or id: in full for Advanced mode, folded behind a title for a beginner. -/
def technical (m : Model) (key title : String) (content : List H) : List H :=
  if m.settings.advancedMode then content
  else [.disclosure title (m.isExpanded key) (Msg.setExpanded key) content]

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
