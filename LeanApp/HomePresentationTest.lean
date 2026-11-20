import WinnowApp.View
import LeanNative.Json
import TestKit.Check

/-! Home's presentation must preserve the warning states and actions as cards are restyled/reordered.
These checks dispatch the rendered controls by identifier, including controls inside callouts. -/

open WinnowApp LeanNative TestKit

def home (m : Model) : H := .list (homeSections m)

partial def paths (w : Wire) (id : String) (path : List Nat := []) : List (List Nat) :=
  (if (w.toJson.getObjValAs? String "id").toOption == some id then [path] else []) ++
    w.children.zipIdx.flatMap (fun (child, i) => paths child id (path ++ [i]))

def tap (h : H) (id : String) : Option Msg := do
  let [path] := paths h.toWire id | none
  h.dispatch path .click

def textHas (h : H) (s : String) : Bool := (h.toWire.toJson.compress.splitOn s).length > 1

partial def fullWidthControl (w : Wire) (id : String) : Bool :=
  (((w.toJson.getObjValAs? String "id").toOption == some id) &&
    ((w.toJson.getObjVal? "decor" >>= fun d => d.getObjValAs? Bool "fullWidth").toOption == some true)) ||
    w.children.any (fun c => fullWidthControl c id)

def funded : Model :=
  { stage := .ready, walletID := some "presentation-test", phase := .synced,
    settings := { network := .mainnet }, status := { balance := 13_790_000 } }

def main : IO UInt32 := runMain "home-presentation-test" do
  let recipients := WinnowApp.view { funded with sheets := [.savedRecipients] }
  check "a symbol-decorated action retains its full-width button shape"
    (fullWidthControl recipients.toWire "recipients.add")
  check "the styled Add recipient button still opens the original person form"
    (tap recipients "recipients.add" matches some (.people (.openAdd _ "")))
  let offline := { funded with phase := .peerDiscoveryFailed }
  let h := home offline
  check "offline balance is explicitly last known" (textHas h "Last known balance")
  check "offline retains the separate network and IP exposure warnings"
    (textHas h "Offline" && textHas h "Peers can see your IP when connected.")
  check "network warning opens its explanation"
    (tap h Ids.homeNetworkWarning matches some (.home (.explainWarning .network)))
  check "privacy warning opens its explanation"
    (tap h Ids.peerRoutingBanner matches some (.home (.explainWarning .routing)))
  let (explained, _) := stepHome (.explainWarning .network) offline
  check "network details stay in the founder's alert"
    (textHas (.list (confirms explained)) "Couldn't reach the Bitcoin network")
  let (settings, _) := stepHome (.warningSettings .network) explained
  check "the alert leads to Settings, where Retry still dispatches"
    (settings.routes == [.settings, .network .sync] &&
      (tap (.list (syncSections settings)) Ids.retryPeersButton matches some .retryPeers))
  check "offline Receive is still available" (tap h Ids.receiveButton matches some .openReceive)
  check "offline Send still opens the form; its existing checks own validation"
    (tap h Ids.openSendButton matches some .openSend)
  let actions := paths h.toWire Ids.openSendButton
  let cards := paths h.toWire Ids.hardwareWalletCard
  check "payment actions precede the protection pitch" (match actions, cards with
    | [a], [b] => a.head! < b.head!
    | _, _ => false)
  check "pairing is not described as protecting existing coins"
    (textHas h "Pairing alone does not protect your balance.")
  -- Its primary action lives inside the callout, not on a new/unhandled route.
  check "protection CTA retains its setup action"
    (tap h "home.protect.setup" matches some (.home .protectWithLedger))
  check "dismissal retains the saved permanent-dismiss action"
    (tap h Ids.dismissHardwareCard matches some (.home (.dismissCard true)))
  let (dismissed, commands) := step (.home (.dismissCard true)) offline
  check "dismissal still removes the card and persists settings"
    ((paths (home dismissed).toWire Ids.hardwareWalletCard).isEmpty &&
      commands.any (· matches .saveSettings _))
  let fresh := home funded
  check "synced balance is current and has no retry control"
    (!textHas fresh "Last known balance" && textHas fresh "Up to date" &&
      (paths fresh.toWire Ids.retryPeersButton).isEmpty)
  check "syncing balance is also last known"
    (textHas (home { funded with status := { funded.status with syncing := true } }) "Last known balance")
  let testnet := home { offline with settings := { network := .regtest } }
  check "test coins remain explicit, separately from the connection failure"
    (textHas testnet "test coins" && textHas testnet "Offline" &&
      (paths testnet.toWire Ids.networkTag).length == 1 && (paths testnet.toWire Ids.peerRoutingBanner).isEmpty)
  check "threshold is unchanged below ten million sats"
    ((paths (home { funded with status := { balance := 9_999_999 } }).toWire Ids.hardwareWalletCard).isEmpty)
  check "backup action survives the warning panel"
    (tap h Ids.backupButton matches some (.home .openBackup))

  check "backup reminder is before Receive, protection and Activity"
    (match paths h.toWire Ids.backupButton, paths h.toWire Ids.receiveButton with
      | [a], [b] => a.head! < b.head!
      | _, _ => false)
  check "backup copy identifies iCloud without claiming a manual backup is missing"
    (textHas h "iCloud backup incomplete" && !textHas h "Not backed up")
  let (prompted, promptCommands) := step .openReceive funded
  check "first Receive presents one optional backup sheet and persists only that it was shown"
    (prompted.topSheet == some .backupIntro && promptCommands.any (· matches .saveSettings _) &&
     !promptCommands.any (· matches .receiveAddress ..) && prompted.cloud.statusTitle == funded.cloud.statusTitle)
  let (later, laterCommands) := step (.backup .receiveWithoutReview) prompted
  check "Not now continues to the original Receive flow"
    (later.topSheet == some .receive && laterCommands.any (· matches .receiveAddress _ false))
  check "Not now leaves the Home reminder visible"
    (tap (home later) Ids.backupButton matches some (.home .openBackup))
  let (closed, _) := step .closeSheet later
  let (again, _) := step .openReceive closed
  check "later Receive does not repeatedly interrupt the same wallet" (again.topSheet == some .receive)
  let restoredSettings := (Lean.fromJson? (Lean.toJson prompted.settings) : Except String Settings).toOption.getD {}
  let (relaunched, _) := step .openReceive { funded with settings := restoredSettings }
  check "the one-time acknowledgment survives a settings round trip" (relaunched.topSheet == some .receive)
  let (newWallet, _) := step .openReceive { funded with settings := restoredSettings, walletID := some "different-wallet" }
  check "a different wallet gets its own backup explanation" (newWallet.topSheet == some .backupIntro)
  let (otherNetwork, _) := step .openReceive { funded with settings := { restoredSettings with network := .signet } }
  check "the acknowledgment is network-scoped" (otherNetwork.topSheet == some .backupIntro)
  let (reviewing, reviewCommands) := step (.backup .reviewOptions) prompted
  check "Review opens actual backup options without marking backup complete"
    (reviewing.topSheet.isNone && reviewing.routes == [.backup] && reviewing.cloud.statusTitle == prompted.cloud.statusTitle &&
     !reviewCommands.any (· matches .receiveAddress ..))
  let (saved, _) := step .openReceive { funded with cloud := { statusTitle := "Backed up", lastSavedText := some "Today" } }
  check "successful iCloud backup skips the introductory prompt" (saved.topSheet == some .receive)
  let (swiped, _) := step .closeSheet prompted
  check "swiping the sheet away leaves backup review reachable"
    (swiped.sheets.isEmpty && (tap (home swiped) Ids.backupButton matches some (.home .openBackup)))
  check "legacy settings default to an unshown prompt"
    (((Lean.fromJson? (Lean.Json.mkObj []) : Except String Settings).toOption.getD {}).backupPromptShownFor.isEmpty)

  -- Current main's safeguards must survive the design overlay.
  let account : MultisigInfo :=
    { id := "segwit-test", name := "Shared", descriptor := "preview",
      balance := 0, policy := some "2 of 3", buildsPayments := false }
  let shared := { funded with multisig := { accounts := [account] }, routes := [.multisigAccount account.id] }
  let sharedView := WinnowApp.view shared
  check "SegWit co-signer accounts retain the founder's no-Send guidance"
    ((paths sharedView.toWire Ids.multisigSendButton).isEmpty &&
     textHas sharedView "Payments from this account are made by whoever holds its fixed key")
  check "SegWit PSBT action still routes to the current account"
    (tap sharedView Ids.multisigPastePSBTButton matches some (.multisig (.pasteForAccount "segwit-test")))
  let (refused, refusedCommands) := step (.multisig (.sendFrom account.id)) shared
  check "a stale Send action cannot bypass the SegWit account restriction"
    (refused.sheets.isEmpty && refusedCommands.isEmpty)
  let damaged := { funded with routes := [.multisigAccounts], multisig := { notice := some "Damaged file" } }
  check "damaged account data retains its explicit recovery action"
    (tap (WinnowApp.view damaged) Ids.multisigSetAsideButton matches some (.multisig .askSetAside))
  let (ask, _) := step (.multisig .askSetAside) damaged
  check "setting data aside still requires the founder's confirmation"
    (ask.confirm == some .setAsideMultisig && textHas (WinnowApp.view ask) "The file is kept on this phone")
  let (_, unconfirmedCommands) := step (.multisig .setAside) damaged
  check "the design cannot bypass damaged-file confirmation" unconfirmedCommands.isEmpty
  check "export authentication cancellation returns to a usable export sheet"
    (!(Model.fail { funded with exportState := { busy := true } } "export.cancelled" "cancelled").exportState.busy)

  -- Controls remain dispatchable after replacing automatic table sections with columns.
  let networkView := WinnowApp.view { funded with routes := [.network .peers] }
  check "routing controls retain their actions in the compact layout"
    (tap networkView Ids.applyPeerRouting matches some (.settings .applyGateways))
  check "direct-connection privacy warning stays visible"
    (textHas networkView "Direct peers can see your IP address.")
  check "account member picker survives the new form layout"
    (tap (WinnowApp.view { funded with routes := [.multisigBuild] }) Ids.multisigBuildAddMemberButton
      matches some (.multisig (.openPicker none)))

  let sending := { funded with sheets := [.send], multisig := { accounts := [{ account with buildsPayments := true }] } }
  let sendView := WinnowApp.view sending
  check "empty Send keeps review disabled in the new form"
    (tap sendView Ids.reviewButton).isNone
  check "destination paste retains its original action"
    (tap sendView Ids.pasteDestinationButton matches some (.send .pasteDestination))

  check "wallet selection remains actionable across the full card"
    (tap sendView Ids.sendFromWallet matches some (.send (.setSource none)))
  check "account selection retains the account identifier"
    (tap sendView (Ids.sendFrom account.id) matches some (.send (.setSource (some "segwit-test"))))

  -- The existing address and QR must be visible on first open. Check actions and safeguards.
  let detailAccount : MultisigInfo :=
    { id := "detail-test", name := "Shared protection", descriptor := "preview", balance := 5_000_000,
      policy := some "2 of 3 members", buildsPayments := true, ledgerFingerprint := some "preview",
      memberLines := ["Phone + Ledger (both required)", "Trustee", "Provider"],
      recovery := some "After 4,320 blocks: recovery key", receiveAddress := some "PREVIEW-ADDRESS" }
  let detail := { funded with routes := [.multisigAccount detailAccount.id], multisig := { accounts := [detailAccount] } }
  let detailView := WinnowApp.view detail
  check "account opens with its recovery rule and receive address visible"
    (textHas detailView "4,320 blocks" && !(paths detailView.toWire Ids.multisigReceiveAddress).isEmpty)
  check "receive keeps original address verification guidance and Ledger action"
    (textHas detailView "check it there before sharing it" &&
      (tap detailView Ids.ledgerVerifyButton matches some (.multisig .verifyAddress)))
  check "new account address retains its original action"
    (tap detailView Ids.multisigNewAddressButton matches some (.multisig .newAddress))
  let verifying := WinnowApp.view { detail with ledgerVerify := { id := detailAccount.id, index := 0, checking := true } }
  check "a Ledger verification in progress cannot be started twice"
    ((tap verifying Ids.ledgerVerifyButton).isNone && textHas verifying "Check the Ledger")
  check "account Send still selects this account"
    (tap detailView Ids.multisigSendButton matches some (.multisig (.sendFrom "detail-test")))
  let draftView := WinnowApp.view { detail with multisig := { accounts := [{ detailAccount with draft := some { psbt := "preview", txid := "preview" } }] } }
  check "an existing draft replaces Send with its signatures route"
    ((paths draftView.toWire Ids.multisigSendButton).isEmpty &&
      (tap draftView Ids.multisigDraftButton matches some (.multisig (.openPSBT "detail-test"))))
  let missing := WinnowApp.view { detail with multisig := { accounts := [{ detailAccount with receiveAddress := none }] } }
  check "missing receive address shows its state and keeps Send usable"
    (textHas missing "Receive address unavailable" &&
      (tap missing Ids.multisigSendButton matches some (.multisig (.sendFrom "detail-test"))))
  let setup := WinnowApp.view { funded with sheets := [.ledgerNearby], ledgerSetup := some {} }
  check "hardware setup keeps its actual creation action"
    (tap setup Ids.ledgerSetupStartButton matches some (.ledgerCard .start))
  check "hardware setup accurately distinguishes the optional third key"
    (textHas setup "Both required" && textHas (WinnowApp.view { funded with sheets := [.ledgerNearby], ledgerSetup := some { withRecoveryKey := true } }) "Any two of this phone")
