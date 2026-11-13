import WinnowApp.Update
import WinnowApp.Ids

/-! The root view (WinnowApp.swift: loading, onboarding, ready as the one home,
StorageDamagedView, the Tor alert), the onboarding screen and sheets, and the presentation stack: each
sheet presents the next one inside itself, and the one alert in the tree goes on the innermost sheet
(an alert behind a sheet never shows). Each area's screens are in its own module. -/

namespace WinnowApp
open LeanNative

/-! ## Onboarding -/

/-- Restore from a file: paste a backup file, import it, the verification report (records-test's
`backupScreens`). -/
def importSheet (m : Model) (inner : List H) : H :=
  formSheet "Import wallet" (some .closeSheet) [closeBar "Close"]
    ([ .section "Backup file" "Use a backup file saved from Winnow (Save a backup file). Keep your recovery words too. Backups from other wallets may not include every coin type."
         [ .input .multiline "" "Paste your backup file (JSON)" m.onboarding.importText Msg.setImportText none
         , Html.symbol "doc.on.clipboard" (.button "Paste from clipboard" .plain (some .pasteImport)) ] ] ++
     (match m.onboarding.importReport with
      | some r => [.identified Ids.importReportSection (.section "Verification report" "" [body r]),
                   .section "" "" [.identified Ids.importContinueButton (.button "Continue" .primary (some .finishOnboarding))]]
      | none => [.section "" "" [.identified Ids.importVerifyButton (.button "Import and verify" .primary
                  (if m.onboarding.busy || m.onboarding.importText.trimAscii.isEmpty then none else some .importWallet))]]) ++
     (if m.onboarding.busy then [.progress "Importing and verifying…"] else []) ++
     errorRows m.onboarding.error) inner (largeTitle := true)

/-! ## Presentations -/

def sheetView (m : Model) (s : Sheet) (inner : List H) : H :=
  match s with
  | .receive => receiveSheet m inner
  | .send => sendSheet m inner
  | .cloudRestore => cloudRestoreSheet m inner
  | .cloudBackup => cloudBackupSheet m inner
  | .importWallet => importSheet m inner
  | .feeBump => feeBumpSheet m inner
  | .addPerson => addPersonSheet m inner
  | .savedRecipients => savedRecipientsSheet m inner
  | .shareCard => shareCardSheet m inner
  | .labelEditor => labelSheet m inner
  | .exportBundle => exportSheet m inner
  | .revealPhrase => revealSheet m inner
  | .papers => papersSheet m inner
  | .readSide => readSideSheet inner
  | .signerPicker => signerPickerSheet m inner
  | .ledgerNearby => ledgerNearbySheet m inner
  | .bluetoothIntro => bluetoothIntroSheet inner

def cancel : H := .button "Cancel" .cancel (some .dismissConfirm)

def confirms (m : Model) : List H :=
  match m.confirm with
  | some (.homeWarning .network) =>
    [.alert (if m.phase.summary m.status.syncing == .peersUnavailable then "Couldn't reach the Bitcoin network" else "Sync problem")
       (networkWarningMessage m)
       [.identified Ids.warningSettingsButton (.button "Network settings" .primary (some (.home (.warningSettings .network)))),
        .button "OK" .cancel (some .dismissConfirm)]]
  | some (.homeWarning .routing) =>
    let state := PeerRoutingState.current m.settings.peerGatewaySettings.mode m.status.activeGateways m.status.discoveringGateways
    [.alert state.alertTitle state.message
       [.identified Ids.warningSettingsButton (.button "Peers and routing" .primary (some (.home (.warningSettings .routing)))),
        .button "OK" .cancel (some .dismissConfirm)]]
  | some .deleteWallet =>
    [.alert "Delete this wallet?" "This deletes the key from this device. Winnow can restore it from your iCloud backup or from a backup file that includes the recovery phrase. Without one of those or the phrase itself, any money in this wallet is unrecoverable. Check you have one before continuing."
       [.button "Delete wallet" .destructive (some (.settings .deleteWallet)), cancel]]
  | some (.deleteFailed msg) =>
    [.alert "Could not delete the wallet" msg [.button "OK" .plain (some .dismissConfirm)]]
  | some .resetPeers =>
    [.alert "Reset and shuffle peers?" "Disconnects all peers, forgets saved peers, and finds new ones from the peer list this version ships with and, when clearnet is allowed, DNS seeds. Your manual peers and the shipped peer list are kept."
       [.button "Reset and shuffle peers" .destructive (some (.settings .resetPeers)), cancel] .actionSheet]
  | some .exportWithPhrase =>
    [.alert "Include the recovery phrase?" "This adds your phone's signing key to the file. Anyone with the file can use that key."
       [.button "Export with phrase" .destructive (some (.backup .confirmExport)), cancel]]
  | some .inferSender =>
    let host := match m.person.lookupConsent with
      | some (base, _) => (urlHost base).getD "the explorer"
      | none => m.settings.explorerHost
    [.alert s!"Look up funding addresses with {host}?"
       ((if m.person.lookupConsent.isSome then lookupDisclosure else "No lookup selected.") ++ " Funding addresses do not establish who sent the payment or where they want a payment sent.")
       [.button s!"Look up with {host}" .plain (some (.people .infer)), cancel]]
  | some (.discardDraft _) =>
    [.alert "Discard this payment?" "The account keeps its coins. The signatures collected so far are lost."
       [.identified Ids.multisigConfirmDiscardButton (.button "Discard" .destructive (some (.multisig .discard))), cancel] .actionSheet]
  | some (.abandonSpend _ _) =>
    [.alert "Give up on this payment?" "Its coins become the account's again. If the network confirms it after all, it shows up here again as a spend."
       [.identified Ids.abandonConfirmButton (.button "Give up" .destructive (some (.multisig .abandon))), cancel] .actionSheet]
  | some .setAsideMultisig =>
    [.alert "Set the damaged file aside?"
       "The file is kept on this phone under another name and Winnow starts again with no multisig accounts, so the wallet can sync. Join each account again from its descriptor: Winnow finds its coins from then on, not ones it already held. The other signers keep theirs."
       [.identified Ids.multisigSetAsideConfirmButton (.button "Set aside" .destructive (some (.multisig .setAside))), cancel] .actionSheet]
  | some (.removeMultisig _) =>
    [.alert "Remove this account from this phone?" "Only an empty account can be removed. The other signers keep theirs."
       [.button "Remove" .destructive (some (.multisig .remove)), cancel] .actionSheet]
  | some (.openExternal url exposed) =>
    let host := urlHost url
    [.alert "Open external block explorer?"
       s!"Opening {host.getD "this explorer"} opens an external browser, which shares its IP address and this exact {exposed} with that service. Winnow does not use its response for wallet balance, history, fees, synchronization, or broadcasting."
       [.button s!"Open {host.getD "explorer"}" .plain (some (.openURL url)), cancel]]
  | none =>
    if m.settings.torRemovedNotice then
      [.alert "Built-in Tor was removed" "Your old built-in Tor setting no longer applies. Automatic routing uses your Tor and I2P gateways on Tailscale when they answer, and connects directly when none do. To require Tor, open Settings → Network → Peers and routing, choose Manual gateway routing, and select only Tor peers with your gateway address."
         [.button "OK" .plain (some (.settings .dismissTor))]]
    else []

/-- The presentation stack, outermost first; the alert goes on the innermost sheet. -/
def nestSheets (m : Model) : List Sheet → List H
  | [] => confirms m
  | s :: rest => [sheetView m s (nestSheets m rest)]

def overlays (m : Model) : List H := nestSheets m m.sheets

/-! ## Screens -/

/-- OnboardingView: create or restore a wallet without a phrase checklist. Looking for iCloud backups is
automatic, and neither it nor the backup blocks using the wallet. -/
def onboardingView (m : Model) : H :=
  let o := m.onboarding
  let c := m.cloud
  let act (msg : Msg) : Option Msg := if o.busy then none else some msg
  .screen "Winnow" none
    ([ .list
        ([ .section "" "" [Html.tone .secondary (body "Your bitcoin, on your phone. Winnow connects directly to Bitcoin and automatically backs up your wallet with iCloud when available.")]
         , .section "" "No iCloud? Your wallet still works. You can save a backup file instead. Recovery words and backup controls are in Settings → Backup."
             (match m.walletID with
              | some _ =>
                [ .identified Ids.resumeImportedWalletButton (Html.symbol "arrow.right.circle" (.button "Continue with your wallet" .primary (act .finishOnboarding))) ]
              | none =>
                (if c.available.isEmpty then [] else
                  [ .identified Ids.restoreCloudBackupButton (Html.symbol "icloud.and.arrow.down" (.button "Restore your iCloud wallet" .primary (act (.cloud .openRestore))))
                  , caption s!"{c.available.length} saved backup(s) found." ]) ++
                [ .identified Ids.createWalletButton (Html.symbol "plus.circle" (.button "Create new wallet" .primary (act .createWallet)))
                , .identified Ids.importWalletButton (Html.symbol "square.and.arrow.down" (.button "Restore from a file" .plain (act .openImport))) ]) ] ++
         (if c.busy then [.section "" "" [.progress "Checking iCloud…"]] else []) ++
         (match c.message with | some t => [.section "" "" [caption t]] | none => []) ++
         -- mainnet unless asked: the picker is folded behind "Use a test network" (open on a test network)
         [.section "" (if m.settings.network == .mainnet && !m.isExpanded "onboarding.network" then "" else "Each network has its own wallet. Signet uses test coins with no value.")
           [.identified Ids.onboardingTestNetwork
             (.disclosure "Use a test network" (m.settings.network != .mainnet || m.isExpanded "onboarding.network") (Msg.setExpanded "onboarding.network")
               [.identified Ids.onboardingNetworkPicker
                 (if o.busy then .labeled "Network" m.settings.network.label else networkPicker m)])]] ++
         (if o.busy then [.section "" "" [.progress "Creating your wallet…"]] else []) ++
         (match o.error with | some e => [.section "" "" (errorRows (some e))] | none => [])) ] ++ overlays m)

/-- The screen pushed on top of the home, if any. -/
def routedScreen (m : Model) : Option H :=
  (routedScreen' m).map fun
    | .screen t b cs r lt _ => .screen t b cs r lt m.routes.length
    | h => h
where routedScreen' (m : Model) : Option H :=
  match m.routes.getLast? with
  | some (.payment t) => some (.screen "Payment" (some (.home .pop)) ([.list (paymentSections m t)] ++ overlays m))
  | some .backup => some (backupScreen m (overlays m))
  | some .settings => some (.screen "Settings" (some (.home .pop)) ([.list (settingsSections m)] ++ overlays m))
  | some (.network .sync) =>
    some (.screen "Sync" (some (.home .pop)) ([.list (syncSections m)] ++ overlays m) (onRefresh := some .syncNow))
  | some (.network .peers) => some (.screen "Peers and routing" (some (.home .pop)) ([.list (peersSections m)] ++ overlays m))
  | some (.network .explorer) => some (.screen "Block explorer" (some (.home .pop)) ([.list (explorerSections m)] ++ overlays m))
  | some (.network .verification) =>
    some (.screen "Chain verification" (some (.home .pop)) ([.list (verificationSections m)] ++ overlays m))
  | some .multisigAccounts => some (.screen "Multisig accounts" (some (.home .pop)) ([.list [multisigSection m]] ++ overlays m))
  | some .multisigAdd => some (multisigAddScreen m (overlays m))
  | some .ledgerPair =>
    some (.screen "Pair a Ledger" (some (.signer .pop)) ([.list (ledgerPairSections m)] ++ overlays m))
  | some .multisigBuild =>
    some (.screen "Create an account" (some (.multisig .pop)) ([.list (multisigBuildSections m)] ++ overlays m))
  | some (.multisigAccount id) =>
    some (.screen ((m.multisigInfo? id).map (·.name) |>.getD "Multisig") (some (.multisig .pop))
      ([.list (multisigAccountSections m id)] ++ overlays m))
  | some (.multisigPSBT id) =>
    some (.screen (multisigPSBTTitle m id) (some (.multisig .pop)) ([.list (multisigPSBTSections m id)] ++ overlays m))
  | some .signers => some (.screen "Signers" (some (.signer .pop)) ([.list (signersSections m)] ++ overlays m))
  | some (.signer id) =>
    some (.screen ((m.signer? id).map (·.name) |>.getD "Signer") (some (.signer .pop))
      ([.list (signerDetailSections m id)] ++ overlays m))
  | some .signerKeysAdd => some (signerKeysScreen m (overlays m))
  | none => none

/-- The home (pull to refresh: `syncNow`), or the screen pushed on top of it. -/
def mainScreen (m : Model) : H :=
  match routedScreen m with
  | some screen => screen
  | none =>
    .screen "Winnow" none
      ([ .toolbar [.identified Ids.settingsButton (.button "Settings" .plain (some (.home .openSettings)))],
         .list (homeSections m) ] ++ overlays m)
      (onRefresh := some .syncNow)

def otherNetwork (n : Network) : Network := if n == .mainnet then .signet else .mainnet

def view (m : Model) : H :=
  match m.stage with
  | .loading => .screen "Winnow" none ([.progress "Opening wallet…"] ++ confirms m)
  | .storageDamaged msg =>
    let other := otherNetwork m.settings.network
    .screen "Winnow" none
      ([.empty "Wallet data needs attention" "externaldrive.badge.exclamationmark" msg
        [ .button "Retry without changing anything" .primary (some .retryOpen)
        , .button s!"Open the {other.name} wallet instead" .plain (some (.switchNetwork other)) ]] ++ confirms m)
  | .onboarding => onboardingView m
  | .ready => mainScreen m

end WinnowApp
