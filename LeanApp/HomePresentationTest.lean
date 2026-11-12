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

def funded : Model :=
  { stage := .ready, walletID := some "presentation-test", phase := .synced,
    settings := { network := .mainnet }, status := { balance := 13_790_000 } }

def main : IO UInt32 := runMain "home-presentation-test" do
  let offline := { funded with phase := .peerDiscoveryFailed }
  let h := home offline
  check "offline balance is explicitly last known" (textHas h "Last known balance")
  check "offline retains the separate network and IP exposure warnings"
    (textHas h "Offline" && textHas h "Peers see your IP")
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
    (textHas h "Pairing alone does not protect your existing balance.")
  -- Its primary action lives inside the callout, not on a new/unhandled route.
  check "protection CTA retains its setup action"
    (match protectionCards offline with
      | [protection] => (protection.dispatch [0, 2] .click matches some (.home .protectWithLedger))
      | _ => false)
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
