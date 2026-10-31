import LeanNativeShell.Manifest

/-! The Winnow app's Xcode project, from LeanNative's app manifest: `lake exe ios-project` (IosProject.lean)
writes its XcodeGen spec, and LeanNative's framework/native/ci/build-ios runs it. The app never imports this
module, so none of it is in the app; records-test checks the background identifiers against
`WinnowApp.Real` (testBackgroundIdentifiersAreDeclaredInBuiltApplication).

What every LeanNative app has (the printed shell, the C shim and Lean's C as sources, the scene delegate,
Lean's headers and retargeted libraries, `-O3`, ad-hoc signing and arm64 only in the simulator) comes from
the framework. What the capabilities in `uses` need is checked at generation: a Face ID, Bluetooth,
background-task or CloudKit use without its usage text or entitlement is refused. -/

namespace WinnowApp
open LeanNativeShell

def manifest : Manifest where
  name := "WinnowLean"
  displayName := "Winnow"
  -- the Swift app's identity, which this app replaces on TestFlight: the same bundle identifier and team,
  -- meant to let an update keep an installed wallet's Keychain items and files (not yet tried over an
  -- installed Swift build)
  bundleId := "com.btcswift.app"
  team := some "2858MX5336"
  -- release.yml sets both from the tag, as xcodebuild arguments
  version := .settings "0.1.0" "1"
  -- as upstream: the iPad app also runs on Apple silicon Macs ("Designed for iPad"); no Mac Catalyst build
  mac := .designedForiPad
  -- upstream's orientations: portrait on iPhone, all four on iPad
  orientations := some ([.portrait], [.portrait, .portraitUpsideDown, .landscapeLeft, .landscapeRight])
  -- upstream's Assets.xcassets: one 1024 pt icon; Xcode makes the other sizes
  icon := some "Assets.xcassets"
  resources := [
    -- the design papers, bundled as the Swift app bundles them (shown by the `page` node)
    "../../docs/site.css", "../../docs/mobile.html", "../../docs/read-side.html",
    "../../docs/write-side.html", "../../docs/import.html",
    -- the census list this build ships (CensusCatalog.bundled reads peers.json beside the executable),
    -- fetched by scripts/import-census (scripts/build-ios runs it when the list is missing)
    "../../build/census/peers.json"]
  uses := ["auth", "keychain.*", "build", "clipboard.*", "paths", "exclude-from-backup", "http.get", "open",
           "ble.*", "bgtask.*", "cloudkit.*"]
  usage := [
    ("NSFaceIDUsageDescription", "Approve payments and reveal your recovery words."),
    -- a paired Ledger signs multisig spends over the shell's ble.* capabilities (upstream's text)
    ("NSBluetoothAlwaysUsageDescription",
     "Winnow talks to your Ledger over Bluetooth to have it sign multisig payments you approve on its screen."),
    -- Automatic routing asks Tailscale's MagicDNS and probes the gateways it names (upstream's text)
    ("NSLocalNetworkUsageDescription",
     "Winnow checks your Tailscale gateways and connects to Bitcoin nodes you configure.")]
  -- background chain checks (WinnowApp/Real/BackgroundSync.lean): iOS decides when they run; each is one
  -- bounded scan with the foreground's routing. The shell registers a handler for each identifier.
  backgroundTasks := [("com.btcswift.winnow.chain-refresh", .refresh),
                      ("com.btcswift.winnow.chain-processing", .processing)]
  -- automatic iCloud backup (WinnowApp/Real/CloudBackup.lean): the private database of upstream's container
  -- (CloudKit/schema.ckdb's WalletBackup records)
  iCloudContainers := ["iCloud.com.btcswift.app"]
  info := [("ITSAppUsesNonExemptEncryption", false)]
  -- the UI test target holds only LeanNative's test kit and its journey driver (LNDriver): the journeys are Lean,
  -- on the Mac (Journeys.lean), run by scripts/ui-journeys (CI: LeanNative's ui-tests with scripts/ui-fixture)
  -- against a regtest fixture
  uiTests := some { sources := [] }

end WinnowApp
