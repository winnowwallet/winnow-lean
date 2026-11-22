import Journeys.Screens

/-! # Journeys over the overlay networks

The fixture's SOCKS5 gateway (scripts/socks-gateway, started by scripts/ui-fixture) stands in for the Tor gateway
a person runs: a CONNECT to any .onion name reaches the regtest node, and anything else is refused. So the app can
be put on Tor alone, as a person puts it, and a payment found through the gateway. -/

namespace WinnowJourneys
open Lean LeanNative LeanNative.Journey WinnowApp.Ids

/-- The node as a Tor hidden service, for the gateway (any name ending in .onion reaches it): a v3 onion name, 56
base32 characters, as Winnow dials only a canonical one. -/
def onionPeer (h : Host) : String :=
  s!"{String.ofList ((List.replicate 4 "winnowregtestnode".toList).flatten.take 56)}.onion:{h.p2p}"

/-- Whether the gateway was asked for `peer` and gave it. -/
def gatewayGave (h : Host) (peer : String) : IO Bool := do
  let text ← try IO.FS.readFile h.socksLog catch _ => pure ""
  return (text.splitOn "\n").contains s!"{peer} ok"

/-- Settings → Peers and routing: the wallet's peer is the node's onion name in place of the local address,
routing is Manual with Tor alone through the gateway, and a payment from the node is then found through it. The
gateway saw the app ask for the name, the peers page shows a Tor peer, and clearnet is never used. -/
def torOnly : Journey := ⟨"torOnly", do
  let r ← Run.new "toronly"
  let h := r.host
  expect (h.socksGateway != 0) "the fixture has no SOCKS gateway (scripts/ui-fixture start)"
  r.launch "toronly"
  createWallet

  step "the node funds the wallet over the local peer" do
    let address ← Receive.address
    Receive.close
    discard <| h.fund address funding
    waitForBalance funding

  step "Peers and routing: the node's onion name in place of its address, Manual routing, Tor alone through the gateway" do
    openSettings
    scrolled networkPeersButton
    tap networkPeersButton
    scrolled (.button "Remove")
    tap (.button "Remove")
    scrolled manualPeerField
    type manualPeerField (onionPeer h)
    tap (.button "Add")
    scrolled gatewayRoutingMode
    tap gatewayRoutingMode
    tap (.button "Manual")
    tap (peerType "tor")
    tap (peerType "clearnet")
    type torGatewayAddress s!"127.0.0.1:{h.socksGateway}"
    scrolled applyPeerRouting
    tap applyPeerRouting
    shot "70-tor-routing"
    waitUntil 60 "the gateway was never asked for the node's onion name" (every := 0.5) do gatewayGave h (onionPeer h)
    -- the page's list is what the last Refresh read
    waitUntil 60 "the peers page shows no Tor peer" (every := 1) do
      scrolled (.button "Refresh")
      tap (.button "Refresh")
      if !(← exists? peerNetwork) then return false
      return (← text peerNetwork).startsWith "Tor"
    expectEq "the peer the page shows" (← text peerEndpoint) (onionPeer h)

  step "a payment from the node is found through the gateway alone" do
    backToWalletList
    let address ← Receive.address
    Receive.close
    let tx ← h.fund address recoveryPayment
    waitForBalance (funding + recoveryPayment)
    waitFor (historyPayment tx) 30
    shot "71-tor-funded"
    let refused := ((← IO.FS.readFile h.socksLog).splitOn "\n").filter (·.endsWith "refused")
    expect refused.isEmpty s!"the app asked the gateway for clearnet: {refused}"⟩

/-- What the fixture's proxy in front of the node does: `pass`, `drop` or `stall` (scripts/peer-proxy). -/
def Host.peerMode (h : Host) (mode : String) : IO Unit := do
  let tmp := h.peerProxyControl ++ ".tmp"
  IO.FS.writeFile tmp (Json.mkObj [("mode", Json.str mode)]).compress
  IO.FS.rename tmp h.peerProxyControl

/-- The wallet's one peer is the fixture's proxy in front of the node. It drops every connection, as a peer that
went away does: Home says so, and when it serves again the wallet reconnects by itself and finds a payment. It
then stalls, keeping the connection open and answering nothing, as a peer that stopped answering does: the wallet
gives it up and says so, and once it answers again finds the next payment. -/
def peerFailures : Journey := ⟨"peerFailures", do
  let r ← Run.new "peerfail"
  let h := r.host
  expect (h.peerProxy != 0) "the fixture has no peer proxy (scripts/ui-fixture start)"
  h.peerMode "pass"
  r.launch "peerfail" [("WINNOW_E2E_PEER", s!"127.0.0.1:{h.peerProxy}")]
  createWallet
  let address ← step "the wallet syncs through the proxy" do
    let address ← Receive.address
    Receive.close
    discard <| h.fund address funding
    waitForBalance funding
    pure address
  try
    step "the peer drops every connection: Home says the network is gone" do
      h.peerMode "drop"
      waitFor homeNetworkWarning 120
      shot "90-peer-dropped"

    step "the peer serves again: the wallet reconnects by itself and finds a payment" do
      h.peerMode "pass"
      discard <| h.fund address smallCoin
      waitUntil 120 "the balance did not reach the payment's" (every := 0.5) do
        return (← balance) == some (funding + smallCoin)
      waitUntil 60 "Home still warns" do return !(← exists? homeNetworkWarning)

    step "the peer stalls on its open connection: the wallet gives it up and says so" do
      h.peerMode "stall"
      h.mine 1
      waitFor homeNetworkWarning 240
      shot "91-peer-stalled"

    step "the peer answers again: the wallet finds the next payment" do
      h.peerMode "pass"
      discard <| h.fund address recoveryPayment
      waitUntil 180 "the balance did not reach the next payment's" (every := 0.5) do
        return (← balance) == some (funding + smallCoin + recoveryPayment)
  finally
    h.peerMode "pass"⟩

end WinnowJourneys
