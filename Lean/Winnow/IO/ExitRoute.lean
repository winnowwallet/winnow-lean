import Winnow.IO.Http

/-! # A Tailscale exit node as the route of direct connections, and whether it is Mullvad's

Tailscale sells Mullvad's servers as exit nodes of a tailnet. While a device uses an exit node, everything it
sends beyond its own networks leaves through that node, so a Bitcoin peer sees the node's address and not the
device's. Winnow cannot ask the Tailscale app which exit node is selected; it can tell two things:

* **That an exit node is the route**, from the routing table alone (`tunnelSource`): a socket for a public
  address would leave from the device's tailnet address, the one a socket for Tailscale's own resolver
  (100.100.100.100) leaves from. Connecting a datagram socket picks the route and sends nothing. A carrier may
  number phones from the same block (100.64.0.0/10), so the answer also needs Tailscale's own IPv6 prefix on
  the IPv6 route, or Tailscale's resolver answering a query.
* **That the exit node is Mullvad's**, by asking Mullvad (`askMullvad`): one HTTPS request to
  `am.i.mullvad.net`, made only once an exit node is the route, so it reaches Mullvad from the exit node's
  address. Mullvad learns nothing it does not carry already when the node is its own; when the node is someone
  else's machine, Mullvad sees that machine's address ask once.

The addresses found (`TunnelSource`) are what the pool binds its direct connections to
(`PeerConnection.tunnel`), so a connection of that session leaves through the exit node or not at all. -/

namespace Winnow.IO
open Lean Winnow.Net Std.Net Std.Async

/-- An address in Tailscale's own IPv6 prefix, fd7a:115c:a1e0::/48. -/
def isTailnetIPv6 (host : String) : Bool :=
  match inetPton6 host with
  | some b => b.size == 16 && (b.extract 0 6) == #[0xfd, 0x7a, 0x11, 0x5c, 0xa1, 0xe0]
  | none => false

/-- Whether Tailscale's resolver (100.100.100.100) answers a query at all (2 s): Tailscale is running. The
query is the Tor gateway's name, which discovery asks it anyway. -/
def quad100Answers : IO Bool := do
  let q : GatewayDNSQuery := { host := "winnow-tor-gateway", id := (← IO.rand 0 65535).toUInt16 }
  let answer ← withDeadline 2_000 (do
    let sock ← UDP.Socket.mk
    sock.connect (← PeerConnection.resolveAddress "100.100.100.100" 53)
    sock.send q.bytes
    let (data, _) ← sock.recv 512
    return data : Async ByteArray)
  return match answer with
    | some b => b.size ≥ 12 && b[0]! == (q.id >>> 8).toUInt8 && b[1]! == (q.id &&& 255).toUInt8 && b[2]! &&& 0x80 != 0
    | none => false

/-- The device's tailnet addresses when a Tailscale exit node carries its default route, none otherwise.
`toward` is the routing table's answer (`localAddressToward`) and `tailscaleAnswers` the resolver's
(`quad100Answers`, asked only when the IPv6 route does not settle it); both are injectable. -/
def tunnelSource (toward : String → IO (Option String) := localAddressToward)
    (tailscaleAnswers : IO Bool := quad100Answers) : IO (Option TunnelSource) := do
  let some v4 ← toward TunnelSource.probe4 | return none
  unless isTailnetIPv4 v4 && (← toward "100.100.100.100") == some v4 do return none
  let v6 := (← toward TunnelSource.probe6).filter isTailnetIPv6
  if v6.isNone then
    unless ← tailscaleAnswers do return none
  return some { v4, v6 }

/-- What Mullvad says of the address a request reached it from. -/
inductive MullvadAnswer where
  /-- One of Mullvad's exit addresses, and the server's name when Mullvad gives one. -/
  | mullvad (server : Option String)
  | notMullvad
  deriving BEq, Repr, Inhabited

namespace MullvadAnswer

def url : String := "https://am.i.mullvad.net/json"

/-- A server name worth showing: Mullvad's are like `se-sto-wg-001`. -/
def serverName (s : String) : Option String :=
  if 0 < s.length && s.length ≤ 40 && s.toList.all (fun c => c.isAlphanum || c == '-') then some s else none

/-- The answer in Mullvad's JSON: `mullvad_exit_ip` must be the boolean `true` to count as Mullvad's. None
when the body is not that JSON object. The bytes are a server's: `Winnow.Text.parseJson` bounds what
`Lean.Json.parse` would not (a number's exponent). -/
def parse (body : ByteArray) : Option MullvadAnswer := do
  let text ← String.fromUTF8? body
  let j ← (Winnow.Text.parseJson text).toOption
  match j.getObjVal? "mullvad_exit_ip" with
  | .ok (.bool true) => some (.mullvad ((j.getObjValAs? String "mullvad_exit_ip_hostname").toOption.bind serverName))
  | .ok (.bool false) => some .notMullvad
  | _ => none

end MullvadAnswer

/-- Asks Mullvad (one request, no redirect followed, 8 s in all); none when it does not answer. -/
def askMullvad (fetch : HttpFetch) : IO (Option MullvadAnswer) := do
  let p ← IO.Promise.new
  discard <| IO.asTask do
    let r ← (fetch { url := MullvadAnswer.url, accept := some "application/json", maximumBytes := 4096,
                     requestTimeoutSeconds := 5, resourceTimeoutSeconds := 8 }).attempt
    p.resolve (match r with
      | .ok (.response 200 _ body) => if body.size ≤ 4096 then MullvadAnswer.parse body else none
      | _ => none)
  after 8_000 (p.resolve none)
  return (← IO.wait p.result?).join

/-- How this session's direct connections leave the device. -/
inductive ExitRoute where
  /-- From the device's own network: whoever is reached sees its address. -/
  | direct
  /-- Through a Tailscale exit node that Mullvad did not confirm as its own (it said no, or did not answer). -/
  | exitNode (source : TunnelSource)
  /-- Through one of Mullvad's servers. -/
  | mullvad (source : TunnelSource) (server : Option String)
  deriving BEq, Repr, Inhabited

namespace ExitRoute

def source? : ExitRoute → Option TunnelSource
  | .direct => none
  | .exitNode s | .mullvad s _ => some s

def isMullvad : ExitRoute → Bool
  | .mullvad .. => true
  | _ => false

end ExitRoute

/-- The route now: direct unless an exit node carries the default route; then Mullvad is asked, and the route
is looked at again afterwards, so an exit node switched off during the question is not reported. -/
def detectExitRoute (ask : IO (Option MullvadAnswer)) (source : IO (Option TunnelSource) := tunnelSource) :
    IO ExitRoute := do
  let some s ← source | return .direct
  let answer ← ask
  unless (← source) == some s do return .direct
  return match answer with
    | some (.mullvad server) => .mullvad s server
    | _ => .exitNode s

end Winnow.IO
