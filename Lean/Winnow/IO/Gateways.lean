import Winnow.IO.Census
import Winnow.IO.Transport

/-! # Tor and I2P peers through SOCKS gateways (`PeerGateways.swift`, `TailnetGatewayDiscovery.swift`)

Upstream #181, #189, #190, #193: a wallet may reach Bitcoin peers on Tor and I2P through SOCKS5 gateways,
normally two devices on the user's tailnet named `winnow-tor-gateway` and `winnow-i2p-gateway`. The pool
dials an overlay peer through the gateway for its network, naming the peer to it unresolved
(`PeerConnection.socksProxy`). When a gateway answers, clearnet is dropped: every peer then goes through
Tor or I2P. Discovery asks Tailscale's MagicDNS (100.100.100.100) over UDP for each name, takes an
address in the tailnet's 100.64.0.0/10 block, and probes it with a SOCKS5 greeting. -/

namespace Winnow.IO
open Lean Winnow.Net Std.Net Std.Async

/-- `PeerNetwork.canonicalHost`: a numeric public clearnet address, or a canonical overlay name. -/
def PeerNetwork.canonicalHost (n : PeerNetwork) (host : String) : Option String :=
  match n with
  | .clearnet => CensusCatalog.canonicalHost host
  | _ => n.canonicalOverlayHost host

/-- Which networks a pool may use, and the SOCKS gateway for each overlay (`PeerGatewayConfiguration`). -/
structure PeerGatewayConfiguration where
  networks : List PeerNetwork := [.clearnet]
  torProxy : Option PeerEndpoint := none
  i2pProxy : Option PeerEndpoint := none
  deriving BEq, Repr, Inhabited

namespace PeerGatewayConfiguration

/-- A plausible gateway: a clearnet `host:port` of printable ASCII with no URL syntax in the host. -/
def validProxy (e : Option PeerEndpoint) : Bool :=
  match e with
  | none => false
  | some e =>
    e.port > 0 && !e.host.isEmpty && e.host.utf8ByteSize ≤ 253 &&
      !e.host.toList.any (fun c => c.isWhitespace || "/@?#\\%[]".toList.contains c) &&
      PeerNetwork.ofHost e.host == .clearnet && e.host.toUTF8.toList.all (fun b => 33 ≤ b && b ≤ 126)

def isValid (c : PeerGatewayConfiguration) : Bool :=
  !c.networks.isEmpty && (!c.networks.contains .tor || validProxy c.torProxy) &&
    (!c.networks.contains .i2p || validProxy c.i2pProxy)

/-- Whether the pool may dial this peer: its network selected, and an overlay name canonical. -/
def permits (c : PeerGatewayConfiguration) (e : PeerEndpoint) : Bool :=
  let n := PeerNetwork.ofHost e.host
  c.isValid && e.port > 0 && c.networks.contains n && (n == .clearnet || (n.canonicalHost e.host).isSome)

/-- The gateway a peer is dialled through (none for clearnet). -/
def proxy (c : PeerGatewayConfiguration) (e : PeerEndpoint) : Option PeerEndpoint :=
  match PeerNetwork.ofHost e.host with
  | .clearnet => none
  | .tor => c.torProxy
  | .i2p => c.i2pProxy

/-- HTTPS (seeds, explorer) needs clearnet or Tor; without clearnet it goes through the Tor gateway. -/
def permitsHTTP (c : PeerGatewayConfiguration) : Bool := c.isValid && (c.networks.contains .clearnet || c.networks.contains .tor)
def httpProxy (c : PeerGatewayConfiguration) : Option PeerEndpoint := if c.networks.contains .clearnet then none else c.torProxy

inductive Invalid where
  | configuration | address
  deriving BEq, Repr

def Invalid.description : Invalid → String
  | .configuration => "Choose at least one peer network and provide a SOCKS gateway for each selected overlay."
  | .address => "Enter a gateway as host:port or [IPv6]:port."

/-- `parseProxy`: `host:port` or `[IPv6]:port`. -/
def parseProxy (text : String) : Except Invalid PeerEndpoint := do
  let t := Winnow.Keys.Unicode.trimWhitespace text
  let cs := t.toList
  let some colon := (List.range cs.length).reverse.find? (cs[·]! == ':') | throw .address
  let some port := (String.ofList (cs.drop (colon + 1))).toNat? | throw .address
  if port > 65535 || (cs.drop (colon + 1)).isEmpty then throw .address
  let mut host := String.ofList (cs.take colon)
  if host.startsWith "[" && host.endsWith "]" then host := String.ofList ((host.toList.drop 1).dropLast)
  else if host.toList.contains ':' then throw .address
  let e : PeerEndpoint := { host, port := port.toUInt16 }
  unless validProxy (some e) do throw .address
  return e

def endpointJson (e : PeerEndpoint) : Json := Json.mkObj [("host", .str e.host), ("port", Lean.toJson e.port.toNat)]
def endpointOf? (j : Json) : Option PeerEndpoint := do
  let host ← (j.getObjValAs? String "host").toOption
  let port ← (j.getObjValAs? Nat "port").toOption
  if port > 65535 then none else some { host, port := port.toUInt16 }

def toJson (c : PeerGatewayConfiguration) : Json :=
  Json.mkObj ([("networks", Json.arr ((PeerNetwork.allCases.filter c.networks.contains).map (Json.str ·.rawValue)).toArray)] ++
    (match c.torProxy with | some e => [("torProxy", endpointJson e)] | none => []) ++
    (match c.i2pProxy with | some e => [("i2pProxy", endpointJson e)] | none => []))

def ofJson? (j : Json) : Option PeerGatewayConfiguration := do
  let names ← (j.getObjValAs? (List String) "networks").toOption
  let networks ← names.mapM PeerNetwork.ofRaw?
  let proxy (k : String) : Option (Option PeerEndpoint) := match j.getObjVal? k with
    | .ok .null | .error _ => some none
    | .ok v => (endpointOf? v).map some
  return { networks := PeerNetwork.allCases.filter networks.contains, torProxy := ← proxy "torProxy", i2pProxy := ← proxy "i2pProxy" }

end PeerGatewayConfiguration

/-- What the user chose (`PeerGatewaySettings`): find the tailnet's gateways, connect directly, or use the
gateways typed in. -/
structure PeerGatewaySettings where
  mode : String := "automatic"
  manual : PeerGatewayConfiguration := {}
  deriving BEq, Repr, Inhabited

namespace PeerGatewaySettings

def modes : List String := ["automatic", "direct", "manual"]

/-- `Codable`: `{"mode": "automatic"|"direct"|"manual", "manual": {…}}`. -/
def toJson (s : PeerGatewaySettings) : Json := Json.mkObj [("mode", .str s.mode), ("manual", s.manual.toJson)]

def ofJson? (j : Json) : Option PeerGatewaySettings := do
  let mode ← (j.getObjValAs? String "mode").toOption
  unless modes.contains mode do none
  let manual ← PeerGatewayConfiguration.ofJson? (← (j.getObjVal? "manual").toOption)
  return { mode, manual }

/-- What saved settings that cannot be read become (`AppModel.init`): manual with no network, so
networking stays offline rather than fall back to direct connections. -/
def unreadable : PeerGatewaySettings := { mode := "manual", manual := { networks := [] } }

/-- The routing in effect before (or without) discovery: the manual gateways, else clearnet. -/
def initialActive (s : PeerGatewaySettings) : PeerGatewayConfiguration := if s.mode == "manual" then s.manual else {}

end PeerGatewaySettings

/-! ## Discovery (`TailnetGatewayDiscovery`) -/

/-- An address in the tailnet's CGNAT block (100.64.0.0/10), not MagicDNS itself. -/
def isTailnetIPv4 (host : String) : Bool :=
  match inetPton4 host with
  | some o => o[0]! == 100 && (64 : UInt8) ≤ o[1]! && o[1]! ≤ 127 && host != "100.100.100.100"
  | none => false

/-- `GatewayDNSQuery`: an A query for one host, and the tailnet addresses an answer gives for it. -/
structure GatewayDNSQuery where
  host : String
  id : UInt16

namespace GatewayDNSQuery

def bytes (q : GatewayDNSQuery) : ByteArray :=
  ByteArray.mk #[(q.id >>> 8).toUInt8, (q.id &&& 255).toUInt8, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, q.host.utf8ByteSize.toUInt8] ++
    q.host.toUTF8 ++ ByteArray.mk #[0, 0, 1, 0, 1]

/-- A name at `cursor` (labels and compression pointers, at most 16 hops, pointers only backwards), and
the cursor after it. -/
partial def name (b : ByteArray) (cursor : Nat) : Option (String × Nat) := Id.run do
  let mut at_ := cursor
  let mut stop : Option Nat := none
  let mut labels : Array String := #[]
  let mut visited : Array Nat := #[]
  while at_ < b.size && !visited.contains at_ && visited.size < 16 do
    visited := visited.push at_
    let count := b[at_]!.toNat
    if count == 0 then return some (".".intercalate labels.toList |>.toLower, stop.getD (at_ + 1))
    if count &&& 0xc0 == 0xc0 then
      if at_ + 1 ≥ b.size then return none
      let target := (count &&& 0x3f) * 256 + b[at_ + 1]!.toNat
      if target < 12 || target ≥ at_ then return none
      if stop.isNone then stop := some (at_ + 2)
      at_ := target
    else
      if count > 63 || at_ + 1 + count ≥ b.size then return none
      labels := labels.push (String.fromUTF8! (b.extract (at_ + 1) (at_ + 1 + count)))
      at_ := at_ + count + 1
  return none

/-- `addresses(in:)`: the A records for the query's host in a well-formed answer to it. -/
def addresses (q : GatewayDNSQuery) (b : ByteArray) : List String := Id.run do
  let word (i : Nat) : Nat := b[i]!.toNat * 256 + b[i + 1]!.toNat
  if b.size < 12 || word 0 != q.id.toNat || (word 2 &&& 0xfa0f) != 0x8000 || word 4 != 1 || word 6 > 16 then return []
  let some (qname, c) := name b 12 | return []
  if qname != q.host || c + 4 > b.size || word c != 1 || word (c + 2) != 1 then return []
  let mut cursor := c + 4
  let mut result : List String := []
  for _ in [0:word 6] do
    let some (owner, c') := name b cursor | return []
    if c' + 10 > b.size then return []
    let (type, klass, length) := (word c', word (c' + 2), word (c' + 8))
    cursor := c' + 10
    if cursor + length > b.size then return []
    if owner == q.host && type == 1 && klass == 1 && length == 4 then
      result := result ++ [".".intercalate ((b.extract cursor (cursor + 4)).toList.map (toString ·.toNat))]
    cursor := cursor + length
  return result.filter isTailnetIPv4

end GatewayDNSQuery

/-- Runs `x` with a deadline; none on timeout or failure. -/
def withDeadline {α} (ms : Nat) (x : Async α) : IO (Option α) := do
  let p ← IO.Promise.new
  let t ← x.toIO
  discard <| IO.mapTask (t := t) fun r => p.resolve (r.toOption)
  after ms (p.resolve none)
  return (← IO.wait p.result?).join

/-- `resolveMagicDNS`: the tailnet addresses MagicDNS gives for one of the two gateway names (2 s). -/
def resolveMagicDNS (host : String) : IO (List String) := do
  unless ["winnow-tor-gateway", "winnow-i2p-gateway"].contains host do return []
  let q : GatewayDNSQuery := { host, id := (← IO.rand 0 65535).toUInt16 }
  let answer ← withDeadline 2_000 (do
    let sock ← UDP.Socket.mk
    let addr ← PeerConnection.resolveAddress "100.100.100.100" 53
    sock.connect addr
    sock.send q.bytes
    let (data, _) ← sock.recv 512
    return data : Async ByteArray)
  return match answer with
    | some data => if data.size ≥ 12 then q.addresses data else []
    | none => []

/-- `probeSOCKS`: a SOCKS5 no-authentication greeting answered with `05 00` (2 s). -/
def probeSOCKS (e : PeerEndpoint) : IO Bool := do
  let r ← withDeadline 2_000 (do
    let sock ← TCP.Socket.Client.mk
    sock.connect (← PeerConnection.resolveAddress e.host e.port)
    sock.send (ByteArray.mk #[5, 1, 0])
    return (← sock.recv? 2) : Async (Option ByteArray))
  return r.join == some (ByteArray.mk #[5, 0])

/-- `TailnetGatewayDiscovery.discover()`: the gateways that answer; with one, clearnet is dropped (every
peer through Tor or I2P), with none the default (clearnet). `resolve` and `probe` are injectable. -/
def discoverGateways (resolve : String → IO (List String) := resolveMagicDNS) (probe : PeerEndpoint → IO Bool := probeSOCKS) :
    IO PeerGatewayConfiguration := do
  let find (host : String) (port : UInt16) : IO (Option PeerEndpoint) := do
    let some address := (← resolve host).find? isTailnetIPv4 | return none
    let e : PeerEndpoint := { host := address, port }
    return if ← probe e then some e else none
  let tor ← IO.asTask (find "winnow-tor-gateway" 9050)
  let i2p ← IO.asTask (find "winnow-i2p-gateway" 4447)
  let tor := (← IO.wait tor).toOption.join
  let i2p := (← IO.wait i2p).toOption.join
  let networks := (if tor.isSome then [PeerNetwork.tor] else []) ++ (if i2p.isSome then [.i2p] else [])
  if networks.isEmpty then return {}
  return { networks, torProxy := tor, i2pProxy := i2p }

end Winnow.IO
