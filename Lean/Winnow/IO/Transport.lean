import Winnow.IO.Base

/-! # One Bitcoin P2P peer over Lean's libuv TCP (`Network/Transport/PeerConnection.swift`)

The Swift `actor PeerConnection` is a structure whose mutable state sits in one `IO.Ref`; every state
transition is an atomic `modifyGet` over it, and the effects (socket writes, resolving waiters,
notifying subscribers) happen outside it, as the actor's code runs between suspension points.

Lifecycle, as in Swift: `connect` opens the socket and performs the version/verack handshake
(protocol 70016, services 0, UA `/winnow:0.1/`, our BIP37 relay flag), refuses a peer without
NODE_COMPACT_FILTERS, sends `sendheaders` (BIP130) and starts the keepalive (ping every 60 s, dead
after 150 s of silence). Inbound `ping` is answered and `feefilter` recorded (and multicast); any other
message resolves a waiting request or collector, or goes to the bounded backlog (256 messages /
`backlogByteLimit` bytes, oldest dropped; `block`/`addr` are not kept; an unsolicited message larger than
the whole buffer is a protocol violation) and to every `events` subscriber. A request purges the backlog
of its reply command first. A relayed `tx` over 400,000 bytes is dropped undecoded. Timeouts run on
libuv timers; the keepalive is a chain of timers; each connection has one dedicated receive thread.

Differences the platform forces (deliberate, small):
* `NWConnection` sits in `.waiting` on a refused dial until the timeout fires (`PeerError.timeout`);
  libuv reports the refusal at once, so a refused dial fails immediately with `disconnected`.
* A hostname is resolved with `getaddrinfo` (Std.Async.DNS) and its first address dialled (IPv4
  first); NWConnection races the addresses.
* Closing is `cancelRecv` + `shutdown` + dropping the socket (libuv closes it on finalization):
  `Std.Async.TCP` has no `close`.
* Swift's `connect` also tears down when its task is cancelled; Lean tasks are not cancelled here.
* A subscriber registered after teardown gets a stream that has already ended (Swift's never ends).
* A failed `request` send unregisters its waiter at once (Swift leaves it to its timeout).
* A request on a closed peer is refused before the backlog is purged (Swift purges first; teardown has
  already emptied the backlog, so nothing observable differs). -/

namespace Winnow.IO
open Winnow.Net Std.Net Std.Async

/-- Unsolicited things a peer tells us outside request/response exchanges. -/
inductive PeerEvent where
  | message (m : PeerMessage)
  | disconnected
  deriving Inhabited

abbrev PeerStream := EventStream PeerEvent NetError

structure PendingRequest where
  id : Nat
  commands : Array String
  promise : IO.Promise (Except NetError PeerMessage)

structure PendingCollector where
  id : Nat
  command : String
  expected : Nat
  received : Array PeerMessage
  promise : IO.Promise (Except NetError (Array PeerMessage))
  /-- the burst's byte bound (`maxTotalBytes`), and the payload bytes received so far -/
  maxTotalBytes : Option Nat := none
  receivedBytes : Nat := 0

structure ConnState where
  peerServices : UInt64 := 0
  peerUserAgent : String := ""
  peerStartHeight : Int32 := 0
  feeFilter : Option Int64 := none
  isConnected : Bool := false
  permanentlyClosed : Bool := false
  didTeardown : Bool := false
  /-- Swift's `connection != nil`. -/
  hasConnection : Bool := false
  socket : Option TCP.Socket.Client := none
  ready : Option (IO.Promise (Except NetError Unit)) := none
  framer : MessageFramer
  pending : Array PendingRequest := #[]
  collectors : Array PendingCollector := #[]
  backlog : Array (PeerMessage × Nat) := #[]
  backlogBytes : Nat := 0
  subscribers : Array PeerStream := #[]
  nextId : Nat := 0
  lastReceivedAt : Nat := 0

initialize connectionCounter : IO.Ref Nat ← IO.mkRef 0

structure PeerConnection where
  /-- Identity (Swift compares connections with `===`). -/
  uid : Nat
  endpoint : PeerEndpoint
  params : NetworkParams
  localServices : UInt64
  localStartHeight : Int32
  /-- BIP37 relay flag sent in our version message. -/
  relayPreference : Bool
  backlogByteLimit : Nat
  pingIntervalMs : Nat
  readIdleTimeoutMs : Nat
  /-- An external SOCKS5 gateway (a Tor or I2P proxy): dialled instead of the peer, which is named to it
  unresolved, so `.onion` and `.i2p` hosts reach the gateway as names. -/
  socksProxy : Option PeerEndpoint := none
  state : IO.Ref ConnState

instance : BEq PeerConnection := ⟨fun a b => a.uid == b.uid⟩

namespace PeerConnection

def protocolVersion : Int32 := 70_016
def userAgent : String := "/winnow:0.1/"
/-- BIP157/158 service bit 6. -/
def nodeCompactFilters : UInt64 := (1 : UInt64) <<< 6
def backlogLimit : Nat := 256
def defaultBacklogByteLimit : Nat := 8_000_000
def maximumRelayedTransactionBytes : Nat := 400_000

/-- `PeerConnection(endpoint:params:…)`; `backlogByteLimit` must be positive (a precondition in Swift). -/
def new (endpoint : PeerEndpoint) (params : NetworkParams) (localServices : UInt64 := 0)
    (localStartHeight : Int32 := 0) (relayPreference : Bool := false)
    (backlogByteLimit : Nat := defaultBacklogByteLimit) (pingIntervalMs : Nat := 60_000)
    (readIdleTimeoutMs : Nat := 150_000) (socksProxy : Option PeerEndpoint := none) : IO PeerConnection := do
  if backlogByteLimit == 0 then throw (IO.userError "the gossip buffer needs a positive ceiling")
  let uid ← connectionCounter.modifyGet fun n => (n, n + 1)
  let now ← monoMs
  return { uid, endpoint, params, localServices, localStartHeight, relayPreference, backlogByteLimit,
           pingIntervalMs, readIdleTimeoutMs, socksProxy,
           state := ← IO.mkRef { framer := { magic := params.magic }, lastReceivedAt := now } }

def peerServices (c : PeerConnection) : BaseIO UInt64 := do return (← c.state.get).peerServices
def peerUserAgent (c : PeerConnection) : BaseIO String := do return (← c.state.get).peerUserAgent
def peerStartHeight (c : PeerConnection) : BaseIO Int32 := do return (← c.state.get).peerStartHeight
/-- Latest BIP133 feefilter (sat/kvB) the peer sent. -/
def feeFilter (c : PeerConnection) : BaseIO (Option Int64) := do return (← c.state.get).feeFilter
def isConnected (c : PeerConnection) : BaseIO Bool := do return (← c.state.get).isConnected
/-- What the gossip buffer holds: messages and payload bytes. -/
def backlogSize (c : PeerConnection) : BaseIO (Nat × Nat) := do
  let s ← c.state.get
  return (s.backlog.size, s.backlogBytes)

private def awaitPromise {α} (p : IO.Promise (Except NetError α)) : NetM α := do
  match ← IO.wait p.result? with
  | some (.ok a) => pure a
  | some (.error e) => throw e
  | none => throw (.peer (.disconnected "closed"))

/-! ## Teardown -/

def teardown (c : PeerConnection) (error : Option NetError) : IO Unit := do
  let taken ← c.state.modifyGet fun st =>
    if st.didTeardown then (none, st)
    else (some (st.socket, st.ready, st.pending, st.collectors, st.subscribers),
          { st with didTeardown := true, isConnected := false, hasConnection := false, socket := none,
                    ready := none, pending := #[], collectors := #[], backlog := #[], backlogBytes := 0,
                    subscribers := #[] })
  let some (sock, ready, pending, collectors, subscribers) := taken | return
  if let some s := sock then
    try s.native.cancelRecv catch _ => pure ()
    try discard <| s.shutdown.toIO catch _ => pure ()
  let failure := error.getD (.peer (.disconnected "closed"))
  if let some r := ready then r.resolve (.error failure)
  for p in pending do p.promise.resolve (.error failure)
  for col in collectors do col.promise.resolve (.error failure)
  for s in subscribers do
    s.yield .disconnected
    s.finish error

/-- Cleanly closes the connection and finishes every event stream. -/
def disconnect (c : PeerConnection) : IO Unit := do
  c.state.modify fun st => { st with permanentlyClosed := true }
  c.teardown none

/-! ## Sending and waiting -/

def send (c : PeerConnection) (m : PeerMessage) : NetM Unit := do
  let st ← c.state.get
  let some sock := st.socket | throw (.peer .notConnected)
  if st.didTeardown then throw (.peer .notConnected)
  let framed := MessageFramer.frame m.command m.payload c.params.magic
  match ← (sock.send framed).block.toBaseIO with
  | .ok () => pure ()
  | .error e => throw (.peer (.disconnected (toString e)))

private def expire (c : PeerConnection) (id : Nat) : IO Unit := do
  let (p, col) ← c.state.modifyGet fun st =>
    let p := st.pending.find? (·.id == id)
    let col := st.collectors.find? (·.id == id)
    ((p, col), { st with pending := st.pending.filter (·.id != id), collectors := st.collectors.filter (·.id != id) })
  if let some p := p then p.promise.resolve (.error (.peer .timeout))
  if let some col := col then col.promise.resolve (.error (.peer .timeout))

private def scheduleTimeout (c : PeerConnection) (id : Nat) (ms : Nat) : IO Unit :=
  after ms (c.expire id)

private def takeFromBacklog (st : ConnState) (i : Nat) : PeerMessage × ConnState :=
  let (m, bytes) := st.backlog[i]!
  (m, { st with backlog := st.backlog.eraseIdx! i, backlogBytes := st.backlogBytes - bytes })

private def purge (st : ConnState) (pred : PeerMessage → Bool) : ConnState :=
  let (drop, keep) := st.backlog.partition (pred ·.1)
  { st with backlog := keep, backlogBytes := st.backlogBytes - drop.foldl (· + ·.2) 0 }

/-- Swift's `guard connection != nil, !didTeardown`: a closed (or never opened) peer has no one left to
resolve a waiter, so registering one would only sleep until its deadline (#176). -/
private def isOpen (st : ConnState) : Bool := st.hasConnection && !st.didTeardown

/-- Registers a waiter for the first message among `commands` (the backlog is consulted first); a
closed peer refuses with `notConnected` instead of registering. -/
private def register (c : PeerConnection) (commands : Array String) (purgeFirst : Bool) :
    NetM (Sum PeerMessage (Nat × IO.Promise (Except NetError PeerMessage))) := do
  let p ← IO.Promise.new
  let r ← c.state.modifyGet fun st =>
    if !isOpen st then (none, st) else
    let st := if purgeFirst then purge st (commands.contains ·.command) else st
    match st.backlog.findIdx? (commands.contains ·.1.command) with
    | some i => let (m, st) := takeFromBacklog st i; (some (.inl m), st)
    | none =>
      let id := st.nextId
      (some (.inr (id, p)), { st with nextId := id + 1, pending := st.pending.push { id, commands, promise := p } })
  match r with
  | some r => return r
  | none => throw (.peer .notConnected)

private def waitFor (c : PeerConnection) (commands : Array String) (timeoutMs : Nat) : NetM PeerMessage := do
  match ← c.register commands false with
  | .inl m => return m
  | .inr (id, p) =>
    c.scheduleTimeout id timeoutMs
    awaitPromise p

/-- Sends a request and awaits the first response among `commands`. -/
def request (c : PeerConnection) (m : PeerMessage) (commands : Array String) (timeoutMs : Nat := 30_000) :
    NetM PeerMessage := do
  match ← c.register commands true with
  | .inl reply => c.send m; return reply
  | .inr (id, p) =>
    c.scheduleTimeout id timeoutMs
    try c.send m
    catch e =>
      c.state.modify fun st => { st with pending := st.pending.filter (·.id != id) }
      throw e
    awaitPromise p

private def burstTooLarge (command : String) (bytes limit : Nat) : NetError :=
  .peer (.protocolViolation s!"{command} burst of {bytes} bytes exceeds the {limit}-byte bound")

/-- Sends a request and collects `count` responses of one command (the `cfilter` burst). A burst past
`maxTotalBytes` payload bytes tears the connection down with a protocol violation. -/
def requestMany (c : PeerConnection) (m : PeerMessage) (command : String) (count : Nat) (timeoutMs : Nat := 60_000)
    (maxTotalBytes : Option Nat := none) : NetM (Array PeerMessage) := do
  if count == 0 then throw (.other "requestMany: count must be positive")
  let p ← IO.Promise.new
  let r ← c.state.modifyGet fun st =>
    if !isOpen st then (none, st) else
    let st := purge st (·.command == command)
    let id := st.nextId
    let st := { st with nextId := id + 1 }
    let rec drain (st : ConnState) (got : Array PeerMessage) (bytes : Nat) (fuel : Nat) : ConnState × Array PeerMessage × Nat :=
      match fuel with
      | 0 => (st, got, bytes)
      | fuel + 1 =>
        if got.size ≥ count then (st, got, bytes)
        else match st.backlog.findIdx? (·.1.command == command) with
          | some i =>
            let size := st.backlog[i]!.2
            let (msg, st) := takeFromBacklog st i
            drain st (got.push msg) (bytes + size) fuel
          | none => (st, got, bytes)
    let (st, got, bytes) := drain st #[] 0 (st.backlog.size + 1)
    if maxTotalBytes.any (bytes > ·) then (some (Sum.inl (Sum.inl bytes)), st)
    else if got.size ≥ count then (some (Sum.inl (Sum.inr got)), st)
    else
      let col : PendingCollector :=
        { id, command, expected := count, received := got, promise := p, maxTotalBytes, receivedBytes := bytes }
      (some (Sum.inr id), { st with collectors := st.collectors.push col })
  let some r := r | throw (.peer .notConnected)
  match r with
  | .inl (.inl bytes) =>
    let e := burstTooLarge command bytes (maxTotalBytes.getD 0)
    c.teardown (some e)
    throw e
  | .inl (.inr got) => c.send m; return got
  | .inr id =>
    c.scheduleTimeout id timeoutMs
    try
      c.send m
      awaitPromise p
    catch e =>
      c.state.modify fun st => { st with collectors := st.collectors.filter (·.id != id) }
      throw e

/-- Manual ping: sends a nonce and waits for any pong. -/
def ping (c : PeerConnection) (timeoutMs : Nat := 10_000) : NetM Unit := do
  discard <| c.request (.ping (← randomU64)) #["pong"] timeoutMs

/-- A multicast stream of unsolicited messages; each caller gets its own, bounded so that a stalled
subscriber cannot hold more than the backlog's byte ceiling (counted in maximal payloads). -/
def events (c : PeerConnection) : IO PeerStream := do
  let largest := min c.backlogByteLimit MessageFramer.maxPayloadSize
  let slots := min backlogLimit (max 1 (c.backlogByteLimit / largest))
  let id ← c.state.modifyGet fun st => (st.nextId, { st with nextId := st.nextId + 1 })
  let s : PeerStream ← EventStream.new id slots
  s.onCancel.set (c.state.modify fun st => { st with subscribers := st.subscribers.filter (·.id != id) })
  let added ← c.state.modifyGet fun st =>
    if st.didTeardown then (false, st) else (true, { st with subscribers := st.subscribers.push s })
  if !added then s.finish none
  return s

/-! ## Inbound -/

private inductive Inbound where
  | none
  | resolve (p : IO.Promise (Except NetError PeerMessage)) (m : PeerMessage)
  | collected (p : IO.Promise (Except NetError (Array PeerMessage))) (ms : Array PeerMessage)
  | burstTooLarge (p : IO.Promise (Except NetError (Array PeerMessage))) (e : NetError)
  | notify (subs : Array PeerStream) (m : PeerMessage)
  | teardown (e : NetError)

private def handleInbound (c : PeerConnection) (command : String) (payload : ByteArray) : IO Unit := do
  if command == "tx" && payload.size > maximumRelayedTransactionBytes then return
  match PeerMessage.decode command payload with
  | .error e => c.teardown (some (.peer (.protocolViolation s!"{command}: {wireErrorText e}")))
  | .ok message =>
    match message with
    | .ping n => discard <| (c.send (.pong n)).attempt
    | .feefilter rate =>
      let subs ← c.state.modifyGet fun st => (st.subscribers, { st with feeFilter := some rate })
      for s in subs do s.yield (.message message)
    | _ =>
      let bytes := payload.size
      let action ← c.state.modifyGet fun st =>
        let isPong := match message with | .pong _ => true | _ => false
        if isPong && !st.pending.any (·.commands.contains "pong") then (Inbound.none, st)
        else match st.pending.find? (·.commands.contains command) with
        | some p => (.resolve p.promise message, { st with pending := st.pending.filter (·.id != p.id) })
        | none =>
          match st.collectors.find? (·.command == command) with
          | some col =>
            let received := col.received.push message
            let receivedBytes := col.receivedBytes + bytes
            if col.maxTotalBytes.any (receivedBytes > ·) then
              (.burstTooLarge col.promise (burstTooLarge command receivedBytes (col.maxTotalBytes.getD 0)),
               { st with collectors := st.collectors.filter (·.id != col.id) })
            else if received.size ≥ col.expected then
              (.collected col.promise received, { st with collectors := st.collectors.filter (·.id != col.id) })
            else (.none, { st with collectors := st.collectors.map fun x =>
              if x.id == col.id then { col with received, receivedBytes } else x })
          | none =>
            if bytes > c.backlogByteLimit then
              (.teardown (.peer (.protocolViolation
                s!"unsolicited {message.command} of {bytes} bytes exceeds the {c.backlogByteLimit}-byte buffer")), st)
            else match message with
              | .block _ | .addr _ => (.none, st)
              | _ =>
                let rec trim (b : Array (PeerMessage × Nat)) (n : Nat) (fuel : Nat) : Array (PeerMessage × Nat) × Nat :=
                  match fuel with
                  | 0 => (b, n)
                  | fuel + 1 =>
                    if b.size > backlogLimit || n > c.backlogByteLimit then trim (b.extract 1 b.size) (n - b[0]!.2) fuel
                    else (b, n)
                let (b, n) := trim (st.backlog.push (message, bytes)) (st.backlogBytes + bytes) (st.backlog.size + 2)
                (.notify st.subscribers message, { st with backlog := b, backlogBytes := n })
      match action with
      | .none => pure ()
      | .resolve p m => p.resolve (.ok m)
      | .collected p ms => p.resolve (.ok ms)
      | .burstTooLarge p e => p.resolve (.error e); c.teardown (some e)
      | .notify subs m => for s in subs do s.yield (.message m)
      | .teardown e => c.teardown (some e)

private partial def drainFrames (c : PeerConnection) : IO Unit := do
  let next ← c.state.modifyGet fun st =>
    if st.didTeardown then (Sum.inl none, st)
    else match st.framer.nextMessage with
      | .error e => (.inl (some e), st)
      | .ok (none, _) => (.inl none, st)
      | .ok (some m, f) => (.inr m, { st with framer := f })
  match next with
  | .inl none => pure ()
  | .inl (some e) => c.teardown (some (.framing e))
  | .inr (command, payload) =>
    c.handleInbound command payload
    c.drainFrames

private partial def receiveLoop (c : PeerConnection) (sock : TCP.Socket.Client) : IO Unit := do
  if (← c.state.get).didTeardown then return
  match ← (sock.recv? ((1 : UInt64) <<< 22)).block.toBaseIO with
  | .error e => c.teardown (some (.peer (.disconnected (toString e))))
  | .ok none => c.teardown (some (.peer (.disconnected "connection closed")))
  | .ok (some chunk) =>
    if chunk.isEmpty then c.teardown (some (.peer (.disconnected "empty read"))); return
    let now ← monoMs
    c.state.modify fun st => { st with lastReceivedAt := now, framer := st.framer.append chunk }
    c.drainFrames
    c.receiveLoop sock

/-! ## Keepalive -/

private partial def keepaliveTick (c : PeerConnection) : IO Unit := do
  let st ← c.state.get
  if st.didTeardown then return
  let silence := (← monoMs) - st.lastReceivedAt
  if silence > c.readIdleTimeoutMs then
    c.teardown (some (.peer (.disconnected s!"no bytes received for {silence / 1000}.{(silence % 1000) / 100} seconds")))
    return
  match ← (c.send (.ping (← randomU64))).attempt with
  | .error e => c.teardown (some e)
  | .ok () => after c.pingIntervalMs c.keepaliveTick

private def startKeepalive (c : PeerConnection) : IO Unit := after c.pingIntervalMs c.keepaliveTick

/-! ## Connect / handshake -/

/-- The socket address for a host (IPv4 or IPv6 literal, else `getaddrinfo`). -/
def resolveAddress (host : String) (port : UInt16) : Async SocketAddress := do
  if let some a := IPv4Addr.ofString host then return .v4 ⟨a, port⟩
  let h := if host.startsWith "[" && host.endsWith "]" then ((host.drop 1).dropEnd 1).toString else host
  if !h.contains '%' then
    if let some a := IPv6Addr.ofString h then return .v6 ⟨a, port⟩
  let addrs ← DNS.getAddrInfo host (toString port)
  let v4 := addrs.find? fun | .v4 _ => true | _ => false
  match v4 <|> addrs[0]? with
  | some (.v4 a) => return .v4 ⟨a, port⟩
  | some (.v6 a) => return .v6 ⟨a, port⟩
  | none => throw (IO.userError s!"no address for {host}")

private def exchangeVersion (c : PeerConnection) (timeoutMs : Nat) : NetM Unit := do
  let version : VersionMessage := {
    version := protocolVersion
    services := c.localServices
    timestamp := Int64.ofInt (← wallSeconds)
    receiver := .unspecified
    sender := .unspecified
    nonce := ← randomU64
    userAgent := userAgent
    startHeight := c.localStartHeight
    relay := c.relayPreference }
  c.send (.version version)
  try
    let theirs ← c.waitFor #["version"] timeoutMs
    let .version v := theirs | throw (.peer (.handshakeFailed "expected version"))
    c.state.modify fun st => { st with peerServices := v.services, peerUserAgent := v.userAgent, peerStartHeight := v.startHeight }
    if v.services &&& nodeCompactFilters == 0 then throw (.peer (.missingCompactFilters v.services))
    -- The peer's verack may already be in the backlog: the waiter consults it first.
    c.send .verack
    discard <| c.waitFor #["verack"] timeoutMs
  catch e =>
    c.teardown (some e)
    throw e
  -- BIP130: headers over inv for block announcements.
  discard <| (c.send .sendheaders).attempt
  c.state.modify fun st => { st with isConnected := true }
  c.startKeepalive

/-! ## SOCKS5 (RFC 1928) -/

def socksReplyDescription (code : UInt8) : String :=
  match code with
  | 0x01 => "general failure" | 0x02 => "connection not allowed by ruleset" | 0x03 => "network unreachable"
  | 0x04 => "host unreachable" | 0x05 => "connection refused" | 0x06 => "TTL expired"
  | 0x07 => "command not supported" | 0x08 => "address type not supported"
  | c => s!"reply code {c}"

/-- Exactly `n` bytes off the proxy, or why not. -/
private partial def recvExactly (sock : TCP.Socket.Client) (n : Nat) (acc : ByteArray := .empty) :
    Async (Except PeerError ByteArray) := do
  if acc.size ≥ n then return .ok acc
  match ← sock.recv? (n - acc.size).toUInt64 with
  | none => return .error (.disconnected "proxy closed the connection")
  | some chunk =>
    if chunk.isEmpty then return .error (.disconnected "empty read from proxy")
    recvExactly sock n (acc ++ chunk)

/-- `negotiateSOCKS5`: the no-authentication greeting, then CONNECT with the destination as a name
(address type 3, unresolved), then the reply and its bound address. A proxy that cannot reach the peer is
the peer being unreachable (`disconnected`), not a protocol fault. -/
def negotiateSOCKS5 (sock : TCP.Socket.Client) (destination : PeerEndpoint) : Async (Except PeerError Unit) := do
  sock.send (ByteArray.mk #[0x05, 0x01, 0x00])
  let chosen ← match ← recvExactly sock 2 with | .ok b => pure b | .error e => return .error e
  unless chosen == ByteArray.mk #[0x05, 0x00] do
    return .error (.handshakeFailed "SOCKS5 proxy refused an unauthenticated connection")
  let name := destination.host.toUTF8
  unless 0 < name.size && name.size ≤ 255 do return .error (.handshakeFailed "SOCKS5 destination name too long")
  sock.send (ByteArray.mk #[0x05, 0x01, 0x00, 0x03, name.size.toUInt8] ++ name ++
    ByteArray.mk #[(destination.port >>> 8).toUInt8, (destination.port &&& 0xFF).toUInt8])
  let head ← match ← recvExactly sock 4 with | .ok b => pure b | .error e => return .error e
  unless head[0]! == 0x05 && head[2]! == 0 do return .error (.handshakeFailed "SOCKS5 proxy returned an invalid reply header")
  let reply := head[1]!
  unless reply == 0 do return .error (.disconnected s!"SOCKS5 proxy: {socksReplyDescription reply}")
  let rest : Except PeerError Nat ← match head[3]! with
    | 0x01 => pure (.ok (4 + 2))
    | 0x04 => pure (.ok (16 + 2))
    | 0x03 => do
      match ← recvExactly sock 1 with
      | .ok len => pure (.ok (len[0]!.toNat + 2))
      | .error e => pure (.error e)
    | _ => pure (.error (.handshakeFailed "SOCKS5 proxy answered with an unknown address type"))
  match rest with
  | .error e => return .error e
  | .ok n => match ← recvExactly sock n with
    | .ok _ => return .ok ()
    | .error e => return .error e

/-- TCP connect (through `socksProxy` when set) + version handshake; `missingCompactFilters` when the peer
cannot serve BIP157. -/
def connect (c : PeerConnection) (timeoutMs : Nat := 20_000) : NetM Unit := do
  let sock ← TCP.Socket.Client.mk
  let ready ← IO.Promise.new
  let go ← c.state.modifyGet fun st =>
    if st.permanentlyClosed then (some false, st)
    else if st.hasConnection then (none, st)
    else (some true, { st with hasConnection := true, socket := some sock, ready := some ready })
  match go with
  | none => return
  | some false => throw (.peer .notConnected)
  | some true => pure ()
  -- through a gateway, the proxy is dialled and the peer named to it inside the same deadline
  let target := c.socksProxy.getD c.endpoint
  let dial ← (do
      let addr ← resolveAddress target.host target.port
      sock.connect addr
      match c.socksProxy with
      | none => return Except.ok ()
      | some _ => negotiateSOCKS5 sock c.endpoint : Async (Except PeerError Unit)).toIO
  discard <| IO.mapTask (t := dial) fun r => ready.resolve (match r with
    | .ok (.ok ()) => .ok ()
    | .ok (.error e) => .error (.peer e)
    | .error e => .error (.peer (.disconnected (toString e))))
  after timeoutMs (ready.resolve (.error (.peer .timeout)))
  match ← IO.wait ready.result? with
  | some (.ok ()) => pure ()
  | some (.error e) => c.teardown (some e); throw e
  | none => let e := NetError.peer (.disconnected "closed"); c.teardown (some e); throw e
  c.state.modify fun st => { st with ready := none, lastReceivedAt := st.lastReceivedAt }
  spawn (c.receiveLoop sock)
  c.exchangeVersion timeoutMs

end PeerConnection
end Winnow.IO
