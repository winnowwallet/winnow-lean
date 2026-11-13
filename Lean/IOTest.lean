import Winnow.IO
import TestKit.Check
import TestKit.FakeNode
import TestKit.Regtest
open Winnow Winnow.Net Winnow.IO Lean TestKit TestKit.Regtest

/-! `io-test`: integration tests of the I/O area against a disposable regtest bitcoind.

Starts `bitcoind -regtest` (temp datadir, random free ports, `-blockfilterindex -peerblockfilters`),
then checks, through the Lean I/O layer only: the handshake; header sync to the node's tip over
several getheaders batches, and the headers.bin round trip; a reorg (invalidateblock + more work) and a
stale equal-work sibling; compact-filter download with a match for a script the test funded, the pinned
filter headers equal to the node's `getblockfilter`, filters.json round trip and a rollback on the
reorg; the mempool window seeing a new transaction; broadcast of a raw transaction the node then holds
in its mempool, a reorg under it making it pending again (rolled back, saved, announced, confirmed again);
peers.json and broadcast.json round trips. Fake peers that never ask for an announced transaction: the
announcement timeout naming each peer, and a relay-only session ending with `seatsGone`. Fake peers that
misbehave or go quiet: a burst past its byte bound, the keepalive and a silent peer, a pool replacing a peer it
lost, and filter votes that split or that one source class carries. Offline policy
checks: HTTP permits and redirects against a local Python server through the curl fetch, seed filtering
and dns-json, the census catalog (the list each build ships). The node is killed by PID at the end, also on failure. -/

def runNet {α} (what : String) (x : NetM α) : IO α := do
  match ← x.attempt with
  | .ok a => return a
  | .error e => throw (IO.userError s!"{what}: {e}")

/-! ## The node -/

def TestKit.Regtest.Node.endpoint (n : Node) : PeerEndpoint := { host := "127.0.0.1", port := n.p2p }

def jsonStr (j : Json) (k : String) : String := (j.getObjValAs? String k).toOption.getD ""

/-! ## Offline checks -/

/-- Every case of the I/O layer's errors (`NetError` and each error it carries) with its `name` and the text the
app shows, as the Swift app words it (the Swift sources at 9cca3fc: PeerConnection, PeerPool, HeaderChain,
FilterSync, RangeScan, TxBroadcaster, RoutedHTTPClient). `FramingError`/`WireError` read as Foundation's default
text and a URLSession failure as `transport`. -/
def errorTexts : List (NetError × String × String) := [
  (.peer .timeout, "timeout",
    "The peer did not answer in time."),
  (.peer .notConnected, "notConnected",
    "The connection to the peer was not open."),
  (.peer (.disconnected "EOF"), "disconnected",
    "The peer disconnected (EOF)."),
  (.peer (.handshakeFailed "no verack"), "handshakeFailed",
    "The peer handshake failed (no verack)."),
  (.peer (.missingCompactFilters 1033), "missingCompactFilters",
    "The peer does not serve compact block filters (services 1033)."),
  (.peer (.protocolViolation "bad inv"), "protocolViolation",
    "The peer violated the protocol (bad inv)."),
  (.framing .badMagic, "badMagic",
    "The operation couldn’t be completed. (WalletCore.FramingError error 0.)"),
  (.framing .badCommand, "badCommand",
    "The operation couldn’t be completed. (WalletCore.FramingError error 1.)"),
  (.framing (.payloadTooLarge 33554433), "payloadTooLarge",
    "The operation couldn’t be completed. (WalletCore.FramingError error 2.)"),
  (.framing (.checksumMismatch "tx"), "checksumMismatch",
    "The operation couldn’t be completed. (WalletCore.FramingError error 3.)"),
  (.headers .doesNotConnect, "doesNotConnect",
    "A peer sent block headers that do not connect to the known Bitcoin chain."),
  (.headers (.invalidTarget 7), "invalidTarget",
    "A peer sent an invalid proof-of-work target at block 7."),
  (.headers (.targetAbovePowLimit 8), "targetAbovePowLimit",
    "A peer sent an impossibly easy proof-of-work target at block 8."),
  (.headers (.insufficientProofOfWork 9), "insufficientProofOfWork",
    "A peer sent a header without enough proof of work at block 9."),
  (.headers (.unexpectedDifficulty 2016), "unexpectedDifficulty",
    "A peer sent the wrong proof-of-work difficulty at block 2016."),
  (.headers (.timestampTooFarInFuture 11), "timestampTooFarInFuture",
    "A peer sent a block header dated too far in the future at block 11."),
  (.headers .reorgWithoutMoreWork, "reorgWithoutMoreWork",
    "A peer offered an older or weaker Bitcoin chain."),
  (.headers (.storageCorrupt "short read"), "storageCorrupt",
    "The saved block-header data is damaged (short read)."),
  (.headers (.storageUnavailable "disk full"), "storageUnavailable",
    "Winnow could not read or save its local block-header data (disk full)."),
  (.headers (.badPeerResponse "empty headers"), "badPeerResponse",
    "A peer returned an invalid block-header response (empty headers)."),
  (.headers (.startMismatch 0 800000), "startMismatch",
    "The stored chain starts at block 0 but this setting needs one starting at 800000."),
  (.headers (.checkpointMismatch 959616), "checkpointMismatch",
    "A peer sent a Bitcoin chain that does not pass through the known block at height 959616."),
  (.headers (.forkBelowCheckpoint 959000), "forkBelowCheckpoint",
    "A peer offered a Bitcoin chain that rewrites settled blocks, from block 959000."),
  (.headers (.timestampNotAfterMedianTime 12), "timestampNotAfterMedianTime",
    "A peer sent a block header dated before the blocks under it at block 12."),
  (.pool .noPeers, "noPeers",
    "No Bitcoin peers are available for block-header sync."),
  (.pool .relayOnly, "relayOnly",
    "Winnow is keeping Bitcoin peers connected only to finish relaying a payment. Resume syncing to download block headers."),
  (.pool (.exhausted 1 "timeout"), "exhausted",
    "Winnow tried 1 Bitcoin peer, but none supplied a usable block-header chain. Last error: timeout"),
  (.pool (.exhausted 3 "timeout"), "exhausted",
    "Winnow tried 3 Bitcoin peers, but none supplied a usable block-header chain. Last error: timeout"),
  (.pool (.allPeersCoolingDown 1 "timeout"), "allPeersCoolingDown",
    "1 Bitcoin peer was slow to answer and is being rested briefly. Syncing will resume on its own. Last error: timeout"),
  (.pool (.allPeersCoolingDown 2 "timeout"), "allPeersCoolingDown",
    "2 Bitcoin peers were slow to answer and are being rested briefly. Syncing will resume on its own. Last error: timeout"),
  (.filters .busy, "busy",
    "Finishing sync. Try loading the payment again in a moment."),
  (.filters .noPeers, "noPeers",
    "No Bitcoin peers are available for compact-filter synchronization."),
  (.filters .relayOnly, "relayOnly",
    "Winnow is keeping Bitcoin peers connected only to finish relaying a payment. Resume syncing to scan for new blocks."),
  (.filters (.crossCheckUnavailable "one source"), "crossCheckUnavailable",
    "Winnow could not check this scan against connections from different sources (one source). Nothing was scanned; it will try again as the peer pool changes."),
  (.filters (.peersCoolingDown 1), "peersCoolingDown",
    "1 Bitcoin peer is resting briefly after a slow reply. Scanning will resume on its own."),
  (.filters (.peersCoolingDown 2), "peersCoolingDown",
    "2 Bitcoin peers are resting briefly after a slow reply. Scanning will resume on its own."),
  (.filters (.checkpointMismatch "split"), "checkpointMismatch",
    "Bitcoin peers disagreed about compact-filter checkpoints (split)."),
  (.filters (.badPeerResponse "missing cfilters"), "badPeerResponse",
    "A Bitcoin peer returned invalid compact-filter data (missing cfilters)."),
  (.filters (.filterHeaderMismatch 12), "filterHeaderMismatch",
    "A compact filter did not match its authenticated header at block 12."),
  (.filters .unexpectedBlockHash, "unexpectedBlockHash",
    "A Bitcoin peer returned a compact filter for a block Winnow did not request."),
  (.filterStorage .unreadable, "unreadable",
    "Winnow could not read its compact-filter progress file. Scanning is stopped so wallet history is not skipped."),
  (.filterStorage (.tooLarge 1048576), "tooLarge",
    "The compact-filter progress file is unexpectedly large (limit: 1048576 bytes). Scanning is stopped."),
  (.filterStorage (.damaged "bad json"), "damaged",
    "The compact-filter progress file is damaged (bad json). Scanning is stopped; Winnow will not replace it automatically."),
  (.filterStorage .writeFailed, "writeFailed",
    "Winnow could not safely save compact-filter progress. The scan frontier was not advanced."),
  (.filterStorage (.frontierBeforeWallet 5 10), "frontierBeforeWallet",
    "Saved compact-filter progress starts at block 5, behind the wallet's required block 10. Scanning is stopped."),
  (.filterStorage (.frontierBeyondTip 20 15), "frontierBeyondTip",
    "Saved compact-filter progress points to block 20, beyond the validated chain tip 15. Scanning is stopped."),
  (.range (.invalidRange 9 3), "invalidRange",
    "Winnow was asked to scan blocks 9 to 3, which is not a range it can scan."),
  (.range .noWatchScripts, "noWatchScripts",
    "A block range scan needs at least one script to look for."),
  (.range (.rangeTooWide 60000 50000), "rangeTooWide",
    "That restore would scan 60000 blocks, past the 50000-block limit for one range."),
  (.range (.tooManyScripts 600 500), "tooManyScripts",
    "That restore looks for 600 scripts, past the limit of 500."),
  (.range (.tooManyIterations 4 1), "tooManyIterations",
    "That restore has already rescanned its range 1 time and asked for pass 4."),
  (.range (.tooManyIterations 4 3), "tooManyIterations",
    "That restore has already rescanned its range 3 times and asked for pass 4."),
  (.range (.filterBytesExhausted 900 800), "filterBytesExhausted",
    "The restore scan reached its data limit (900 of 800 bytes of compact filters). It can be resumed."),
  (.range (.runTimedOut 90000), "runTimedOut",
    "The restore scan reached its time limit (90.0 seconds). It can be resumed."),
  (.range (.rangeBelowChain 5 10), "rangeBelowChain",
    "The restore scan starts at block 5, below block 10, which is the first block Winnow holds a header for."),
  (.range (.rangeAboveChain 30 20), "rangeAboveChain",
    "The restore scan ends at block 30, above the validated chain tip 20."),
  (.range (.rangeSpansNoCheckpoint 100 200), "rangeSpansNoCheckpoint",
    "Blocks 100 to 200 hold no filter checkpoint, and Winnow has no verified filter header below them, so nothing could check what a peer sent. Scan a wider range."),
  (.range .recordUnreadable, "recordUnreadable",
    "Winnow could not read the restore scan's progress file. The scan is stopped so a payment is not skipped."),
  (.range (.recordTooLarge 1048576), "recordTooLarge",
    "The restore scan's progress file is unexpectedly large (limit: 1048576 bytes). The scan is stopped."),
  (.range (.recordDamaged "bad json"), "recordDamaged",
    "The restore scan's progress file is damaged (bad json). The scan is stopped; Winnow will not replace it automatically."),
  (.range .recordWriteFailed, "recordWriteFailed",
    "Winnow could not safely save the restore scan's progress. Nothing was recorded for this batch."),
  (.broadcast .invalidFeeRate, "invalidFeeRate",
    "The transaction fee rate must be a positive, finite number within Bitcoin's monetary range."),
  (.broadcast .stopped, "stopped",
    "This transaction relay session has stopped. Reconnect before changing relay state."),
  (.broadcastStorage .unreadable, "unreadable",
    "Winnow could not read its pending-transaction file. Relay is stopped until local storage is available."),
  (.broadcastStorage (.tooLarge 1048576), "tooLarge",
    "The pending-transaction file is unexpectedly large (limit: 1048576 bytes). Relay is stopped to protect the wallet."),
  (.broadcastStorage (.damaged "bad json"), "damaged",
    "The pending-transaction file is damaged (bad json). Relay is stopped; Winnow will not discard or replay its entries."),
  (.broadcastStorage (.unsupportedVersion 9), "unsupportedVersion",
    "The pending-transaction file uses unsupported version 9. Update Winnow before relaying transactions."),
  (.broadcastStorage .writeFailed, "writeFailed",
    "Winnow could not safely save pending transaction state. The relay change was not accepted."),
  (.wire (.truncated 4 1), "truncated",
    "The operation couldn’t be completed. (WalletCore.WireError error 0.)"),
  (.wire (.trailingBytes 2), "trailingBytes",
    "The operation couldn’t be completed. (WalletCore.WireError error 1.)"),
  (.wire .invalidVarInt, "invalidVarInt",
    "The operation couldn’t be completed. (WalletCore.WireError error 2.)"),
  (.wire (.malformed "bad script"), "malformed",
    "The operation couldn’t be completed. (WalletCore.WireError error 3.)"),
  (.http .unavailable, "unavailable",
    "Network request failed: unavailable."),
  (.http .response, "response",
    "Network request failed: response."),
  (.http .tooLarge, "tooLarge",
    "Network request failed: tooLarge."),
  (.http .redirect, "redirect",
    "Network request failed: redirect."),
  (.http (.status 503), "HTTPFailure",
    "The server returned HTTP 503."),
  (.http (.transport "offline"), "URLError",
    "The network request failed (offline)."),
  (.http .cancelled, "cancelled",
    "The request was cancelled."),
  (.cancelled, "cancelled",
    "The operation was cancelled."),
  (.other "socket closed", "other",
    "socket closed")]

/-- Swift's `"\(error)"` for a `WireError`, which a peer's protocol violation quotes (`wireErrorText`). -/
def wireTexts : List (Winnow.WireError × String) := [
  (.truncated 4 1, "truncated(expected: 4, remaining: 1)"),
  (.trailingBytes 2, "trailingBytes(2)"),
  (.invalidVarInt, "invalidVarInt"),
  (.malformed "bad script", "malformed(\"bad script\")")]

/-- `errorTexts` and `wireTexts`: each case's name and the text the app shows. -/
def errorTextChecks : IO Unit := do
  for (e, name, text) in errorTexts do
    check s!"error name: {name}" (e.name == name) e.name
    check s!"error text: {name}" (e.description == text) e.description
  for (w, text) in wireTexts do
    check s!"wire error text: {w.name}" (wireErrorText w == text) (wireErrorText w)

def offlineChecks (dir : String) : IO Unit := do
  errorTextChecks
  say "policy (offline)"
  -- Seed filtering and IP literals (BSD inet_pton)
  check "inet_pton4 refuses leading zeros" ((inetPton4 "01.2.3.4").isNone && (inetPton4 "1.2.3.4").isSome)
  check "inet_pton6 forms" ((inetPton6 "::1").isSome && (inetPton6 "2001:db8::1").isSome &&
    (inetPton6 "::ffff:1.2.3.4").isSome && (inetPton6 "1:2:3:4:5:6:7:8:9").isNone && (inetPton6 ":::").isNone)
  check "seed filter drops private answers" (!SeedAddressFilter.accepts "10.0.0.1" false &&
    SeedAddressFilter.accepts "10.0.0.1" true && SeedAddressFilter.accepts "8.8.8.8" false &&
    !SeedAddressFilter.accepts "::ffff:192.168.1.1" false && !SeedAddressFilter.accepts "fe80::1" false &&
    !SeedAddressFilter.accepts "seed.example" true)
  check "netblock" (netblock "8.8.4.4" == some "v4:8.8" && netblock "127.0.0.1" == none &&
    netblock "2a01:4f8::1" == some "v6:2a01:04f8" && netblock "::ffff:8.8.8.8" == some "v4:8.8")
  let dnsBody := "{\"Status\":0,\"Answer\":[{\"name\":\"x\",\"type\":5,\"data\":\"y.\"},{\"type\":1,\"data\":\" 1.2.3.4 \"},{\"type\":28,\"data\":\"2a01::1\"}]}"
  check "dns-json answers" ((DNSJSON.hosts dnsBody.toUTF8).toOption == some #["1.2.3.4", "2a01::1"])
  check "dns-json non-zero status" ((DNSJSON.hosts "{\"Status\":3}".toUTF8).toOption == some #[])
  let stub : SeedResolver := { lookup := fun h p _ => pure #[{ host := h ++ ".1", port := p }, { host := "dup", port := p }] }
  let seeds ← stub.resolveSeeds #["a", "b"] 8333 false
  check "resolveSeeds dedupes" (seeds.size == 3)
  let sys ← SeedResolver.getaddrinfo "localhost" 8333
  check "getaddrinfo resolves localhost" (sys.any (·.host == "127.0.0.1") || sys.any (·.host == "::1")) s!"{sys.map (·.host)}"
  check "seed endpoints keep loopback only with allowPrivate"
    ((SeedResolver.endpoints #["127.0.0.1", "127.0.0.1", "8.8.8.8"] 1 false).size == 1 &&
     (SeedResolver.endpoints #["127.0.0.1", "127.0.0.1", "8.8.8.8"] 1 true).size == 2)
  -- Diversity
  let pol : DiversityPolicy := { peerCount := 3 }
  let c (h : String) (s : PeerSource) : PeerCandidate := { endpoint := { host := h, port := 8333 }, source := s }
  check "diversity: one netblock once" (!pol.admits (c "8.8.1.1" .census) #[c "8.8.2.2" .dnsSeed])
  check "diversity: a class may not hold every seat"
    (!pol.admits (c "9.9.9.9" .census) #[c "1.1.1.1" .census, c "2.2.2.2" .census] &&
      pol.admits (c "9.9.9.9" .manual) #[c "1.1.1.1" .manual, c "2.2.2.2" .manual])
  check "cooldown doubles to the cap" (PeerPool.cooldown 1 == 30_000 && PeerPool.cooldown 2 == 60_000 &&
    PeerPool.cooldown 5 == 480_000 && PeerPool.cooldown 6 == 600_000 && PeerPool.cooldown 40 == 600_000)
  check "rebroadcast backoff" (TxBroadcaster.backoffInterval 0 60 3600 == 60 && TxBroadcaster.backoffInterval 5 60 3600 == 1920 &&
    TxBroadcaster.backoffInterval 6 60 3600 == 3600)
  -- peers.json formats
  let legacy := "[{\"host\":\"1.2.3.4\",\"port\":8333}]".toUTF8
  check "peers.json legacy array reads as persisted"
    ((PersistedPeers.decode legacy).map (·.map (·.source)) == some #[.persisted])
  let enc := PersistedPeers.encode #[c "1.2.3.4" .dnsSeed, c "::1" .manual]
  check "peers.json v2 encodes as JSONEncoder does"
    (String.fromUTF8! enc == "{\"version\":2,\"peers\":[{\"host\":\"1.2.3.4\",\"port\":8333,\"source\":\"dnsSeed\"},{\"host\":\"::1\",\"port\":8333,\"source\":\"manual\"}]}")
  check "peers.json v2 round trip" (PersistedPeers.decode enc == some #[c "1.2.3.4" .dnsSeed, c "::1" .manual])
  let censusEnc := PersistedPeers.encode #[c "5.6.7.8" .census]
  check "a census peer keeps the legacy source name \"fallback\""
    (((String.fromUTF8! censusEnc).splitOn "\"source\":\"fallback\"").length == 2 &&
      PersistedPeers.decode censusEnc == some #[c "5.6.7.8" .census])
  check "peers.json other versions are refused" ((PersistedPeers.decode "{\"version\":3,\"peers\":[]}".toUTF8).isNone)
  -- HTTP policy
  check "permits" (permits "https://1.1.1.1/dns-query" && permits "http://a:8080/x" && !permits "ftp://a/x" &&
    !permits "https://user@a/x" && !permits "https:///x" && !permits "http://a:0/" && !permits "http://a:70000/")
  let a := (parseURL "https://Census.example/p").get!
  check "redirect rules" (followsRedirect a (parseURL "https://census.example/q").get! &&
    !followsRedirect a (parseURL "http://census.example/q").get! && !followsRedirect a (parseURL "https://other.example/").get!)
  -- A local server for the curl fetch.
  let script := s!"{dir}/http_server.py"
  IO.FS.writeFile script ("import http.server, sys\n" ++
    "class H(http.server.BaseHTTPRequestHandler):\n" ++
    "    def log_message(self, *a): pass\n" ++
    "    def do_GET(self):\n" ++
    "        port = self.server.server_address[1]\n" ++
    "        if self.path == '/ok': self.reply(200, b'hello')\n" ++
    "        elif self.path == '/big': self.reply(200, b'x' * 5000)\n" ++
    "        elif self.path == '/accept': self.reply(200, (self.headers.get('Accept') or '').encode())\n" ++
    "        elif self.path == '/same': self.redirect('/ok')\n" ++
    "        elif self.path == '/other': self.redirect('http://localhost:%d/ok' % port)\n" ++
    "        else: self.reply(404, b'no')\n" ++
    "    def reply(self, code, body):\n" ++
    "        self.send_response(code); self.send_header('Content-Length', str(len(body))); self.end_headers(); self.wfile.write(body)\n" ++
    "    def redirect(self, loc):\n" ++
    "        self.send_response(302); self.send_header('Location', loc); self.send_header('Content-Length', '0'); self.end_headers()\n" ++
    "s = http.server.HTTPServer(('127.0.0.1', 0), H)\n" ++
    "print(s.server_address[1], flush=True)\n" ++
    "s.serve_forever()\n")
  let server ← IO.Process.spawn { cmd := "python3", args := #["-I", script], stdout := .piped, stderr := .null, stdin := .null }
  try
    let port := (← server.stdout.getLine).trimAscii.toString
    let client ← RoutedHTTPClient.new (curlFetch "/usr/bin/curl")
    let base := s!"http://127.0.0.1:{port}"
    let r1 ← (client.get s!"{base}/ok" 100).attempt
    check "http 200" (match r1 with | .ok b => b == "hello".toUTF8 | .error _ => false)
    let r2 ← (client.get s!"{base}/big" 4999).attempt
    check "http body over the cap is tooLarge" (match r2 with | .error (.http .tooLarge) => true | _ => false)
    let r2b ← (client.get s!"{base}/big" 5000).attempt
    check "http body at the cap is accepted" (match r2b with | .ok b => b.size == 5000 | _ => false)
    let r3 ← (client.get s!"{base}/same" 100).attempt
    check "same-host redirect followed" (match r3 with | .ok b => b == "hello".toUTF8 | .error _ => false)
    let r4 ← (client.get s!"{base}/other" 100).attempt
    check "cross-host redirect refused as HTTP 302" (match r4 with | .error (.http (.status 302)) => true | _ => false)
    let r5 ← (client.get s!"{base}/missing" 100).attempt
    check "http 404" (match r5 with | .error (.http (.status 404)) => true | _ => false)
    let r6 ← (client.get s!"{base}/accept" 100 (accept := some "application/dns-json")).attempt
    check "accept header sent" (match r6 with | .ok b => b == "application/dns-json".toUTF8 | _ => false)
    client.cancel
    let r7 ← (client.get s!"{base}/ok" 100).attempt
    check "cancelled client refuses" (match r7 with | .error (.http .unavailable) => true | _ => false)
  finally
    server.kill
  -- The census catalog (shipped with each build: no signature, no expiry).
  let now ← wallSeconds
  let today := now / 86_400
  let civil (days : Int) : String := Id.run do
    -- civil_from_days
    let z := days + 719468
    let era := (if z ≥ 0 then z else z - 146096) / 146097
    let doe := z - era * 146097
    let yoe := (doe - doe / 1460 + doe / 36524 - doe / 146096) / 365
    let y := yoe + era * 400
    let doy := doe - (365 * yoe + yoe / 4 - yoe / 100)
    let mp := (5 * doy + 2) / 153
    let d := doy - (153 * mp + 2) / 5 + 1
    let m := if mp < 10 then mp + 3 else mp - 9
    let y := if m ≤ 2 then y + 1 else y
    let p2 (x : Int) := if x < 10 then s!"0{x}" else toString x
    return s!"{y}-{p2 m}-{p2 d}"
  let entry (h : String) := s!"\{\"host\":\"{h}\",\"port\":8333,\"userAgent\":\"/Satoshi:28.0.0/\",\"startHeight\":900000}"
  let doc (date : String) (hosts : List String) :=
    s!"\{\"schemaVersion\":1,\"date\":\"{date}\",\"tip\":900010,\"networks\":\{\"clearnet\":[{",".intercalate (hosts.map entry)}],\"tor\":[]}}"
  let good := doc (civil today) ["9.9.9.9", "::FFFF:8.8.8.8", "2a01:4f8:0:0::1"]
  match CensusCatalog.decode good.toUTF8 with
  | .ok cat => check "census validates and canonicalizes" ((cat.clearnet.map (·.map (·.host))) == some #["2a01:4f8::1", "8.8.8.8", "9.9.9.9"])
                 s!"{cat.clearnet.map (·.map (·.host))}"
  | .error e => check "census validates and canonicalizes" false e.name
  let nameOf (r : Except CensusError CensusCatalog) := match r with | .ok _ => "ok" | .error e => e.name
  check "census of any age validates (no expiry)" (nameOf (CensusCatalog.decode (doc (civil (today - 400)) ["9.9.9.9"]).toUTF8) == "ok")
  check "census dated ahead validates (no clock)" (nameOf (CensusCatalog.decode (doc (civil (today + 1)) ["9.9.9.9"]).toUTF8) == "ok")
  check "census duplicate" (nameOf (CensusCatalog.decode (doc (civil today) ["9.9.9.9", "::ffff:9.9.9.9"]).toUTF8) == "duplicate")
  check "census diversity" (nameOf (CensusCatalog.decode (doc (civil today) ["9.9.9.9", "9.9.1.1"]).toUTF8) == "diversity")
  check "census private host" (nameOf (CensusCatalog.decode (doc (civil today) ["192.168.1.1"]).toUTF8) == "endpoint")
  check "census thin" (nameOf (CensusCatalog.decode (doc (civil today) ["9.9.9.9"]).toUTF8 (minimumEntries := 50)) == "thin")
  check "census bad date" (CensusCatalog.day "2026-02-30" == none && CensusCatalog.day "2026-10-26" == some 20752)
  check "no bundled census outside an app bundle" (← CensusCatalog.bundled).isNone
  -- After Settings → Reset peers the rebuilt pool is told which peers it had (`avoidOnReset`): they are the
  -- census entries it dials last, after every other one; the manual peer, then the remembered one, still
  -- come first (`PeerPool.localCandidates`). Census entries are mainnet's: port 8333, one per netblock.
  let censusHosts := ["9.9.9.9", "8.8.8.8", "1.1.1.1", "4.2.2.2", "208.67.222.222", "64.6.64.6", "77.88.8.8", "94.140.14.14"]
  match CensusCatalog.decode (doc (civil today) censusHosts).toUTF8 with
  | .error e => check "reset order: the census list" false e.name
  | .ok census =>
    let at8333 (h : String) : PeerEndpoint := { host := h, port := 8333 }
    let manual := at8333 "185.70.40.1"
    let remembered := at8333 "51.15.0.1"
    let had := [at8333 "1.1.1.1", at8333 "77.88.8.8"]
    let peersFile := System.FilePath.mk dir / "reset-order-peers.json"
    IO.FS.writeBinFile peersFile (PersistedPeers.encode #[{ endpoint := remembered, source := .persisted }])
    let pool ← PeerPool.new NetworkParams.mainnet (manualPeers := #[manual]) (peersFile := some peersFile)
      (censusCatalog := some census) (avoidOnReset := had.toArray) (seedResolver := some { lookup := fun _ _ _ => pure #[] })
    -- the census is shuffled per round: twenty rounds, so an avoided peer dialled early would show
    let mut orders : Array (List PeerCandidate) := #[]
    for _ in [0:20] do orders := orders.push (← pool.localCandidates {}).toList
    let ok (order : List PeerCandidate) : Bool :=
      let census := order.drop 2
      order.take 2 == [{ endpoint := manual, source := .manual }, { endpoint := remembered, source := .persisted }] &&
      census.length == censusHosts.length && census.all (·.source == .census) &&
      ((census.drop (censusHosts.length - had.length)).map (·.endpoint)).all had.contains
    let bad := orders.find? (!ok ·)
    check "reset order: manual, remembered, the other census peers, then the census peers it had"
      bad.isNone s!"{(bad.getD []).map (·.endpoint.description)}"
    let firsts := (orders.map fun o => ((o.drop 2).take 1).map (·.endpoint)).toList.eraseDups.length
    check "reset order: the other census peers still in shuffled order" (firsts > 1) s!"{firsts} first choices"
    -- a peer it had that is already connected (or cooling off) is left out like any other
    let excluded ← pool.localCandidates (({} : Std.HashSet PeerEndpoint).insert (at8333 "1.1.1.1"))
    check "reset order: an excluded peer it had is not dialled"
      (excluded.size == censusHosts.length + 1 && !excluded.any (·.endpoint == at8333 "1.1.1.1") &&
       excluded.back?.map (·.endpoint) == some (at8333 "77.88.8.8"))
      s!"{excluded.map (·.endpoint.description)}"
  -- FilterSyncTests.overlayDeadlines: Tor and I2P peers get longer filter and block deadlines
  check "deadline: 100 clearnet filters, 30 s" (FilterSync.chunkTimeoutSeconds 100 == 30)
  check "deadline: 1000 clearnet filters, 120 s" (FilterSync.chunkTimeoutSeconds 1_000 == 120)
  check "deadline: 100 overlay filters, 120 s" (FilterSync.chunkTimeoutSeconds 100 (overlay := true) == 120)
  check "deadline: 1000 overlay filters, 1200 s" (FilterSync.chunkTimeoutSeconds 1_000 (overlay := true) == 1_200)
  check "deadline: a clearnet block keeps its 120 s" (FilterSync.blockTimeoutMs 120_000 false == 120_000)
  check "deadline: an overlay block gets at least 300 s" (FilterSync.blockTimeoutMs 30_000 true == 300_000)
  check "deadline: a longer overlay block deadline stands" (FilterSync.blockTimeoutMs 600_000 true == 600_000)
  -- FilterSync.frontier on a headers-only chain: nothing scanned, then the genesis block scanned
  let pool ← PeerPool.new NetworkParams.regtest (seedResolver := some { lookup := fun _ _ _ => pure #[] })
  let store ← match ← (HeaderStore.open NetworkParams.regtest none).toBaseIO with
    | .ok s => pure s | .error e => throw (IO.userError s!"headers: {e}")
  let open? (start : UInt32) : IO FilterSyncIO := do
    match ← (FilterSyncIO.new pool store start).toBaseIO with
    | .ok f => pure f | .error e => throw (IO.userError s!"filters: {e}")
  check "frontier: nothing scanned has no hash" ((← (← open? 0).frontier) == (0, none))
  check "frontier: the hash of the last block scanned" ((← (← open? 1).frontier) == (1, ← store.blockHash 0) &&
    (← store.blockHash 0).isSome)
  let _ := dir

/-! ## Against the node -/

def regtest := NetworkParams.regtest
def noSeeds : SeedResolver := { lookup := fun _ _ _ => pure #[] }

/-- Collects a stream's elements on a thread of its own. -/
def collect {α ε} (s : EventStream α ε) : IO (IO.Ref (Array α)) := do
  let r ← IO.mkRef #[]
  spawn do
    repeat
      match ← s.next with
      | .value a => r.modify (·.push a)
      | .finished _ => break
  return r

def scriptOf (n : Node) (addr : String) : IO ByteArray := do
  let info ← Json.parse (← n.wallet #["getaddressinfo", addr]) |> IO.ofExcept
  return ofHex! (jsonStr info "scriptPubKey")

def nodeFilterHeader (n : Node) (height : Nat) : IO String := do
  let hash ← n.cli #["getblockhash", toString height]
  let j ← n.json #["getblockfilter", hash]
  return jsonStr j "header"

/-! ## A scripted fake peer (Lean TCP server) for the failure paths -/

inductive FakeMode where
  /-- Accepts and never speaks. -/
  | silent
  /-- Answers version without NODE_COMPACT_FILTERS. -/
  | noFilters
  /-- Speaks the wrong network magic. -/
  | badMagic
  /-- Handshakes, then answers getheaders with one header that does not connect. -/
  | strayHeader
  /-- Handshakes, then never answers. -/
  | mute

def fakePeer (mode : FakeMode) : IO UInt16 := do
  let server ← Std.Async.TCP.Socket.Server.mk
  server.bind (.v4 ⟨Std.Net.IPv4Addr.ofParts 127 0 0 1, 0⟩)
  server.listen 8
  let port := (← server.getSockName).port
  spawn do
    let keep := server
    let sock ← keep.accept.block
    let magic := regtest.magic
    let send (m : PeerMessage) : IO Unit :=
      (sock.send (MessageFramer.frame m.command m.payload (if mode matches .badMagic then ofHex! "deadbeef" else magic))).block
    let version (services : UInt64) : PeerMessage := .version {
      version := 70016
      services := services
      timestamp := 0
      receiver := .unspecified
      sender := .unspecified
      nonce := 7
      userAgent := "/fake:0/"
      startHeight := 0
      relay := false }
    let mut framer : MessageFramer := { magic }
    let mut alive := true
    while alive do
      let some chunk ← (sock.recv? 65536).block | break
      framer := framer.append chunk
      repeat
        match framer.nextMessage with
        | .ok (some (cmd, payload), f) =>
          framer := f
          match mode, cmd with
          | .silent, _ => pure ()
          | .noFilters, "version" => send (version 0); send .verack
          | .badMagic, "version" => send (version 64)
          | .strayHeader, "version" | .mute, "version" => send (version 64); send .verack
          | .strayHeader, "getheaders" =>
            let h := BlockHeader.mk' 1 (ByteArray.mk (Array.replicate 32 9)) (ByteArray.mk (Array.replicate 32 1)) 1 0x207fffff 0
            send (.headers #[h])
          | _, _ => pure ()
          let _ := payload
        | .ok (none, _) => break
        | .error _ => alive := false; break
    discard <| sock.shutdown.toIO
  return port

/-- Upstream `PeerClosedRequestTests.closedPeerDoesNotWait` (#176): a request on a closed peer fails with
`notConnected` within the polling budget, long before its 90 s response deadline. -/
def closedPeerChecks : IO Unit := do
  for collectMany in [false, true] do
    let peer ← PeerConnection.new { host := "127.0.0.1", port := 1 } NetworkParams.signet
    peer.disconnect
    let outcome ← IO.mkRef (none : Option (Except NetError Unit))
    spawn do
      let r ← (if collectMany then
          discard <| peer.requestMany (.ping 1) "pong" 1 (timeoutMs := 90_000)
        else discard <| peer.request (.ping 1) #["pong"] (timeoutMs := 90_000)).attempt
      outcome.set (some r)
    let done ← waitUntil 5_000 (do return (← outcome.get).isSome)
    let kind := if collectMany then "requestMany" else "request"
    check s!"a closed peer fails without waiting for its response deadline ({kind})"
      (done && (match ← outcome.get with | some (.error (.peer .notConnected)) => true | _ => false))
      (match ← outcome.get with | some (.error e) => e.description | some (.ok ()) => "accepted" | none => "still waiting")

/-- A canonical one-input, one-output transaction without a witness, spending a made-up coin: fake peers
never look inside. -/
def fakeRawTx (tag : UInt8) : ByteArray :=
  ofHex! "0200000001" ++ ByteArray.mk (Array.replicate 32 tag) ++ ofHex! "00000000" ++ ofHex! "00ffffffff" ++
    ofHex! "01e803000000000000" ++ ofHex! "0151" ++ ofHex! "00000000"

/-! ## Peers that misbehave or go quiet -/

def filled (size : Nat) (tag : UInt8) : ByteArray := ByteArray.mk (Array.replicate size tag)

def connectedTo (e : PeerEndpoint) (pingIntervalMs : Nat := 60_000) (readIdleTimeoutMs : Nat := 150_000) :
    IO PeerConnection := do
  let c ← PeerConnection.new e regtest (pingIntervalMs := pingIntervalMs) (readIdleTimeoutMs := readIdleTimeoutMs)
  runNet "connect" (c.connect 5_000)
  return c

/-- A peer past `requestMany`'s byte bound (`burstTooLarge`), which is what limits what a peer can make us
hold: exactly at the bound the burst arrives, and one byte under it the connection goes. -/
def burstChecks : IO Unit := do
  let filter : PeerMessage := .cfilter { blockHash := filled 32 7, filter := filled 1_000 8 }
  let burst := 3 * filter.payload.size
  let node ← fakeNode regtest (answer := fun send m => do
    if m matches .getcfilters _ then for _ in [0:3] do send filter)
  let ask (c : PeerConnection) (limit : Nat) :=
    c.requestMany (.getcfilters { startHeight := 0, stopHash := filled 32 0 }) "cfilter" 3 (timeoutMs := 5_000)
      (maxTotalBytes := some limit)
  let fits ← connectedTo node
  let got ← (ask fits burst).attempt
  check "a burst exactly at its byte bound arrives" (match got with | .ok ms => ms.size == 3 | _ => false)
    (match got with | .error e => e.description | .ok ms => s!"{ms.size} messages")
  check "that peer stays connected" (← fits.isConnected)
  fits.disconnect
  let over ← connectedTo node
  let refused ← (ask over (burst - 1)).attempt
  check "a burst one byte past its bound is a protocol violation"
    (match refused with
     | .error (.peer (.protocolViolation why)) => why == s!"cfilter burst of {burst} bytes exceeds the {burst - 1}-byte bound"
     | _ => false)
    (match refused with | .error e => e.description | .ok _ => "accepted")
  check "and it tears the connection down" (!(← over.isConnected))

/-- The keepalive (`keepaliveTick`): pings on its interval hold a quiet connection open while the peer
answers, and a peer that stops is torn down once `readIdleTimeoutMs` passes, failing what waits on it. -/
def keepaliveChecks : IO Unit := do
  let pings ← IO.mkRef 0
  let answering ← fakeNode regtest (answer := fun _ m => do if m matches .ping _ then pings.modify (· + 1))
  let alive ← connectedTo answering (pingIntervalMs := 100) (readIdleTimeoutMs := 1_500)
  IO.sleep 2_000
  check "a peer answering the keepalive outlives the idle timeout" (← alive.isConnected)
  check "the keepalive pings on its interval" ((← pings.get) ≥ 3) s!"{← pings.get} pings in two seconds"
  alive.disconnect
  let silent ← fakeNode regtest (pongs := false)
  let quiet ← connectedTo silent (pingIntervalMs := 100) (readIdleTimeoutMs := 1_500)
  let start ← IO.monoMsNow
  let waiting ← IO.mkRef (none : Option (Except NetError PeerMessage))
  spawn do waiting.set (some (← (quiet.request (.ping 1) #["pong"] (timeoutMs := 30_000)).attempt))
  let gone ← waitUntil 8_000 (do return !(← quiet.isConnected)) (every := 20)
  let took := (← IO.monoMsNow) - start
  check "a silent peer is torn down after the idle timeout" (gone && took ≥ 1_450) s!"{took} ms"
  discard <| waitUntil 2_000 (do return (← waiting.get).isSome) (every := 20)
  check "what waited on it fails, naming the silence"
    (match ← waiting.get with
     | some (.error (.peer (.disconnected why))) => why.startsWith "no bytes received for"
     | _ => false)
    (match ← waiting.get with | some (.error e) => e.description | some (.ok _) => "answered" | none => "still waiting")

/-- A pool that loses its peer dials another (`pruneAndReplenish`, on the monitor's interval). -/
def replenishChecks : IO Unit := do
  let hangUpA ← IO.Promise.new (α := Unit)
  let hangUpB ← IO.Promise.new (α := Unit)
  let a ← fakeNode regtest (hangUp := some hangUpA)
  let b ← fakeNode regtest (hangUp := some hangUpB)
  let pool ← PeerPool.new regtest (peerCount := 1) (manualPeers := #[a, b]) (seedResolver := some noSeeds)
    (monitorIntervalMs := 100)
  pool.start
  discard <| waitUntil 5_000 (do return (← pool.connectedPeers).size == 1)
  let first := (← pool.connectedPeers).map (·.endpoint)
  (if first == #[a] then hangUpA else hangUpB).resolve ()
  let other := if first == #[a] then b else a
  let moved ← waitUntil 10_000 do
    let peers ← pool.connectedPeers
    return peers.map (·.endpoint) == #[other] && (← peers.allM (·.isConnected))
  check "a pool that loses its peer dials another" moved
    s!"on {(← pool.connectedPeers).map (·.endpoint.description)}"
  pool.stop

/-- Regtest headers on genesis, for a chain tall enough to have filter checkpoints. -/
def minedHeaders (count : Nat) : Array BlockHeader := Id.run do
  let mut previous := HeaderChain.genesisHeader regtest
  let mut out := #[]
  for i in [0:count] do
    let time := regtest.genesisTime + (i.toUInt32 + 1) * 600
    let mut nonce : UInt32 := 0
    let mut h := BlockHeader.mk' 1 previous.hash (filled 32 0) time regtest.genesisBits nonce
    while !(HeaderChain.checkedWork h regtest 1).isOk do
      nonce := nonce + 1
      h := BlockHeader.mk' 1 previous.hash (filled 32 0) time regtest.genesisBits nonce
    out := out.push h
    previous := h
  return out

/-- A peer with no headers to give, answering the filter questions with these tags as its filter data. -/
def filterAnswers (checkpoint cfheader : UInt8) (send : PeerMessage → IO Unit) : PeerMessage → IO Unit
  | .getheaders _ => send (.headers #[])
  | .getcfcheckpt r => send (.cfcheckpt { stopHash := r.stopHash, filterHeaders := #[filled 32 checkpoint] })
  | .getcfheaders r =>
    send (.cfheaders { stopHash := r.stopHash, previousFilterHeader := filled 32 0, filterHashes := #[filled 32 cfheader] })
  | _ => pure ()

/-- Peers that disagree about filters, through a real `sync`. Two manual peers and a remembered one on `::1`
make two source classes, and a vote carried by one class alone is `refuseDisputedVote`: everyone is cooled off
and nobody is condemned, since one channel's word can't say who lied. -/
def voteChecks (dir : String) : IO Unit := do
  let store ← runNet "vote headers" (HeaderStore.open regtest none)
  discard <| runNet "vote chain" (store.connect (minedHeaders 1_000))
  let syncOn (pool : PeerPool) (seats : Nat) : IO (Except NetError Unit) := do
    let seated ← waitUntil 10_000 (do return (← pool.connectedPeers).size == seats)
    check s!"vote: {seats} peers seated" seated s!"{(← pool.connectedPeers).size}"
    let filters ← runNet "vote filters" (FilterSyncIO.new pool store 0)
    (filters.sync #[] (onMatch := fun _ => pure ())).attempt
  let mismatch (r : Except NetError Unit) (reason : String) : Bool :=
    match r with | .error (.filters (.checkpointMismatch why)) => why == reason | _ => false
  let show' (r : Except NetError Unit) := match r with | .error e => e.description | .ok () => "synced"
  -- no majority: two peers, two answers
  let a ← fakeNode regtest (startHeight := 1_000) (answer := filterAnswers 1 1)
  let b ← fakeNode regtest (startHeight := 1_000) (answer := filterAnswers 2 1)
  let split ← PeerPool.new regtest (peerCount := 2) (manualPeers := #[a, b]) (seedResolver := some noSeeds)
  split.start
  let r ← syncOn split 2
  check "vote: two peers disagree on a checkpoint, and the sync is refused"
    (mismatch r "no cfcheckpt majority across 2 peers") (show' r)
  check "vote: both are dropped and refused"
    ((← split.connectedPeers).isEmpty && (← split.rejectionReason a) == some "cfcheckpt no majority" &&
     (← split.rejectionReason b) == some "cfcheckpt no majority" && !(← split.knownGood).contains a)
  split.stop
  let threePeers (name : String) (x y z : UInt8 × UInt8) : IO (PeerPool × PeerEndpoint × PeerEndpoint × PeerEndpoint) := do
    -- at our height: a peer far below it is evicted as stale before any vote
    let manualA ← fakeNode regtest (startHeight := 1_000) (answer := filterAnswers x.1 x.2)
    let manualB ← fakeNode regtest (startHeight := 1_000) (answer := filterAnswers y.1 y.2)
    let remembered ← fakeNode regtest (v6 := true) (startHeight := 1_000) (answer := filterAnswers z.1 z.2)
    let file : System.FilePath := s!"{dir}/{name}-peers.json"
    IO.FS.writeBinFile file (PersistedPeers.encode #[{ endpoint := remembered, source := .persisted }])
    let pool ← PeerPool.new regtest (peerCount := 3) (manualPeers := #[manualA, manualB]) (peersFile := some file)
      (seedResolver := some noSeeds)
    pool.start
    return (pool, manualA, manualB, remembered)
  let allCooled (pool : PeerPool) (peers : List PeerEndpoint) (reason : String) : IO Bool := do
    let judged ← peers.allM fun e => do
      return (← pool.isCoolingDown e) && (← pool.rejectionReason e) == some reason
    return judged && (← pool.connectedPeers).isEmpty
  -- a class outvotes another on the checkpoint
  let (pool, x, y, z) ← threePeers "checkpoint-vote" (1, 1) (1, 1) (2, 1)
  let r ← syncOn pool 3
  let reason := "cfcheckpt: one source class outvotes another"
  check "vote: one class outvoting another on a checkpoint is refused" (mismatch r reason) (show' r)
  check "vote: all three are cooled off" (← allCooled pool [x, y, z] reason)
  check "vote: and the remembered peer stays remembered" ((← pool.knownGood).contains z)
  pool.stop
  -- the same on the filter headers, the checkpoint agreed
  let (pool, x, y, z) ← threePeers "cfheaders-vote" (1, 1) (1, 1) (1, 2)
  let r ← syncOn pool 3
  let reason := "cfheaders at 0: one source class outvotes another"
  check "vote: one class outvoting another on filter headers is refused" (mismatch r reason) (show' r)
  check "vote: all three are cooled off again" (← allCooled pool [x, y, z] reason)
  pool.stop
  -- a majority spanning both classes is evidence, so its dissenter alone goes
  let (pool, x, y, z) ← threePeers "spanning-vote" (1, 1) (2, 1) (1, 1)
  let _ ← syncOn pool 3
  check "vote: a majority across classes condemns its dissenter"
    ((← pool.rejectionReason y) == some "cfcheckpt mismatch" && !(← pool.knownGood).contains y)
    s!"{← pool.rejectionReason y}"
  check "vote: and leaves the majority alone" (!(← pool.isCoolingDown x) && !(← pool.isCoolingDown z))
  pool.stop

/-- The window frees a txid when its fetch fails, so another peer's announcement fetches it: without this a
payment isn't seen until the next block (`handleNotfound`, `sendFailed`). -/
def mempoolRefetchChecks : IO Unit := do
  let tx ← match Transaction.decode (fakeRawTx 1) with
    | .ok t => pure t
    | .error _ => throw (IO.userError "fakeRawTx does not decode")
  let script := (tx.outputs[0]!).scriptPubKey
  let a : PeerEndpoint := { host := "127.0.0.1", port := 1 }
  let b : PeerEndpoint := { host := "127.0.0.1", port := 2 }
  let vectors : Array InventoryVector := #[{ type := InventoryType.tx, hash := tx.txid }]
  let announced : PeerMessage := .inv { vectors }
  let opened : MempoolWindow := (({ watchScripts := Std.HashSet.ofList [script] } : MempoolWindow).start).1
  let askedOf (es : Array MempoolEffect) : Array PeerEndpoint :=
    es.filterMap fun | .sendGetData p _ => some p | _ => none
  let paid (es : Array MempoolEffect) : Bool :=
    es.any fun | .emit (.paymentSeen _ amount _) => amount == 1_000 | _ => false
  let (w, first) := opened.handle announced a 100
  check "mempool: the first announcement is fetched" (askedOf first == #[a])
  let (w, second) := w.handle announced b 101
  check "mempool: a second one waits on the fetch" (askedOf second).isEmpty
  -- notfound for something else frees nothing
  let block : InventoryPayload := { vectors := #[{ type := InventoryType.block, hash := tx.txid }] }
  let (w, _) := w.handle (.notfound block) a 102
  check "mempool: a block's notfound frees no txid" (askedOf (w.handle announced b 103).2).isEmpty
  let (w, _) := w.handle (.notfound { vectors }) a 104
  let (_, late) := w.handle (.tx tx) a 105
  check "mempool: after notfound the transaction is no longer expected" !(paid late)
  let (w, third) := w.handle announced b 106
  check "mempool: after notfound, another peer's announcement fetches it" (askedOf third == #[b])
  let (_, seen) := w.handle (.tx tx) b 107
  check "mempool: and the payment is seen" (paid seen)
  -- the getdata could not be sent
  let (w, _) := opened.handle announced a 100
  let w := w.sendFailed vectors
  check "mempool: a failed send frees the request" w.inFlight.isEmpty
  let (w, retry) := w.handle announced b 101
  check "mempool: after a failed send, another peer's announcement fetches it" (askedOf retry == #[b])
  let (_, seen) := w.handle (.tx tx) b 102
  check "mempool: and that payment is seen" (paid seen)

/-- The broadcaster giving up on peers that take the inv and never ask for the transaction (#39), over an
IPv4 and an IPv6 fake node (ephemeral, so high, ports): an announcement unanswered past
`announcementTimeoutMs` fails naming its peer's endpoint (`expireStaleAnnouncements`, `endpointOfKey`),
and a relay-only session whose seat has had its announcements ends with `seatsGone` (`canAnnounce`,
`endRelayOnlySessionIfSeatsGone`), leaving the payment pending. -/
def broadcastGiveUpChecks : IO Unit := do
  let v4 ← fakeNode regtest
  let v6 ← fakeNode regtest (v6 := true)
  let pool ← PeerPool.new regtest (peerCount := 2) (manualPeers := #[v4, v6]) (seedResolver := some noSeeds)
  pool.start
  discard <| waitUntil 5_000 (do return (← pool.connectedPeers).size == 2)
  let b ← runNet "give-up broadcaster" (TxBroadcaster.new pool (rebroadcastBaseMs := 200) (announcementTimeoutMs := 100))
  let events ← collect (← b.events)
  let txid ← runNet "give-up broadcast" (b.broadcast (fakeRawTx 1))
  let timedOut (ep : PeerEndpoint) : IO Bool := do
    return (← events.get).any fun | .failed t p r => t == txid && p == ep && r == "announcement timeout" | _ => false
  let both ← waitUntil 5_000 (do return (← timedOut v4) && (← timedOut v6))
  let failedAt := (← events.get).filterMap fun | .failed _ p r => some s!"{p.description} {r}" | _ => none
  check s!"announce timeout: each unanswered peer is named ({v4.description}, {v6.description})" both s!"{failedAt}"
  b.shutdown
  let b2 ← runNet "seat broadcaster" (TxBroadcaster.new pool (rebroadcastBaseMs := 200) (maxAnnouncementsPerPeer := 1))
  let events2 ← collect (← b2.events)
  let txid2 ← runNet "seat broadcast" (b2.broadcast (fakeRawTx 2))
  check "relay-only: a session opens over the fake seat" (← runNet "enterRelayOnly" (b2.enterRelayOnly 1))
  let ended ← waitUntil 5_000 (do return (← events2.get).any fun | .relaySessionEnded .seatsGone => true | _ => false)
  check "relay-only: a seat out of announcements that never asked ends the session (seatsGone)"
    (ended && !(← b2.isRelayOnly) && !(← pool.isRunning) && (← b2.pendingTxids) == #[txid2])
    (toString ((← events2.get).filterMap fun | .relaySessionEnded r => some r.rawValue | _ => none))
  b2.shutdown
  pool.stop

/-- Upstream `PeerPoolTests` for #175: discovery as one completion stream of dials and seed answers. -/
def discoveryChecks (dir : String) : IO Unit := do
  let seeded : NetworkParams := { regtest with dnsSeeds := #["seed-a.test", "seed-b.test", "seed-c.test"] }
  -- localDialsDoNotWaitForSeeds
  let gate ← IO.Promise.new (α := Unit)
  let blocked : SeedResolver := { lookup := fun _ _ _ => do discard <| IO.wait gate.result?; pure #[] }
  let first ← fakeNode seeded
  let second ← fakeNode seeded
  let pool ← PeerPool.new seeded (peerCount := 2) (manualPeers := #[first, second]) (seedResolver := some blocked)
  spawn pool.start
  let connected ← waitUntil 20_000 (do return (← pool.connectedPeers).size == 2)
  gate.resolve ()
  check "ready local peers are seated without waiting for DNS" connected
  pool.stop
  -- seedResultsAreConsumedAsTheyArrive
  let gate2 ← IO.Promise.new (α := Unit)
  let node ← fakeNode seeded
  let halfBlocked : SeedResolver := { lookup := fun host _ _ => do
    if host == "seed-a.test" then return #[node]
    discard <| IO.wait gate2.result?
    return #[] }
  let pool2 ← PeerPool.new seeded (peerCount := 1) (seedResolver := some halfBlocked)
  spawn pool2.start
  let finished ← waitUntil 20_000 (do
    let s ← pool2.connectionStatus
    return s.connected == 1 && !s.dialing)
  gate2.resolve ()
  check "a usable seed result connects while other seeds are still waiting" finished
  pool2.stop
  -- diversityExhaustionStillResolvesSeeds
  let nodes ← (List.range 4).mapM fun _ => fakeNode seeded
  let file : System.FilePath := s!"{dir}/diversity-peers.json"
  IO.FS.writeBinFile file (PersistedPeers.encode (nodes.take 3 |>.toArray.map ({ endpoint := ·, source := .census })))
  let seedPeer := nodes[3]!
  let pool3 ← PeerPool.new seeded (peerCount := 3) (peersFile := some file) (maxParallelDials := 1)
    (seedResolver := some { lookup := fun _ _ _ => pure #[seedPeer] })
  pool3.start
  check "DNS still fills a seat after diversity skips remembered candidates"
    ((← pool3.connectedPeers).size == 3 && (← pool3.source seedPeer) == some .dnsSeed &&
     !(← pool3.connectionStatus).exhausted)
    s!"{(← pool3.connectedPeers).size} seated, seed peer {repr (← pool3.source seedPeer)}"
  pool3.stop
  -- fullPoolDoesNotWaitForSilentDial
  let good ← fakeNode regtest
  let silent ← fakeNode regtest (silent := true)
  let pool4 ← PeerPool.new regtest (peerCount := 1) (manualPeers := #[silent, good]) (seedResolver := some noSeeds)
    (dialTimeoutMs := 90_000)
  spawn pool4.start
  let settled ← waitUntil 20_000 (do
    let s ← pool4.connectionStatus
    return s.connected == 1 && !s.dialing)
  check "a full pool closes silent surplus dials immediately" settled
  pool4.stop

def fakeChecks (dir : String) : IO Unit := do
  say "transport and pool failure paths (fake peers)"
  closedPeerChecks
  discoveryChecks dir
  let ep (port : UInt16) : PeerEndpoint := { host := "127.0.0.1", port }
  let silent ← fakePeer .silent
  let c1 ← PeerConnection.new (ep silent) regtest
  check "silent peer: handshake times out" (match ← (c1.connect 800).attempt with
    | .error (.peer .timeout) => true | _ => false)
  let nf ← fakePeer .noFilters
  let c2 ← PeerConnection.new (ep nf) regtest
  check "peer without compact filters is refused" (match ← (c2.connect 3_000).attempt with
    | .error (.peer (.missingCompactFilters 0)) => true | _ => false)
  let bm ← fakePeer .badMagic
  let c3 ← PeerConnection.new (ep bm) regtest
  check "wrong magic tears down as a framing error" (match ← (c3.connect 3_000).attempt with
    | .error (.framing .badMagic) => true | _ => false)
  -- Pool judgement: a data fault burns the peer, a timeout only cools it.
  let stray ← fakePeer .strayHeader
  let pool ← PeerPool.new regtest (peerCount := 1) (manualPeers := #[ep stray]) (seedResolver := some noSeeds)
  pool.start
  discard <| waitUntil 5_000 (do return (← pool.connectedPeers).size == 1)
  let store ← runNet "fake headers" (HeaderStore.open regtest none)
  let r ← (pool.syncHeaders store (timeoutPerPeerMs := 2_000)).attempt
  let reason ← pool.rejectionReason (ep stray)
  check "headers that do not connect: misbehaving, then exhausted"
    ((match r with | .error (.pool (.exhausted 1 _)) => true | _ => false) &&
     reason == some (HeaderChainError.description .doesNotConnect))
    (match r with | .error e => e.description | .ok _ => "ok")
  pool.stop
  let mute ← fakePeer .mute
  let pool2 ← PeerPool.new regtest (peerCount := 1) (manualPeers := #[ep mute]) (seedResolver := some noSeeds)
  pool2.start
  discard <| waitUntil 5_000 (do return (← pool2.connectedPeers).size == 1)
  let r2 ← (pool2.syncHeaders store (timeoutPerPeerMs := 800)).attempt
  check "a peer that stops answering is cooled off, not banned"
    ((match r2 with | .error (.pool (.allPeersCoolingDown 1 _)) => true | _ => false) &&
     (← pool2.isCoolingDown (ep mute)) && (← pool2.knownGood).isEmpty == false)
    (match r2 with | .error e => e.description | .ok _ => "ok")
  pool2.stop
  broadcastGiveUpChecks
  burstChecks
  keepaliveChecks
  replenishChecks
  voteChecks dir
  mempoolRefetchChecks

/-- 3b. Restore-only range scans (#226): a back-scan for the funded script below the forward frontier. -/
def rangeChecks (dir : String) (pool : PeerPool) (store : HeaderStore) (fs : FilterSyncIO) (spk : ByteArray)
    (tip fundHeight : Nat) (filtersPath : System.FilePath) : IO Unit := do
  let rangePath : System.FilePath := s!"{dir}/range.json"
  let rfs ← runNet "range filters" (FilterSyncIO.new pool store 0 none)
  let rtip := tip.toUInt32
  let rangeMatches ← IO.mkRef (#[] : Array Nat)
  let forwardBefore ← fs.nextScanHeight
  let out ← runNet "scanRange" (rfs.scanRange 1 rtip #[spk] (path := some rangePath)
    (onMatch := fun m => rangeMatches.modify (·.push m.height.toNat)))
  check "range: finds the payment, the run complete" ((← rangeMatches.get).contains fundHeight && out.isComplete &&
    out.matchedHeights.contains fundHeight.toUInt32 && out.iteration == 1 && out.filterBytesRead > 0) s!"{repr out}"
  check "range: the forward frontiers are untouched" ((← fs.nextScanHeight) == forwardBefore && (← rfs.nextScanHeight) == 0)
  check "range: the receipt names the node" (out.crossCheck.any (·.agreed.any (·.source == some .manual)))
  let again ← runNet "scanRange again" (rfs.scanRange 1 rtip #[spk] (path := some rangePath) (onMatch := fun _ => pure ()))
  check "range: a finished pass resumes as finished, reading nothing" (again.isComplete && again.matchedHeights.isEmpty &&
    again.filterBytesRead == 0)
  let other := ByteArray.mk #[0x51, 0x20] ++ ByteArray.mk (Array.replicate 32 0x44)
  let pass2 ← runNet "scanRange pass 2" (rfs.scanRange 1 rtip #[spk, other] (path := some rangePath)
    (onMatch := fun _ => pure ()))
  check "range: a new script set is the next pass over the range" (pass2.iteration == 2 && pass2.isComplete &&
    pass2.matchedHeights.contains fundHeight.toUInt32)
  let refused {α} (x : NetM α) (ok : RangeScanError → Bool) : IO Bool := do
    match ← x.toBaseIO with | .error (.range e) => return ok e | _ => return false
  let budgetPath : System.FilePath := s!"{dir}/range-budget.json"
  check "range: a run past its byte budget refuses, the batch committing nothing"
    ((← refused (rfs.scanRange 1 rtip #[spk] (RangeScanLimits.make (maxFilterBytes := 1)) (some budgetPath) (fun _ => pure ()))
      (fun | .filterBytesExhausted r 1 => r > 1 | _ => false)) && !(← fileExists budgetPath))
  check "range: and resumes with a budget" ((← runNet "scanRange budget" (rfs.scanRange 1 rtip #[spk]
    (path := some budgetPath) (onMatch := fun _ => pure ()))).isComplete)
  check "range: no time budget is refused before a filter is read"
    (← refused (rfs.scanRange 1 rtip #[spk] (RangeScanLimits.make (maxDurationMs := 0)) none (fun _ => pure ()))
      (fun | .runTimedOut 0 => true | _ => false))
  let strictRange ← runNet "strict range" (FilterSyncIO.new pool store 0 none (crossCheckPolicy := .requireDistinctSources))
  check "range: the strict policy refuses one class before a filter is fetched"
    (match ← (strictRange.scanRange 1 rtip #[spk] (onMatch := fun _ => pure ())).toBaseIO with
     | .error (.filters (.crossCheckUnavailable _)) => true | _ => false)
  if rtip < 3000 then
    -- 2001 would run: its anchor at 2000 is itself a boundary the reference speaks for
    check "range: a range that reaches no checkpoint, with no anchor, is refused"
      (← refused (rfs.scanRange 2101 rtip #[spk] (onMatch := fun _ => pure ()))
        (fun | .rangeSpansNoCheckpoint 2101 _ => true | _ => false))
  check "range: shape refusals" ((← refused (rfs.scanRange 10 9 #[spk] (onMatch := fun _ => pure ()))
      (fun | .invalidRange 10 9 => true | _ => false)) &&
    (← refused (rfs.scanRange 10 10 #[] (onMatch := fun _ => pure ())) (· == .noWatchScripts)) &&
    (← refused (rfs.scanRange 10 11 #[spk] (RangeScanLimits.make (maxBlocks := 1)) none (fun _ => pure ()))
      (fun | .rangeTooWide 2 1 => true | _ => false)) &&
    (← refused (rfs.scanRange 10 10 #[spk, other] (RangeScanLimits.make (maxScripts := 1)) none (fun _ => pure ()))
      (fun | .tooManyScripts 2 1 => true | _ => false)) &&
    (← refused (rfs.scanRange 10 (rtip + 1) #[spk] (onMatch := fun _ => pure ()))
      (fun | .rangeAboveChain t _ => t == rtip + 1 | _ => false)))
  check "range: the forward loader refuses a range record"
    (match ← (FilterSyncIO.new pool store 0 (some rangePath)).toBaseIO with
     | .error (.filterStorage (.damaged _)) => true | _ => false)
  check "range: the range loader refuses forward progress"
    (← refused (rfs.scanRange 1 rtip #[spk] (path := some filtersPath) (onMatch := fun _ => pure ()))
      (fun | .recordDamaged r => (r.splitOn "not a range-scan record").length > 1 | _ => false))
  -- the record's rules
  let fp := RangeScanProgress.fingerprint #[spk]
  check "range: a repeated script is the same set, in any order"
    (RangeScanProgress.fingerprint #[spk, other, other] == RangeScanProgress.fingerprint #[other, spk] &&
     fp != RangeScanProgress.fingerprint #[spk, other])
  let capped : RangeScanProgress := { fromHeight := 1, toHeight := rtip, nextScanHeight := 1, watchFingerprint := fp, iteration := 1 }
  check "range: the pass cap refuses at its boundary"
    ((match RangeScanProgress.resumed (some capped) 1 rtip (RangeScanProgress.fingerprint #[other])
        (RangeScanLimits.make (maxIterations := 1)) with
      | .error (.tooManyIterations 2 1) => true | _ => false) &&
     (RangeScanProgress.resumed (some capped) 1 rtip (RangeScanProgress.fingerprint #[other])
        (RangeScanLimits.make (maxIterations := 2))).toBool)
  check "range: a pass number past the ceiling is damage"
    (match RangeScanProgress.load (some ({ capped with iteration := 51 }).toJson.compress) with
     | .error (.recordDamaged "the pass number is out of range") => true | _ => false)
  let greedy := RangeScanLimits.make 0xFFFFFFFF 1_000_000 (2 ^ 40) 86_400_000 1_000
  check "range: no cap can be raised past its ceiling" (greedy.maxBlocks == 262_800 && greedy.maxScripts == 20_000 &&
    greedy.maxFilterBytes == 1_073_741_824 && greedy.maxDurationMs == 3_600_000 && greedy.maxIterations == 50)
  let hdr := hex (ByteArray.mk (Array.replicate 32 7))
  let wide : Std.HashMap String String := (List.range 3200).foldl (fun m h => m.insert (toString (h + 1)) hdr) ({} : Std.HashMap String String)
  check "range: pruning keeps the anchor below the range" ((RangeScan.prunedRangeHeaders wide 3201 1).contains "0" == false &&
    (RangeScan.prunedRangeHeaders wide 3201 2).contains "1" && !(FilterSync.prunedFilterHeaders wide 3201).contains "2")

/-- Copies `src` to `dst` until either side closes. -/
partial def pump (src dst : Std.Async.TCP.Socket.Client) : IO Unit := do
  match ← (src.recv? 65536).block.toBaseIO with
  | .ok (some chunk) =>
    if chunk.isEmpty then discard <| dst.shutdown.toIO
    else match ← (dst.send chunk).block.toBaseIO with
      | .ok () => pump src dst
      | .error _ => discard <| src.shutdown.toIO
  | _ => discard <| dst.shutdown.toIO

/-- A SOCKS5 gateway stand-in: the no-authentication greeting, then CONNECT by name (address type 3), every
name forwarded to `target`. Records the names it was asked for; with `refuse`, answers CONNECT with reply 5. -/
def fakeSocks (target : PeerEndpoint) (refuse : Bool := false) : IO (PeerEndpoint × IO.Ref (Array String)) := do
  let asked ← IO.mkRef (#[] : Array String)
  let server ← Std.Async.TCP.Socket.Server.mk
  server.bind (.v4 ⟨Std.Net.IPv4Addr.ofParts 127 0 0 1, 0⟩)
  server.listen 8
  let port := (← server.getSockName).port
  spawn do
    let keep := server
    repeat
      let sock ← keep.accept.block
      spawn do
        let buf ← IO.mkRef ByteArray.empty
        let take (n : Nat) : IO (Option ByteArray) := do
          while (← buf.get).size < n do
            let some chunk ← (sock.recv? 4096).block | return none
            if chunk.isEmpty then return none
            buf.modify (· ++ chunk)
          let b ← buf.get
          buf.set (b.extract n b.size)
          return some (b.extract 0 n)
        -- any greeting that offers no-authentication (curl also offers GSS-API)
        let some hello ← take 2 | return
        let some methods ← take hello[1]!.toNat | return
        unless hello[0]! == 5 && methods.toList.contains 0 do discard <| sock.shutdown.toIO; return
        (sock.send (ByteArray.mk #[5, 0])).block
        let some head ← take 5 | return
        unless head[0]! == 5 && head[1]! == 1 && head[3]! == 3 do discard <| sock.shutdown.toIO; return
        let some rest ← take (head[4]!.toNat + 2) | return
        asked.modify (·.push (String.fromUTF8! (rest.extract 0 head[4]!.toNat)))
        if refuse then
          (sock.send (ByteArray.mk #[5, 5, 0, 1, 0, 0, 0, 0, 0, 0])).block
          discard <| sock.shutdown.toIO
          return
        let up ← Std.Async.TCP.Socket.Client.mk
        (up.connect (.v4 ⟨Std.Net.IPv4Addr.ofParts 127 0 0 1, target.port⟩)).block
        (sock.send (ByteArray.mk #[5, 0, 0, 1, 127, 0, 0, 1, 0, 0])).block
        let left ← buf.get
        if !left.isEmpty then (up.send left).block
        spawn (pump up sock)
        pump sock up
  return ({ host := "127.0.0.1", port }, asked)

/-- The routing gate (`RoutingTests.i2pOnlyClientRefusesPublicHosts`,
`PeerGatewayTests.torHTTPUsesTheGatewayForRemoteResolution`): I2P alone makes no HTTP request at all;
Tor alone fetches through its gateway, which is asked for the URL's host by name. -/
def routedHTTPChecks (dir : String) : IO Unit := do
  say "routed HTTP (the gateway gate)"
  let calls ← IO.mkRef 0
  let counting : HttpFetch := fun _ => do calls.modify (· + 1); return .response 200 none "OK".toUTF8
  let i2pOnly : PeerGatewayConfiguration := { networks := [.i2p], i2pProxy := some { host := "100.74.30.8", port := 4447 } }
  let refusing ← RoutedHTTPClient.ofGateways counting i2pOnly
  check "i2p only: the client is not enabled" (!refusing.enabled)
  check "i2p only: a public host is unavailable"
    (match ← (refusing.get "http://127.0.0.1:1/census/peers.json" 8).attempt with | .error (.http .unavailable) => true | _ => false)
  check "i2p only: nothing was fetched" ((← calls.get) == 0)
  let disabled ← RoutedHTTPClient.new counting (enabled := false)
  check "a disabled client refuses" ((match ← (disabled.get "https://example.com" 1024).attempt with
    | .error (.http .unavailable) => true | _ => false) && (← calls.get) == 0)
  let badProxy ← RoutedHTTPClient.new counting (proxy := some { host := "a b", port := 9050 })
  check "an implausible proxy disables the client" (!badProxy.enabled)
  let torOnly : PeerGatewayConfiguration := { networks := [.tor], torProxy := some { host := "100.74.30.9", port := 9050 } }
  let viaTor ← RoutedHTTPClient.ofGateways counting torOnly
  let both : PeerGatewayConfiguration := { networks := [.clearnet, .tor], torProxy := some { host := "100.74.30.9", port := 9050 } }
  check "tor only: through the gateway; with clearnet: direct"
    (viaTor.enabled && viaTor.proxy == torOnly.torProxy && (← RoutedHTTPClient.ofGateways counting both).proxy.isNone)
  let seen ← IO.mkRef (none : Option HttpRequest)
  let recording : HttpFetch := fun r => do seen.set (some r); return .response 200 none "OK".toUTF8
  discard <| ((← RoutedHTTPClient.ofGateways recording torOnly).get "https://example.com/x" 8).attempt
  check "tor only: every hop names the proxy, with the longer limits" (match ← seen.get with
    | some r => r.socks == torOnly.torProxy && r.requestTimeoutSeconds == 90 && r.resourceTimeoutSeconds == 180
    | none => false)
  -- The curl fetch through a SOCKS5 gateway to the local Python server (offlineChecks wrote its script).
  let server ← IO.Process.spawn { cmd := "python3", args := #["-I", s!"{dir}/http_server.py"], stdout := .piped,
                                  stderr := .null, stdin := .null }
  try
    let port := (← server.stdout.getLine).trimAscii.toString
    let (gateway, asked) ← fakeSocks { host := "127.0.0.1", port := port.toNat!.toUInt16 }
    let http ← RoutedHTTPClient.new (curlFetch "/usr/bin/curl") (proxy := some gateway)
    let body ← (http.get "http://gateway-http.invalid/ok" 100).attempt
    check "tor: the body arrives through the gateway" (match body with | .ok b => b == "hello".toUTF8 | _ => false)
      (match body with | .error e => e.description | .ok b => s!"{b.size} bytes")
    check "tor: the gateway was asked for the URL's host by name" ((← asked.get) == #["gateway-http.invalid"])
      s!"{← asked.get}"
    http.cancel
  finally
    server.kill

/-- A MagicDNS answer for `host`: `addresses` as A records under a compression pointer to the question. -/
def dnsAnswer (id : UInt16) (host : String) (addresses : List (List UInt8)) (flags : UInt16 := 0x8180) : ByteArray := Id.run do
  let u16 (v : UInt16) : ByteArray := ByteArray.mk #[(v >>> 8).toUInt8, (v &&& 255).toUInt8]
  let mut b := u16 id ++ u16 flags ++ u16 1 ++ u16 addresses.length.toUInt16 ++ u16 0 ++ u16 0
  b := b ++ ByteArray.mk #[host.utf8ByteSize.toUInt8] ++ host.toUTF8 ++ ByteArray.mk #[0] ++ u16 1 ++ u16 1
  for a in addresses do
    b := b ++ ByteArray.mk #[0xc0, 12] ++ u16 1 ++ u16 1 ++ ByteArray.mk #[0, 0, 0, 60] ++ u16 4 ++ ByteArray.mk a.toArray
  return b

/-- 10. Tor and I2P gateways (#181, #189, #190, #193): configuration, MagicDNS answers, discovery, and a
regtest node reached by an onion name through a SOCKS5 stand-in. -/
def gatewayChecks (n : Node) : IO Unit := do
  say "gateways (Tor/I2P through SOCKS5)"
  let onion : PeerEndpoint := { host := String.ofList (List.replicate 56 'a') ++ ".onion", port := 18444 }
  let garlic : PeerEndpoint := { host := String.ofList (List.replicate 52 'b') ++ ".b32.i2p", port := 0 }
  let gw : PeerEndpoint := { host := "100.101.102.103", port := 9050 }
  check "parseProxy: host:port and [IPv6]:port"
    ((PeerGatewayConfiguration.parseProxy " 100.101.102.103:9050 ").toOption == some gw &&
     (PeerGatewayConfiguration.parseProxy "[::1]:4447").toOption == some { host := "::1", port := 4447 } &&
     (PeerGatewayConfiguration.parseProxy "gateway.local:9050").toOption == some { host := "gateway.local", port := 9050 })
  check "parseProxy refuses URLs, bare IPv6, port 0, overlay hosts"
    (["http://x:1", "::1:9050", "x:0", "x:70000", "x", "a@b:1", onion.host ++ ":9050", ""].all fun t =>
      match PeerGatewayConfiguration.parseProxy t with | .error .address => true | _ => false)
  let tor : PeerGatewayConfiguration := { networks := [.tor], torProxy := some gw }
  check "a selected overlay needs its gateway" (!({ networks := [.tor] } : PeerGatewayConfiguration).isValid &&
    !({ networks := [] } : PeerGatewayConfiguration).isValid && tor.isValid && ({} : PeerGatewayConfiguration).isValid)
  check "Tor-only permits canonical onions, not clearnet or I2P"
    (tor.permits onion && !tor.permits { host := "1.2.3.4", port := 8333 } && !tor.permits garlic &&
     !tor.permits { onion with host := "short.onion" } && !tor.permits { onion with port := 0 })
  check "an onion goes through the Tor gateway, clearnet direct"
    (tor.proxy onion == some gw && ({} : PeerGatewayConfiguration).proxy { host := "1.2.3.4", port := 8333 } == none)
  check "HTTP without clearnet goes through Tor; I2P alone has none"
    (tor.permitsHTTP && tor.httpProxy == some gw && ({} : PeerGatewayConfiguration).httpProxy == none &&
     !({ networks := [.i2p], i2pProxy := some gw } : PeerGatewayConfiguration).permitsHTTP)
  let both : PeerGatewayConfiguration := { networks := [.i2p, .tor], torProxy := some gw, i2pProxy := some { gw with port := 4447 } }
  check "configuration JSON round trip (networks in canonical order)"
    (PeerGatewayConfiguration.ofJson? both.toJson == some { both with networks := [.tor, .i2p] } &&
     PeerGatewayConfiguration.ofJson? ({} : PeerGatewayConfiguration).toJson == some {})
  -- MagicDNS
  let q : GatewayDNSQuery := { host := "winnow-tor-gateway", id := 0x1234 }
  check "DNS query bytes" (q.bytes == ByteArray.mk #[0x12, 0x34, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 18] ++
    "winnow-tor-gateway".toUTF8 ++ ByteArray.mk #[0, 0, 1, 0, 1])
  check "DNS answer: tailnet A records only"
    (q.addresses (dnsAnswer 0x1234 "winnow-tor-gateway" [[100, 101, 102, 103], [8, 8, 8, 8], [100, 100, 100, 100], [100, 128, 0, 1]])
      == ["100.101.102.103"])
  check "DNS answer: wrong id, truncated, error rcode, other name give nothing"
    (q.addresses (dnsAnswer 0x4321 "winnow-tor-gateway" [[100, 101, 102, 103]]) == [] &&
     q.addresses ((dnsAnswer 0x1234 "winnow-tor-gateway" [[100, 101, 102, 103]]).extract 0 40) == [] &&
     q.addresses (dnsAnswer 0x1234 "winnow-tor-gateway" [[100, 101, 102, 103]] (flags := 0x8183)) == [] &&
     q.addresses (dnsAnswer 0x1234 "winnow-i2p-gateway" [[100, 101, 102, 103]]) == [])
  check "tailnet range is 100.64/10 without MagicDNS"
    (isTailnetIPv4 "100.64.0.1" && isTailnetIPv4 "100.127.255.254" && !isTailnetIPv4 "100.128.0.1" &&
     !isTailnetIPv4 "100.63.0.1" && !isTailnetIPv4 "100.100.100.100" && !isTailnetIPv4 "10.0.0.1")
  let resolveTor : String → IO (List String) := fun h => pure (if h == "winnow-tor-gateway" then ["8.8.8.8", "100.101.102.103"] else [])
  let found ← discoverGateways resolveTor (fun _ => pure true)
  check "discovery: a Tor gateway alone drops clearnet" (found == { networks := [.tor], torProxy := some gw })
  let none_ ← discoverGateways resolveTor (fun _ => pure false)
  check "discovery: no gateway answering keeps clearnet" (none_ == {})
  -- Through the stand-in, to the regtest node.
  let (proxy, asked) ← fakeSocks n.endpoint
  check "SOCKS probe: the stand-in answers 05 00" (← probeSOCKS proxy)
  check "SOCKS probe: a Bitcoin node is not a gateway" !(← probeSOCKS n.endpoint)
  let c ← PeerConnection.new onion regtest (socksProxy := some proxy)
  runNet "connect through SOCKS5" (c.connect 10_000)
  check "an onion peer handshakes through the gateway"
    ((← c.isConnected) && (← c.peerUserAgent).startsWith "/Satoshi:")
  check "the gateway was given the onion name, unresolved" ((← asked.get).contains onion.host) s!"{← asked.get}"
  c.disconnect
  let (refusing, _) ← fakeSocks n.endpoint (refuse := true)
  let r ← PeerConnection.new onion regtest (socksProxy := some refusing)
  check "a gateway that cannot reach the peer is a transport failure"
    (match ← (r.connect 5_000).attempt with
      | .error e@(.peer (.disconnected m)) => e.isTransportPeerError && m == "SOCKS5 proxy: connection refused"
      | _ => false)
  -- The pool: Tor only, so the clearnet manual peer is never dialled and no seed is resolved.
  let seedAsks ← IO.mkRef 0
  let counting : SeedResolver := { lookup := fun _ _ _ => do seedAsks.modify (· + 1); pure #[] }
  asked.set #[]
  let pool ← PeerPool.new regtest (peerCount := 2) (manualPeers := #[n.endpoint, onion]) (seedResolver := some counting)
    (gateways := { networks := [.tor], torProxy := some proxy })
  pool.start
  check "Tor-only pool seats the onion through the gateway"
    (← waitUntil 10_000 (do return (← pool.connectedPeers).any (·.endpoint == onion)))
  discard <| waitUntil 3_000 (do return (← pool.connectionStatus).exhausted)
  let seated := (← pool.connectedPeers).map (·.endpoint)
  check "Tor-only pool never dials clearnet nor resolves seeds"
    (seated == #[onion] && (← seedAsks.get) == 0 && (← asked.get) == #[onion.host]) s!"{seated.map (·.host)}"
  pool.stop

/-- FilterSync's pure steps that the IO scan runs: `batches` (the cfheaders requests of a batch, and
`batchStop`, which the forward and range scans step by) and `verifiedBlock` on a real block, a block the
filter did not name, and one whose transactions were changed. -/
def filterSyncPure (n : Node) : IO Unit := do
  check "batches: one short batch" (FilterSync.batches 5 9 == #[(5, 9)])
  check "batches: split at maxRangePerRequest" (FilterSync.batches 0 2_500 == #[(0, 999), (1_000, 1_999), (2_000, 2_500)])
  check "batches: a single block" (FilterSync.batches 7 7 == #[(7, 7)])
  check "batches: none past the ceiling" (FilterSync.batches 10 9 == #[])
  check "batches: up to the last representable height"
    (FilterSync.batches 0xFFFFFC17 0xFFFFFFFE == #[(0xFFFFFC17, 0xFFFFFFFE)])
  let hash ← n.cli #["getblockhash", "101"]
  let raw := ofHex! (← n.cli #["getblock", hash, "0"])
  match Block.decode raw with
  | .error e => check "verifiedBlock: decode block 101" false e.name
  | .ok b =>
    let named := ofDisplayHex! hash
    check "verifiedBlock: the block the filter named" (FilterSync.verifiedBlock b named 101 matches .ok _)
    check "verifiedBlock: another block's hash"
      (match FilterSync.verifiedBlock b (ofDisplayHex! (← n.cli #["getblockhash", "100"])) 101 with
       | .error (.badPeerResponse why) => why == "block hash mismatch at 101" | _ => false)
    -- the coinbase's last byte (its lock time): the header still names the block, the merkle root no longer matches
    match Block.decode (raw.set! (raw.size - 1) (raw[raw.size - 1]! ^^^ 0x01)) with
    | .error e => check "verifiedBlock: decode the changed block" false e.name
    | .ok changed =>
      check "verifiedBlock: changed transactions"
        (match FilterSync.verifiedBlock changed named 101 with
         | .error (.badPeerResponse why) => why == "merkle root mismatch at 101" | _ => false)

/-- A reorg under a confirmed send (#38), on the node: filter sync reports the fork, and
`TxBroadcaster.rollBack` (as the app's `rollBackStores` calls it from `onReorg`) makes the tombstone
pending again, saved and announced; a reload keeps it pending, and it confirms again on the new branch.
`b` holds `txid` as a tombstone at `confirmedAt` and is shut down here; the scan is one of its own over
`store`, from just below that block. -/
def reorgUnderSendChecks (n : Node) (pool : PeerPool) (store : HeaderStore) (b : TxBroadcaster)
    (txid raw : ByteArray) (confirmedAt : Nat) (dest : String) (broadcastPath : System.FilePath)
    (mineAddr otherAddr : String) : IO Unit := do
  let events ← collect (← b.events)
  let destSpk ← scriptOf n dest
  let fs ← runNet "send filters" (FilterSyncIO.new pool store (confirmedAt - 2).toUInt32)
  n.waitFilterIndex
  runNet "filter sync to the tip" (fs.sync #[destSpk] (onMatch := fun _ => pure ()))
  discard <| n.cli #["invalidateblock", ← n.cli #["getblockhash", toString confirmedAt]]
  -- the heavier branch leaves the send out, so it waits in the node's mempool
  for _ in [0:2] do discard <| n.cli #["generateblock", otherAddr, "[]"]
  n.waitFilterIndex
  let sendForks ← IO.mkRef (#[] : Array UInt32)
  runNet "filter sync over the reorg" (fs.sync #[destSpk]
    (onReorg := some fun fork => do sendForks.modify (·.push fork); b.rollBack fork) (onMatch := fun _ => pure ()))
  check "reorg under a send: reported at the block below its confirmation"
    ((← sendForks.get) == #[(confirmedAt - 1).toUInt32]) s!"{← sendForks.get}"
  check "reorg under a send: pending again" ((← b.pendingTxids) == #[txid] && (← b.rawTransaction txid) == some raw)
  check "reorg under a send: announced again" (← waitUntil 5_000 (do
    return (← events.get).any fun | .announced t k => t == txid && k ≥ 1 | _ => false))
  b.shutdown
  let reloaded ← runNet "broadcaster reload after the reorg" (TxBroadcaster.new pool (some broadcastPath))
  check "reorg under a send: still pending after a reload" (reloaded.persistenceState == .loaded 1 && (← reloaded.pendingTxids) == #[txid])
  let reloadedEvents ← collect (← reloaded.events)
  n.mine 1 mineAddr
  n.waitFilterIndex
  let matched ← IO.mkRef (#[] : Array UInt32)
  runNet "filter sync, the send mined again" (fs.sync #[destSpk] (onMatch := fun m => do
    if m.block.transactions.any (·.txid == txid) then
      matched.modify (·.push m.height)
      reloaded.markConfirmed txid m.height))
  let reconfirmed ← waitUntil 5_000 (do return (← reloadedEvents.get).any fun | .confirmed t => t == txid | _ => false)
  check "reorg under a send: confirmed again on the new branch"
    (reconfirmed && (← reloaded.pendingTxids).isEmpty && (← matched.get) == #[(← n.height).toUInt32]) s!"matched at {← matched.get}"
  reloaded.shutdown

def nodeChecks (dir : String) (n : Node) : IO Unit := do
  say s!"node: bitcoind regtest pid {n.pid}, p2p {n.p2p}"
  discard <| n.cli #["createwallet", "w"]
  let mineAddr ← n.wallet #["getnewaddress"]
  let otherAddr ← n.wallet #["getnewaddress"]
  n.mine 101 mineAddr
  filterSyncPure n
  -- 1. Handshake
  let c ← PeerConnection.new n.endpoint regtest
  runNet "connect" (c.connect 10_000)
  let ua ← c.peerUserAgent
  check "handshake: version/verack completed" ((← c.isConnected) && ua.startsWith "/Satoshi:") ua
  check "handshake: peer signals NODE_COMPACT_FILTERS" ((← c.peerServices) &&& PeerConnection.nodeCompactFilters != 0)
  let info ← n.json #["getpeerinfo"]
  let subvers := match info with | .arr xs => xs.map (jsonStr · "subver") | _ => #[]
  check "node sees our user agent /winnow:0.1/" (subvers.contains "/winnow:0.1/") s!"{subvers}"
  runNet "ping" c.ping
  check "ping answered with pong" true
  let refused ← PeerConnection.new { host := "127.0.0.1", port := 1 } regtest
  check "refused dial is a transport error" (match ← (refused.connect 2_000).attempt with
    | .error e => e.isTransportPeerError | .ok _ => false)
  -- Chain: a funded watch script, then enough blocks for several header and filter batches.
  let watchAddr ← n.wallet #["getnewaddress"]
  let spk ← scriptOf n watchAddr
  let fundTxid ← n.wallet #["sendtoaddress", watchAddr, "1.0"]
  n.mine 1 mineAddr
  let fundHeight ← n.height
  n.mineElsewhere 2100
  let tip ← n.height
  say s!"  chain: tip {tip}, funding tx {fundTxid} at {fundHeight}"
  -- 2. Header sync through the pool
  let peersPath : System.FilePath := s!"{dir}/peers.json"
  let headersPath : System.FilePath := s!"{dir}/headers.bin"
  let filtersPath : System.FilePath := s!"{dir}/filters.json"
  let pool ← PeerPool.new regtest (manualPeers := #[n.endpoint]) (peersFile := some peersPath) (seedResolver := some noSeeds)
  pool.start
  check "pool seats the manual peer" (← waitUntil 10_000 (do return (← pool.connectedPeers).size == 1))
  let status ← pool.connectionStatus
  check "pool reports exhaustion below target" (status.exhausted && status.connected == 1 && status.target == 3)
  let store ← runNet "open headers" (HeaderStore.open regtest (some headersPath))
  let outcome ← runNet "syncHeaders" (pool.syncHeaders store)
  let best ← n.cli #["getbestblockhash"]
  check "header sync reaches the node's tip" ((← store.height).toNat == tip && displayHex (← store.tipHash) == best)
    s!"{outcome.connected} headers, tip {← store.height}"
  let reopened ← runNet "reopen headers" (HeaderStore.open regtest (some headersPath))
  let fileBytes ← IO.FS.readBinFile headersPath
  check "headers.bin round trip" ((← reopened.height) == (← store.height) && (← reopened.tipHash) == (← store.tipHash) &&
    fileBytes == (← store.snapshot).fileBytes) s!"{fileBytes.size} bytes"
  -- 3. Compact filters
  n.waitFilterIndex
  let fs ← runNet "filters open" (FilterSyncIO.new pool store 0 (some filtersPath))
  let matched ← IO.mkRef (#[] : Array (UInt32 × Bool))
  runNet "filter sync" (fs.sync #[spk] (onMatch := fun m => do
    let has := m.block.transactions.any (fun t => displayHex t.txid == fundTxid)
    matched.modify (·.push (m.height, has))))
  let ms ← matched.get
  check "filter sync matches the funded script's block" (ms.any fun (h, has) => h.toNat == fundHeight && has) s!"{ms.map (·.1)}"
  check "filter sync scans to the tip" ((← fs.nextScanHeight).toNat == tip + 1)
  check "frontier after a sync: the tip's height and hash"
    ((← fs.frontier) == ((tip + 1).toUInt32, some (ofDisplayHex! (← n.cli #["getblockhash", toString tip]))))
  let pinned ← fs.filterHeader tip.toUInt32
  check "pinned filter header equals the node's" ((pinned.map displayHex) == some (← nodeFilterHeader n tip))
  let receipt ← (fs.transaction (ofDisplayHex! fundTxid) fundHeight.toUInt32).attempt
  check "historical receipt fetched from its block" (match receipt with | .ok t => displayHex t.txid == fundTxid | _ => false)
  let fs2 ← runNet "filters reopen" (FilterSyncIO.new pool store 0 (some filtersPath))
  check "filters.json round trip" (fs2.persistenceState == .loaded && (← fs2.nextScanHeight) == (← fs.nextScanHeight) &&
    (← fs2.pinnedFilterHeaders).size == (← fs.pinnedFilterHeaders).size) s!"{(← fs.pinnedFilterHeaders).size} pinned"
  -- 3a. The cross-check receipt (#226): who agreed, through which class, persisted with the frontier.
  let xcheck ← fs.lastCrossCheck
  check "receipt: the node, as a manual peer, about the tip" (match xcheck with
    | some r => r.tipHeight.toNat == tip && r.answerDigest.length == 64 &&
        r.agreed == #[{ endpoint := n.endpoint.description, source := some .manual }]
    | none => false) s!"{repr xcheck}"
  check "receipt: one class, so not distinct sources" (xcheck.any (!·.spansDistinctSources))
  check "receipt: persisted with the frontier" ((← fs2.lastCrossCheck) == xcheck)
  let strictPath : System.FilePath := s!"{dir}/strict-filters.json"
  let strict ← runNet "strict filters" (FilterSyncIO.new pool store 0 (some strictPath) (crossCheckPolicy := .requireDistinctSources))
  check "receipt: requireDistinctSources refuses one class, having scanned nothing"
    ((match ← (strict.sync #[spk] (onMatch := fun _ => pure ())).toBaseIO with
      | .error (.filters (.crossCheckUnavailable _)) => true | _ => false) && (← strict.nextScanHeight) == 0 &&
     !(← fileExists strictPath))
  -- the file names what it is, and the rules a receipt is held to
  let some r := xcheck | throw (IO.userError "no receipt")
  let withRecord : Progress := { nextScanHeight := 5, crossCheck := some r, record := some "range" }
  check "progress: a range record is refused by the forward loader"
    (match FilterSync.load (some withRecord.toJson.compress) 0 with | .error (.damaged _) => true | _ => false)
  let badDigest : CrossCheckReceipt := { r with answerDigest := "00" }
  let withBadDigest : Progress := { nextScanHeight := 5, crossCheck := some badDigest }
  check "progress: a bad digest is refused" (match FilterSync.load (some withBadDigest.toJson.compress) 0 with
    | .error (.damaged _) => true | _ => false)
  let withReceipt : Progress := { nextScanHeight := 5, crossCheck := some r }
  let unknownClass := withReceipt.toJson.compress.replace "\"manual\"" "\"tailnet\""
  check "progress: an unknown source class reads as none" (match FilterSync.load (some unknownClass) 0 with
    | .ok (_, p) => p.crossCheck.any (·.agreed.all (·.source.isNone)) | .error _ => false)
  check "progress: a rollback drops the receipt" (match FilterSync.rollBack withReceipt 2 with
    | some p => p.crossCheck.isNone && p.nextScanHeight == 3 | none => false)
  -- 3b. Restore-only range scans (#226)
  rangeChecks dir pool store fs spk tip fundHeight filtersPath
  -- 4. A reorg: invalidate three blocks, mine four elsewhere.
  let tipBefore ← n.height
  let forkAt := tipBefore - 3
  discard <| n.cli #["invalidateblock", ← n.cli #["getblockhash", toString (forkAt + 1)]]
  n.mine 4 otherAddr
  let tipAfter ← n.height
  n.waitFilterIndex
  let reorgs ← IO.mkRef (#[] : Array UInt32)
  runNet "filter sync after reorg" (fs.sync #[spk] (onReorg := some fun h => reorgs.modify (·.push h)) (onMatch := fun _ => pure ()))
  check "reorg reported at the fork before filters resume" ((← reorgs.get) == #[forkAt.toUInt32]) s!"{← reorgs.get}"
  check "reorg: headers follow the heavier branch" ((← store.height).toNat == tipAfter &&
    displayHex (← store.tipHash) == (← n.cli #["getbestblockhash"]))
  check "reorg: filters rescanned on the new branch" ((← fs.nextScanHeight).toNat == tipAfter + 1 &&
    ((← fs.filterHeader tipAfter.toUInt32).map displayHex) == some (← nodeFilterHeader n tipAfter))
  -- 5. A stale sibling of equal work, then a heavier branch.
  let oldTip ← store.tipHash
  discard <| n.cli #["invalidateblock", ← n.cli #["getbestblockhash"]]
  -- A fresh coinbase address, or the sibling would be the invalidated block itself.
  n.mine 1 (← n.wallet #["getnewaddress"])
  let sib ← runNet "sync sibling" (store.sync c)
  check "equal-work sibling is a stale sibling, tip kept" (sib.staleSiblings ≥ 1 && (← store.tipHash) == oldTip)
    s!"staleSiblings {sib.staleSiblings}"
  n.mine 1 (← n.wallet #["getnewaddress"])
  let heavier ← runNet "sync heavier" (store.sync c)
  check "heavier sibling branch replaces the tip" (heavier.minForkHeight == some (tipAfter - 1).toUInt32 &&
    displayHex (← store.tipHash) == (← n.cli #["getbestblockhash"])) s!"fork {heavier.minForkHeight}"
  -- 6. The mempool window, on a relaying connection.
  let relayPool ← PeerPool.new regtest (peerCount := 1) (manualPeers := #[n.endpoint]) (relayPreference := true)
    (seedResolver := some noSeeds)
  relayPool.start
  discard <| waitUntil 10_000 (do return (← relayPool.connectedPeers).size == 1)
  let seenAddr ← n.wallet #["getnewaddress"]
  let seenSpk ← scriptOf n seenAddr
  let window ← MempoolWindowIO.new relayPool #[seenSpk]
  let wevents ← collect (← window.events)
  window.start 600
  let seenTxid ← n.wallet #["sendtoaddress", seenAddr, "0.5"]
  let gotIt ← waitUntil 45_000 (do
    return (← wevents.get).any fun | .paymentSeen t a _ => displayHex t == seenTxid && a == 50_000_000 | _ => false)
  check "mempool window sees the payment" gotIt
  -- 7. Broadcast a raw transaction the node has not seen.
  let dest ← n.wallet #["getnewaddress"]
  let rawUnfunded ← n.wallet #["createrawtransaction", "[]", s!"\{\"{dest}\":0.1}"]
  let funded ← Json.parse (← n.wallet #["fundrawtransaction", rawUnfunded]) |> IO.ofExcept
  let signed ← Json.parse (← n.wallet #["signrawtransactionwithwallet", jsonStr funded "hex"]) |> IO.ofExcept
  let raw := ofHex! (jsonStr signed "hex")
  let broadcastPath : System.FilePath := s!"{dir}/broadcast.json"
  let b ← runNet "broadcaster" (TxBroadcaster.new pool (some broadcastPath))
  let bevents ← collect (← b.events)
  let expectedTxid := ((Transaction.decode raw).toOption.map (·.txid)).getD .empty
  window.watchEcho expectedTxid
  let txid ← runNet "broadcast" (b.broadcast raw (some 20.0))
  let inMempool ← waitUntil 20_000 (do
    let mp ← n.json #["getrawmempool"]
    return match mp with | .arr xs => xs.any (· == Json.str (displayHex txid)) | _ => false)
  check "broadcast: the node accepted the transaction" inMempool (displayHex txid)
  check "broadcast: announced, requested, served" ((← bevents.get).any (fun | .served t _ => t == txid | _ => false) &&
    (← b.wasServed txid))
  let echoed ← waitUntil 45_000 (do
    return (← wevents.get).any fun | .txidEchoed t _ => t == txid | _ => false)
  check "mempool window: the broadcast echoes back from the network" echoed
  window.stop
  check "mempool window closes" !(← window.isRunning)
  relayPool.stop
  b.shutdown
  let b2 ← runNet "broadcaster reload" (TxBroadcaster.new pool (some broadcastPath))
  check "broadcast.json round trip" (b2.persistenceState == .loaded 1 && (← b2.pendingTxids) == #[txid] &&
    (← b2.rawTransaction txid) == some raw && (← b2.wasServed txid))
  -- 7b. A relay-only session over the pending payment (#226): the pool keeps one seat, refuses header and
  -- filter sync, comes back with start(); the drain then ends the session and leaves the resumed pool alone.
  let b2events ← collect (← b2.events)
  check "relay-only: the pool is running with its seat" ((← pool.isRunning) && (← pool.connectedPeers).size == 1)
  check "relay-only: a session opens over a pending payment" (← runNet "enterRelayOnly" (b2.enterRelayOnly 1))
  check "relay-only: the pool is narrowed to one seat" ((← pool.mode) == .relayOnly && (← pool.connectedPeers).size == 1 &&
    (← pool.connectionStatus).target == 1)
  check "relay-only: header sync is refused"
    (match ← (pool.syncHeaders store).toBaseIO with | .error (.pool .relayOnly) => true | _ => false)
  check "relay-only: filter sync is refused"
    (match ← (fs.sync #[spk] (onMatch := fun _ => pure ())).toBaseIO with | .error (.filters .relayOnly) => true | _ => false)
  pool.start
  check "relay-only: start() resumes full service" ((← pool.mode) == .full && (← pool.isRunning))
  n.mine 1 mineAddr
  let confirmedAt ← n.height
  runNet "markConfirmed" (b2.markConfirmed txid confirmedAt.toUInt32)
  let drained ← waitUntil 5_000 (do
    return (← b2events.get).any fun | .relaySessionEnded .drained => true | _ => false)
  check "relay-only: the drain ends the session" (drained && !(← b2.isRelayOnly))
  check "relay-only: and leaves a pool its caller resumed running" ((← pool.isRunning) && (← pool.mode) == .full)
  check "relay-only: nothing pending, no session, and the pool goes quiet"
    (!(← runNet "enterRelayOnly again" (b2.enterRelayOnly 1)) && !(← pool.isRunning))
  pool.start
  discard <| waitUntil 20_000 (do return (← pool.connectedPeers).size == 1)
  b2.shutdown
  let b3 ← runNet "broadcaster reload 2" (TxBroadcaster.new pool (some broadcastPath))
  check "confirmed tombstone persists and is silent" ((← b3.pendingTxids).isEmpty && (← b3.rawTransaction txid).isNone &&
    b3.persistenceState == .loaded 1)
  reorgUnderSendChecks n pool store b3 txid raw confirmedAt dest broadcastPath mineAddr otherAddr
  -- 7c. A payment broadcast while no peer is seated reaches the node once one is, not on the 60 s retry.
  pool.stop
  let b4 ← runNet "broadcaster, no peers" (TxBroadcaster.new pool (some broadcastPath))
  let rawUnfunded4 ← n.wallet #["createrawtransaction", "[]", s!"\{\"{dest}\":0.1}"]
  let funded4 ← Json.parse (← n.wallet #["fundrawtransaction", rawUnfunded4]) |> IO.ofExcept
  let signed4 ← Json.parse (← n.wallet #["signrawtransactionwithwallet", jsonStr funded4 "hex"]) |> IO.ofExcept
  let txid4 ← runNet "broadcast, no peers" (b4.broadcast (ofHex! (jsonStr signed4 "hex")) (some 20.0))
  pool.start
  let relayed ← waitUntil 20_000 (do
    let mp ← n.json #["getrawmempool"]
    return match mp with | .arr xs => xs.any (· == Json.str (displayHex txid4)) | _ => false)
  check "broadcast with no peer seated: relayed as soon as one is" relayed (displayHex txid4)
  b4.shutdown
  -- 8. A fresh Lean scan from genesis.
  n.waitFilterIndex
  let freshStore ← runNet "fresh headers" (HeaderStore.open regtest (some s!"{dir}/fresh-headers.bin"))
  let freshFilters ← runNet "fresh filters" (FilterSyncIO.new pool freshStore 0 (some s!"{dir}/fresh-filters.json"))
  let freshMatches ← IO.mkRef (#[] : Array Nat)
  runNet "fresh filter sync" (freshFilters.sync #[spk] (onMatch := fun m => freshMatches.modify (·.push m.height.toNat)))
  let leanMatches := (← freshMatches.get).qsort (· < ·)
  let leanTip ← freshStore.height
  -- The broadcast transaction may spend the watched coin, so its block can match too.
  check "fresh scan from genesis: tip and match" (leanTip.toNat == (← n.height) && leanMatches.contains fundHeight) s!"{leanMatches}"
def main (_args : List String) : IO UInt32 := runMain "io-test" (progress := true) do
  let tmp ← IO.FS.createTempDir
  let dir := tmp.toString
  say s!"io-test: work dir {dir}"
  try
    withNode dir fun n => do
      offlineChecks dir
      fakeChecks dir
      routedHTTPChecks dir
      nodeChecks dir n
      gatewayChecks n
  finally
    try IO.FS.removeDirAll tmp catch _ => pure ()
