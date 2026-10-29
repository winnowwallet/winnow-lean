-- The I/O area: transport, peers, census, broadcast and the sync loops, over Lean TCP (aggregator).
import Winnow.IO.Base
import Winnow.IO.Transport
import Winnow.IO.Http
import Winnow.IO.Diversity
import Winnow.IO.Seeds
import Winnow.IO.Census
import Winnow.IO.Gateways
import Winnow.IO.Headers
import Winnow.IO.Pool
import Winnow.IO.Filters
import Winnow.IO.Mempool
import Winnow.IO.Broadcast

/-! # The I/O area (port of WalletCore's networking that talks to real peers)

| Lean | Swift (Sources/WalletCore/Network/…) |
|---|---|
| `IO/Base.lean` | the error enums' cases and `errorDescription`s; `Duration` timers, `.atomic` writes, `AsyncStream` |
| `IO/Transport.lean` | `Transport/PeerConnection.swift` (on `Std.Async.TCP`, libuv) |
| `IO/Http.lean` | `Transport/RoutedHTTPClient.swift`: policy in Lean, the fetch injected (`HttpFetch`; `curlFetch` for tests) |
| `IO/Diversity.lean` | `Peers/PeerDiversity.swift`, `SeedAddressFilter` (BSD `inet_pton` ported), `PersistedPeers` (peers.json) |
| `IO/Seeds.lean` | `Peers/SeedResolver.swift` (DoH through `RoutedHTTPClient`, `getaddrinfo` via `Std.Async.DNS`) |
| `IO/Census.lean` | `Peers/CensusCatalog.swift` (the list shipped with the build: `CensusCatalog.bundled`) |
| `IO/Gateways.lean` | `Peers/PeerGateways.swift`, `Peers/TailnetGatewayDiscovery.swift` (MagicDNS over `Std.Async.UDP`) |
| `IO/Headers.lean` | `Headers/HeaderChain.swift`: file read/write and `sync(using:)` (the chain is Net's pure `HeaderChain`) |
| `IO/Pool.lean` | `Peers/PeerPool.swift` |
| `IO/Filters.lean` | `Filters/FilterSync.swift`: `sync`, `transaction(_:at:)`, filters.json (decisions: Net's `FilterSync`) |
| `IO/Mempool.lean` | `Mempool/MempoolWindow.swift`: timers, listeners, getdata (bookkeeping: Net's `MempoolWindow`) |
| `IO/Broadcast.lean` | `Broadcast/TxBroadcaster.swift`, broadcast.json |

Actors are structures over `IO.Ref` state changed by atomic `modifyGet`s (the chain is under a
`Std.Mutex`); async sequences are `EventStream`s; long-lived loops (one receive loop per connection,
the pool monitor, stream listeners) are dedicated threads; timeouts and backoff are libuv timers.
Errors are one `NetError` with a case per Swift error type (`NetM := EIO NetError`).

Tests: `Lean/IOTest.lean` (`lake build io-test && .lake/build/bin/io-test [--swift <oracle-io>]`), against
a disposable regtest bitcoind and scripted fake peers; `LeanOracle/IO/main.swift` runs the Swift
side on the same node (built outside SwiftPM:
`swiftc -O -I .build/release -Xcc -fmodule-map-file=.build/out/Intermediates.noindex/GeneratedModuleMaps/libsecp256k1.modulemap
LeanOracle/IO/main.swift .build/release/{WalletCore,P256K,libsecp256k1}.o -o oracle-io`
after `swift build -c release -Xswiftc -enable-testing --product oracle-net`).

## Not covered (by the port or by the tests)

* No TLS in Lean: every HTTPS fetch (census list, DoH, explorer) is the injected `HttpFetch`; the live
  census/DoH endpoints are not exercised (no network in the tests). In-flight HTTP cancellation is not
  ported (a cancelled client only refuses new requests).
* No `fsync` and no `seek` in Lean's file API: header appends flush instead of `synchronize()`, and a
  file longer than its count is rewritten whole. No iOS data-protection class on written files.
* No task cancellation: Swift's `CancellationError` paths (connect torn down on cancel, sync loops
  stopping) have no trigger here; `NetError.cancelled` exists for callers that want to throw it.
* A refused TCP dial fails at once (`disconnected`) where NWConnection waits in `.waiting` until the
  dial timeout (`timeout`); hostnames are dialled at their first resolved address.
* Not tested against a node: census-driven candidate selection, DNS-seed dialling, stale-tip eviction,
  `catchUp`, the cfcheckpt/cfheaders votes with disagreeing peers (only the single-peer degraded mode
  and agreeing votes run), deprioritization and fee-floor events, the backlog's byte ceiling, and the
  keepalive's idle timeout. iOS reconnect-on-foreground is the app's job (PORT.md). -/
