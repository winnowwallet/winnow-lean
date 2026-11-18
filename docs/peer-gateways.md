# Tor and I2P through Tailscale gateways, and Mullvad exit nodes

Fresh installations use **Automatic** routing.
Winnow checks `winnow-tor-gateway:9050` and `winnow-i2p-gateway:4447` when
networking starts in the foreground and when the user reconnects or retries.
Connect the Tailscale app to the intended tailnet first, with MagicDNS enabled.

Discovery asks Tailscale's Quad100 resolver (`100.100.100.100:53`) for these
two names directly. It accepts only IPv4 addresses in Tailscale's `100.64.0.0/10`
range and an unauthenticated SOCKS5 greeting. There is no public DNS fallback,
subnet scan, tailnet API token, embedded router, or additional Tailscale login.
Both lookups run concurrently; each DNS exchange and SOCKS check has a two-second
deadline and is cancelled when networking stops. Addresses are pinned for that
foreground networking generation, never saved to preferences. Discovery does
not monitor Tailscale continuously; reconnect or foreground Winnow after a change.

This is discovery by **name convention**, not by tag. The deployed servers have
`tag:winnow-tor` and `tag:winnow-i2p` for administration, but iOS does not consult
those tags. A tailnet administrator must reserve these names for trusted
gateways and allow access to their SOCKS ports. A SOCKS greeting identifies the
protocol, not the operator or overlay type. Discovery supports conventional
IPv4 tailnet addresses; custom address ranges and IPv6-only discovery need an
extension. Manual gateways support DNS names and bracketed IPv6 addresses.

When either gateway answers, Automatic uses only Tor and I2P: no peer
connection or explorer lookup goes direct, and peers never
see the phone's IP address. When neither answers, it falls back to clearnet
so the wallet keeps syncing, and the home shows a short warning, "Peers see
your IP", whose alert has the whole message and leads to Peers and routing;
unless a Tailscale exit node carries the phone's traffic, which is the next
section. Existing peer provenance and address diversity checks remain in
force. Onion and I2P names have no address block to limit, so while clearnet
is selected automatic Tor and I2P peers together may not take every slot, and
with Tor and I2P both selected and clearnet off neither overlay may; a round
that cannot fill the pool with a mix relaxes that rule for the next one. Gateways see
the destinations clients ask them to reach; Bitcoin peers still undergo the
normal version, compact-filter, header and chain checks.

Settings → Network → Peers and routing → Peer networks offers:

- **Automatic**: discover the conventional gateways; use only them when
  either answers, clearnet when neither does (through the exit node, when one
  is the route).
- **Direct only**: skip discovery and use clearnet peers (likewise).
- **Manual**: choose any nonempty combination of clearnet, Tor and I2P and
  supply each selected overlay's SOCKS address. Edits take effect on **Apply
  routing**.

Tor and I2P destinations are sent by name to their respective SOCKS gateway;
failed overlay connections never dial those destinations directly. Manual,
persisted, census and seed candidates all obey the selection. The census list
each release ships carries validated v3 onion and ordinary base32 I2P entries
beside clearnet ones, held to the same diversity checks.

Explorer requests use direct HTTP when clearnet is selected and SOCKS through
Tor otherwise. I2P-only routing makes no HTTP request at all, so it never asks
its gateway for a public host and explorer requests stay off.
Corrupt saved routing settings keep networking offline until replaced.

[winnowwallet/census `gateways/`](https://github.com/winnowwallet/census/tree/main/gateways)
reproduces the gateway VMs the project ran.

## Mullvad and other Tailscale exit nodes

Tailscale sells Mullvad's servers as exit nodes of a tailnet. While the phone
uses an exit node, what it sends beyond its own networks leaves through that
node, so a clearnet Bitcoin peer sees the node's address and not the phone's.
Winnow cannot switch an exit node on, and cannot ask the Tailscale app which
one is selected. It recognises one that is on, each time networking starts in
the foreground or reconnects, when the routing in effect includes clearnet:

1. **Is an exit node the route?** The routing table answers, and nothing is
   sent: a socket for a public address would leave from the phone's tailnet
   address, the same one a socket for Tailscale's resolver leaves from. Some
   carriers number phones from the same block (100.64.0.0/10), so the answer
   also needs Tailscale's own IPv6 prefix (`fd7a:115c:a1e0::/48`) on the IPv6
   route or, on a tailnet without IPv6, Tailscale's resolver answering a query.
2. **Is it Mullvad's?** Only then, one HTTPS request to
   `am.i.mullvad.net/json`, which answers whether the address it was reached
   from is a Mullvad exit address. It goes through the exit node. Mullvad
   learns nothing it does not already carry when the node is its own; when the
   node is another machine, Mullvad sees that machine's address ask once. A
   phone with no exit node never asks. No answer, or any answer but `true`, is
   not Mullvad.

What follows:

| Route | Peers | The home says |
|---|---|---|
| A gateway answers | Tor and I2P only, as above | "Private: peers reached through Tor" (a lock) |
| No gateway, a Mullvad exit node | Clearnet, through Mullvad | "Mullvad exit node: peers see Mullvad's address, not yours" (a half shield, no warning) |
| No gateway, another exit node | Clearnet, through it | "Peers see your exit node's IP" (a warning) |
| No gateway, no exit node | Clearnet, directly | "Peers see your IP" (a warning, which also suggests a Mullvad exit node) |

Tor and I2P come first because no one party there sees both who is asking and
what for. Mullvad is not that, and the screens do not call it private:

- **Mullvad sees the phone's address and every peer it talks to**, and Bitcoin's
  peer protocol is not encrypted, so Mullvad can read what the wallet asks its
  peers and the transactions it broadcasts. Tailscale knows which of its users
  uses which Mullvad server; it says Mullvad is not told who the user is.
- **The exit address is shared but stable.** Mullvad picks it from the device's
  key, so peers see the same address until that key rotates.
- **An exit node of one's own hides nothing from peers that matters**: its
  address belongs to one person, at home or on a rented server. Winnow cannot
  tell which, so it warns.

While an exit node is the route, the session is held to it. Each connection to
an address beyond the phone's own networks is bound to the tailnet address, so
it leaves through the exit node or not at all; a peer on the local network or
the tailnet (a node of one's own) is reached as ever. A peer given by name is
not looked up, DNS seeds are not asked, and HTTP requests (seed lookups,
explorer requests) are refused once the exit node is no longer the route; the
HTTP check is a look at the routing table just before the request, since the
system's HTTP client cannot be bound.

When the exit node drops or is switched off while Winnow is open, nothing goes
direct. Within about five seconds (the routing table is read again every five)
the home says "Mullvad route dropped" or "Exit node dropped", and peers wait
until the same exit route returns, when Mullvad is asked again whose it is, or
until the person taps **Check gateways and reconnect** or reopens Winnow, when
Automatic decides afresh: gateways, else an exit node, else direct with the
warning. An exit node switched on while Winnow is open is picked up the same
way, at the next foreground or reconnect; connections made before it may not
move into the tunnel until then. In the background Automatic does not step
down silently: after Tor or I2P it will not use Mullvad or connect directly,
and after Mullvad it will not connect directly.

## Validation

`io-test` (`Lean/IOTest.lean`, run by `scripts/ci-regtest` in CI's `lean`
job) checks gateway configuration and
address parsing, MagicDNS answers, discovery, SOCKS5 greetings, routed HTTP
(I2P alone makes no request; Tor alone fetches through its gateway by host
name) and a regtest node reached by an onion name through a SOCKS5 stand-in.
Live Tor and I2P are not involved, and CI has no tailnet of real gateways.
The [2026-09-29 run](security/evidence/live-gateways-2026-09-29.md) of the
Swift app's manual live-gateway check is recorded; this repository has no such
script.

For exit nodes, CI has neither a tailnet nor a Mullvad subscription, so the
routing table's answers and Mullvad's are given to the code: `io-test` checks
what each combination means (an exit node, a carrier's own 100.64.0.0/10, a
tailnet without IPv6), Mullvad's JSON and the one request that asks for it,
that a public peer bound to an address the machine does not have is refused
before anything is sent, and that seeds are not looked up; `records-test` the
screens' words and the backend's part (Mullvad not asked behind a gateway, the
route watched, HTTP refused once it is gone, the background rule);
`backend-test` a wallet syncing with the route reported as Mullvad's, held and
released; and the journey `mullvadExitNode` the screens in the app itself,
with a route test mode gives it (`WINNOW_E2E_EXIT_ROUTE`) and takes away: the
home's line, Peers and routing, the warning when the exit node goes and its
going when the exit node is back. The [2026-11-18 run](security/evidence/exit-node-2026-11-18.md)
recorded the routing table's answers and bound connections on a Mac with a
real exit node on and off, with ordinary tools and with this code. Not tried:
a Mullvad exit node itself, and any of it on an iPhone.

A successful greeting is not proof of Tor/I2P reachability. A physical iPhone
with the Tailscale VPN enabled remains part of device acceptance testing.
