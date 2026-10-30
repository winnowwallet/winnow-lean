# Tor and I2P through Tailscale gateways

Fresh installations use **Automatic** routing in both simple and advanced mode.
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
so the wallet keeps syncing, and simple mode's banner says peers can see the
IP address. Existing peer provenance and address diversity checks remain in
force. Onion and I2P names have no address block to limit, so while clearnet
is selected automatic Tor and I2P peers together may not take every slot, and
with Tor and I2P both selected and clearnet off neither overlay may; a round
that cannot fill the pool with a mix relaxes that rule for the next one. Gateways see
the destinations clients ask them to reach; Bitcoin peers still undergo the
normal version, compact-filter, header and chain checks.

Advanced Settings → Peer networks offers:

- **Automatic**: discover the conventional gateways; use only them when
  either answers, clearnet when neither does.
- **Direct only**: skip discovery and use clearnet peers.
- **Manual**: choose any nonempty combination of clearnet, Tor and I2P and
  supply each selected overlay's SOCKS address. Edits take effect on **Apply
  routing**; these preferences remain active when returning to simple mode.

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

## Validation

`io-test` (`Lean/IOTest.lean`, run by `scripts/ci-regtest` in CI's `extra`
job) checks gateway configuration and
address parsing, MagicDNS answers, discovery, SOCKS5 greetings, routed HTTP
(I2P alone makes no request; Tor alone fetches through its gateway by host
name) and a regtest node reached by an onion name through a SOCKS5 stand-in.
Live Tor and I2P are not involved, and CI has no tailnet of real gateways.
The [2026-09-29 run](security/evidence/live-gateways-2026-09-29.md) of the
Swift app's manual live-gateway check is recorded; this repository has no such
script.

A successful greeting is not proof of Tor/I2P reachability. A physical iPhone
with the Tailscale VPN enabled remains part of device acceptance testing.
