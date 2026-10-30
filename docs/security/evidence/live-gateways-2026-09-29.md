[Back to evidence README](README.md)

# Live Tor and I2P gateway check, 2026-09-29

A manual run from a Mac on the tailnet that runs the project's two
[peer gateways](../../peer-gateways.md). CI has no tailnet, so this is the
only live evidence for #181's routing. No wallet addresses or transactions were
sent. The simulator journey below shares the Mac's network; the physical-iPhone
run is recorded in #181.

- **Revision:** WalletCore identical to main `8661469` (#181).
- **Census input:** `census/peers.json` dated 2026-09-28 from
  `census.winnowwallet.com`, SHA-256 `cec282a3ad5e9af72436d5fc004175434186ed7a0f8ce21ec679439cd7b764d7`,
  with `peers.json.sig` SHA-256 `30a1b77c4caa0ca62e06b83a8b6f6db7b044246717b12fe87be4d6337316a0cd`.
  It listed 974 clearnet, 2,000 Tor and 2,000 I2P endpoints.

## Repository check (15:54Z)

```sh
DEVELOPER_DIR=/Applications/Xcode.app/Contents/Developer \
  scripts/check-live-gateways peers.json
```

| Step | Result |
|---|---|
| Discovery through `100.100.100.100` | `winnow-tor-gateway` → `100.75.175.127:9050`, `winnow-i2p-gateway` → `100.74.30.8:4447` |
| Census from the I2P mirror through the I2P gateway | 945,095 bytes, publisher signature verified |
| Bitcoin handshake through the Tor gateway | `/Satoshi:29.3.0/Knots:20260507/` |
| Bitcoin handshake through the I2P gateway | `/Satoshi:31.1.0/` |

`TailnetGatewayDiscoveryTests.deployedMagicDNSGateways` passed in 24.6 seconds.

## Simulator UI journey (18:18–18:21Z)

```sh
scripts/check-live-gateways-ui "platform=iOS Simulator,id=<iPhone 18 Pro>" <new evidence directory>
```

Built from main `a63e763` with Xcode 27.0 and run on an iPhone 18 Pro
simulator (iOS 27.0) whose Mac was on the tailnet.
`LiveGatewayDeviceTests.testRealGatewaysDiscoverRouteAndRefresh` passed in
163 seconds: Automatic discovered both gateways, I2P alone refreshed the
census from the mirror and seated a `.b32.i2p` peer, and Tor alone seated an
onion peer. A simulator shares the Mac's network, so this does not replace the
physical-iPhone run recorded in #181.

## Independent cross-checks (15:15–15:25Z)

These used ordinary tools rather than WalletCore:

- Both gateways answered an unauthenticated SOCKS5 greeting (`05 00`).
- `curl --socks5-hostname 100.74.30.8:4447` fetched the mirror's `peers.json`
  in 15.3 seconds; its SHA-256 matched the public file above.
- A Python client sent a Bitcoin `version` message through each gateway to six
  randomly chosen Tor and six I2P census endpoints. All 12 answered with
  `version`, reported height 969,172 and advertised compact filters
  (`NODE_COMPACT_FILTERS`). Tor handshakes took 5.4–11.9 seconds, I2P 2.6–4.9.

| Network | Answered | Software |
|---|---|---|
| Tor | 6 / 6 | Core 31.1.0 ×4, 30.2.0, 29.4.0 |
| I2P | 6 / 6 | Core 31.1.0 ×3, 31.0.0 ×2, Knots 29.3.0 (20260210) |

A successful handshake shows reachability through the gateways at that time;
it says nothing about the operators' independence or honesty, which the
wallet's header and filter checks still decide.
