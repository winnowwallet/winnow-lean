import Winnow.IO.Base
import Winnow.Keys.Unicode

/-! # Peer provenance and diversity (`Network/Peers/PeerDiversity.swift`, `SeedAddressFilter` of
`SeedResolver.swift`), and the persisted peers file

`PeerSource` is the Net area's (`Winnow.Net.PeerSource`). IP literals are parsed with a port of the BSD
`inet_pton` that Darwin's libc uses (dotted quads without leading zeros; IPv6 with one `::`, at most
four hex digits a group, an optional trailing dotted quad), so these functions answer as the Swift
ones do without calling the C library.

`peers.json` (version 2): `{"version":2,"peers":[{"host":…,"port":…,"source":…}]}`, the field order
`JSONEncoder` writes; the legacy bare array of `{"host","port"}` is still read (as `persisted`). -/

namespace Winnow.IO
open Winnow.Net Lean

/-! ## IP literals -/

/-- BSD `inet_pton4`. -/
def inetPton4 (s : String) : Option (Array UInt8) := Id.run do
  let mut out : Array Nat := #[0]
  let mut sawDigit := false
  let mut octets := 0
  for ch in s.toList do
    if ch.isDigit then
      let cur := out.back!
      let v := cur * 10 + (ch.toNat - '0'.toNat)
      if sawDigit && cur == 0 then return none
      if v > 255 then return none
      out := out.set! (out.size - 1) v
      if !sawDigit then
        octets := octets + 1
        if octets > 4 then return none
        sawDigit := true
    else if ch == '.' && sawDigit then
      if octets == 4 then return none
      out := out.push 0
      sawDigit := false
    else return none
  if octets < 4 then return none
  return some (out.map (·.toUInt8))

private def hexVal (c : Char) : Option Nat :=
  if c.isDigit then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c && c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else none

/-- BSD `inet_pton6`. -/
def inetPton6 (s : String) : Option (Array UInt8) := Id.run do
  let mut cs := s.toList
  if cs.head? == some ':' then
    if (cs.drop 1).head? != some ':' then return none
    cs := cs.drop 1
  let mut tp : Array UInt8 := #[]
  let mut colonp : Option Nat := none
  let mut curtok := cs
  let mut sawX := false
  let mut seen := 0
  let mut val := 0
  let mut rest := cs
  let mut doneV4 := false
  while !rest.isEmpty do
    let ch := rest.head!
    rest := rest.tail
    if let some d := hexVal ch then
      val := val * 16 + d
      seen := seen + 1
      if seen > 4 then return none
      sawX := true
      continue
    if ch == ':' then
      curtok := rest
      if !sawX then
        if colonp.isSome then return none
        colonp := some tp.size
        continue
      else if rest.isEmpty then return none
      if tp.size + 2 > 16 then return none
      tp := tp.push (val / 256).toUInt8 |>.push (val % 256).toUInt8
      sawX := false; seen := 0; val := 0
      continue
    if ch == '.' && tp.size + 4 ≤ 16 then
      match inetPton4 (String.ofList curtok) with
      | some v4 => tp := tp ++ v4; sawX := false; doneV4 := true; break
      | none => return none
    return none
  if sawX then
    if tp.size + 2 > 16 then return none
    tp := tp.push (val / 256).toUInt8 |>.push (val % 256).toUInt8
  if let some cp := colonp then
    if tp.size == 16 then return none
    let head := tp.extract 0 cp
    let tail := tp.extract cp tp.size
    tp := head ++ Array.replicate (16 - tp.size) 0 ++ tail
  let _ := doneV4
  if tp.size != 16 then return none
  return some tp

/-! ## `SeedAddressFilter` -/

namespace SeedAddressFilter

def ipv4Octets (host : String) : Option (Array UInt8) := inetPton4 host
def ipv6Octets (host : String) : Option (Array UInt8) := inetPton6 host

def isIPv4Mapped (b : Array UInt8) : Bool :=
  b.size == 16 && (b.extract 0 10).all (· == 0) && b[10]! == 0xFF && b[11]! == 0xFF

def isPublicIPv4 (o : Array UInt8) : Bool :=
  let (a, b) := (o[0]!, o[1]!)
  !(a == 0 || a == 10 || a == 127 || (a == 169 && b == 254) || (a == 172 && (b &&& 0xF0) == 16) ||
    (a == 192 && b == 168) || a ≥ 224)

def isPublicIPv6 (b : Array UInt8) : Bool :=
  !(b.all (· == 0) || ((b.extract 0 15).all (· == 0) && b[15]! == 1) || (b[0]! &&& 0xFE) == 0xFC ||
    (b[0]! == 0xFE && (b[1]! &&& 0xC0) == 0x80) || b[0]! == 0xFF)

/-- `allowPrivate` keeps RFC1918/loopback/link-local (custom signets); non-literals are refused. -/
def accepts (host : String) (allowPrivate : Bool) : Bool :=
  match ipv4Octets host with
  | some v4 => allowPrivate || isPublicIPv4 v4
  | none => match ipv6Octets host with
    | some v6 =>
      if isIPv4Mapped v6 then allowPrivate || isPublicIPv4 (v6.extract 12 16)
      else allowPrivate || isPublicIPv6 v6
    | none => false

end SeedAddressFilter

private def hex2 (b : UInt8) : String :=
  let d := "0123456789abcdef".toList.toArray
  String.ofList [d[b.toNat / 16]!, d[b.toNat % 16]!]

/-- The address block a peer shares with its neighbours (IPv4 /16, IPv6 /32); `none` for hostnames and
non-public addresses, which the diversity rules never restrict. -/
def netblock (host : String) : Option String :=
  match SeedAddressFilter.ipv4Octets host with
  | some o => if SeedAddressFilter.isPublicIPv4 o then some s!"v4:{o[0]!}.{o[1]!}" else none
  | none => match SeedAddressFilter.ipv6Octets host with
    | none => none
    | some b =>
      if SeedAddressFilter.isIPv4Mapped b then
        let m := b.extract 12 16
        if SeedAddressFilter.isPublicIPv4 m then some s!"v4:{m[0]!}.{m[1]!}" else none
      else if SeedAddressFilter.isPublicIPv6 b then
        some s!"v6:{hex2 b[0]!}{hex2 b[1]!}:{hex2 b[2]!}{hex2 b[3]!}"
      else none

def _root_.Winnow.Net.PeerEndpoint.netblock (e : PeerEndpoint) : Option String := Winnow.IO.netblock e.host

/-! ## Candidates and the diversity policy -/

structure PeerCandidate where
  endpoint : PeerEndpoint
  source : PeerSource
  deriving BEq, Inhabited, Repr

/-- Which network a peer is on (`PeerNetwork`, PeerGateways.swift): `.onion` names are Tor, `.i2p` I2P. -/
inductive PeerNetwork where
  | clearnet | tor | i2p
  deriving BEq, Repr, Inhabited, DecidableEq, Hashable

namespace PeerNetwork
def allCases : List PeerNetwork := [.clearnet, .tor, .i2p]
def rawValue : PeerNetwork → String | .clearnet => "clearnet" | .tor => "tor" | .i2p => "i2p"
def ofRaw? : String → Option PeerNetwork
  | "clearnet" => some .clearnet | "tor" => some .tor | "i2p" => some .i2p | _ => none

/-- `PeerNetwork(host:)`: lower-cased, leading and trailing dots trimmed, by suffix. -/
def ofHost (host : String) : PeerNetwork :=
  let h := String.ofList ((host.toLower.toList.dropWhile (· == '.')).reverse.dropWhile (· == '.')).reverse
  if h.endsWith ".onion" then .tor else if h.endsWith ".i2p" then .i2p else .clearnet

/-- The canonical name of a Tor (56 base32 characters + `.onion`) or I2P (52 + `.b32.i2p`) host. -/
def canonicalOverlayHost (n : PeerNetwork) (host : String) : Option String :=
  if host != Winnow.Keys.Unicode.trimWhitespace host then none else
  let host := host.toLower
  let (suffix, length) := match n with
    | .tor => (".onion", 56) | .i2p => (".b32.i2p", 52) | .clearnet => ("", 0)
  if n == .clearnet || !host.endsWith suffix then none else
  let name := (host.toList.take (host.length - suffix.length))
  if name.length == length && name.all (fun c => ('a' ≤ c && c ≤ 'z') || ('2' ≤ c && c ≤ '7')) then some host else none
end PeerNetwork

/-- A Tor or I2P destination, reached through its gateway by name. -/
def _root_.Winnow.Net.PeerEndpoint.isOverlay (e : PeerEndpoint) : Bool := PeerNetwork.ofHost e.host != .clearnet

/-- The seating rules (`DiversityPolicy`), each a ceiling rather than a quota: one seat per netblock; no
source class in every seat; while clearnet is selected, Tor and I2P together never in every seat (their
names have no netblock); and with Tor and I2P both selected and clearnet off (`overlayMix`), neither overlay
in every seat. Manual peers are exempt from all but the netblock rule. -/
structure DiversityPolicy where
  peerCount : Nat
  clearnetSelected : Bool := true
  overlayMix : Bool := false

def DiversityPolicy.admits (p : DiversityPolicy) (candidate : PeerCandidate) (seated : Array PeerCandidate) : Bool :=
  let blocked := match candidate.endpoint.netblock with
    | some block => seated.any (·.endpoint.netblock == some block)
    | none => false
  if blocked then false
  else if candidate.source == .manual || !(p.peerCount > 1) then true
  else if p.clearnetSelected && candidate.endpoint.isOverlay &&
      (seated.filter (·.endpoint.isOverlay)).size ≥ p.peerCount - 1 then false
  else if p.overlayMix && candidate.endpoint.isOverlay &&
      (seated.filter (PeerNetwork.ofHost ·.endpoint.host == PeerNetwork.ofHost candidate.endpoint.host)).size ≥ p.peerCount - 1 then false
  else (seated.filter (·.source == candidate.source)).size < p.peerCount - 1

/-! ## `peers.json` -/

namespace PersistedPeers

def currentVersion : Nat := 2
def maximumPeersFileBytes : Nat := 256 * 1_024

def encode (candidates : Array PeerCandidate) : ByteArray :=
  let records := candidates.toList.map fun c =>
    s!"\{\"host\":{jsonString c.endpoint.host},\"port\":{c.endpoint.port},\"source\":{jsonString c.source.rawValue}}"
  s!"\{\"version\":{currentVersion},\"peers\":[{",".intercalate records}]}".toUTF8

/-- A JSON integer in `0 … max` (`JSONDecoder` refuses fractions and out-of-range values). -/
def jsonNat? (j : Json) (max : Nat) : Option Nat :=
  match j with
  | .num n =>
    let scale : Int := 10 ^ n.exponent
    if n.mantissa % scale != 0 then none
    else let v := n.mantissa / scale; if v < 0 || v > max then none else some v.toNat
  | _ => none

def jsonInt? (j : Json) (lo hi : Int) : Option Int :=
  match j with
  | .num n =>
    let scale : Int := 10 ^ n.exponent
    if n.mantissa % scale != 0 then none
    else let v := n.mantissa / scale; if v < lo || v > hi then none else some v
  | _ => none

private def endpointOf (j : Json) : Option PeerEndpoint := do
  let .str host ← (j.getObjVal? "host").toOption | none
  let port ← jsonNat? (← (j.getObjVal? "port").toOption) 65535
  return { host, port := port.toUInt16 }

/-- Reads either format; `none` when it is neither. -/
def decode (data : ByteArray) : Option (Array PeerCandidate) := do
  let text ← String.fromUTF8? data
  let j ← (Json.parse text).toOption
  let versioned : Option (Array PeerCandidate) := do
    let v ← jsonNat? (← (j.getObjVal? "version").toOption) (2 ^ 63)
    let .arr peers ← (j.getObjVal? "peers").toOption | none
    let records ← peers.mapM fun r => do
      let e ← endpointOf r
      let .str s ← (r.getObjVal? "source").toOption | none
      let src ← PeerSource.ofRaw? s
      return ({ endpoint := e, source := src } : PeerCandidate)
    if v == currentVersion then some records else none
  match versioned with
  | some r => some r
  | none =>
    let .arr xs := j | none
    xs.mapM fun x => do return { endpoint := ← endpointOf x, source := .persisted }

/-- `PeerPool.boundedRead`: the file only when it is no larger than the writer ever makes it. -/
def boundedRead (path : System.FilePath) : IO (Option ByteArray) := do
  let some size ← fileSize? path | return none
  if size > maximumPeersFileBytes then return none
  try
    let data ← IO.FS.readBinFile path
    return if data.size ≤ maximumPeersFileBytes then some data else none
  catch _ => return none

end PersistedPeers
end Winnow.IO
