import Winnow.IO.Diversity
import Winnow.IO.Http

/-! # DNS seeds (`Network/Peers/SeedResolver.swift`)

DNS-over-HTTPS (dns-json, Cloudflare's `https://1.1.1.1/dns-query` by default) through the routed
HTTP client, A and AAAA in parallel; when that yields no acceptable address, the system resolver
(`getaddrinfo`, here Std.Async.DNS). Both paths drop non-public answers unless `allowPrivate` (custom
signets). Seeds are resolved in parallel in a shuffled order and the results de-duplicated in arrival
order. `lookup` is the injectable seam, as in Swift. -/

namespace Winnow.IO
open Winnow.Net Lean

def defaultDoHEndpoint : String := "https://1.1.1.1/dns-query"

namespace DNSJSON

/-- Host strings of the A (1) and AAAA (28) answers; a non-zero `Status` gives none. Throws (as
`JSONDecoder` does) on a body that is not the dns-json shape. -/
def hosts (data : ByteArray) : Except String (Array String) := do
  let some text := String.fromUTF8? data | throw "not UTF-8"
  let j ← Json.parse text
  let some status := PersistedPeers.jsonInt? (← j.getObjVal? "Status") (-(2 ^ 63)) (2 ^ 63 - 1) | throw "Status"
  let answers ← match j.getObjVal? "Answer" with
    | .ok .null => pure #[]
    | .ok (.arr xs) => xs.mapM fun a => do
        let some t := PersistedPeers.jsonInt? (← a.getObjVal? "type") (-(2 ^ 63)) (2 ^ 63 - 1) | throw "type"
        let .str d ← a.getObjVal? "data" | throw "data"
        pure (t, d)
    | .ok _ => throw "Answer"
    | .error _ => pure #[]
  if status != 0 then return #[]
  return answers.filterMap fun (t, d) =>
    if t == 1 || t == 28 then
      let h := d.trimAscii.toString
      if h.isEmpty then none else some h
    else none

end DNSJSON

/-- Percent-encoding of a query value (`URLQueryItem`). -/
def percentEncode (s : String) : String :=
  let d := "0123456789ABCDEF".toList.toArray
  s.toUTF8.foldl (fun acc b =>
    let c := Char.ofNat b.toNat
    if b < 0x80 && (c.isAlphanum || c == '-' || c == '.' || c == '_' || c == '~') then acc.push c
    else (acc.push '%').push d[b.toNat / 16]! |>.push d[b.toNat % 16]!) ""

structure SeedResolver where
  /-- host, port, allowPrivate → endpoints. -/
  lookup : String → UInt16 → Bool → IO (Array PeerEndpoint)

namespace SeedResolver

def maximumDoHBytes : Nat := 128 * 1024

/-- The system resolver: numeric hosts of every A/AAAA record. -/
def getaddrinfo (host : String) (port : UInt16) : IO (Array PeerEndpoint) := do
  match ← (Std.Async.DNS.getAddrInfo host "").block.toBaseIO with
  | .ok addrs => return addrs.map fun a => { host := toString a, port }
  | .error _ => return #[]

def endpoints (hosts : Array String) (port : UInt16) (allowPrivate : Bool) : Array PeerEndpoint := Id.run do
  let mut seen : Array String := #[]
  let mut out := #[]
  for h in hosts do
    if seen.contains h then continue
    seen := seen.push h
    if !SeedAddressFilter.accepts h allowPrivate then continue
    out := out.push { host := h, port }
  return out

/-- A and AAAA over dns-json, in parallel; a failed fetch or body contributes nothing. -/
def dohHosts (name : String) (fetchJSON : String → String → NetM ByteArray) : IO (Array String) := do
  let tasks ← #["A", "AAAA"].mapM fun t => IO.asTask (do
    match ← (fetchJSON name t).attempt with
    | .ok data => return (DNSJSON.hosts data).toOption.getD #[]
    | .error _ => return #[])
  let mut out := #[]
  for t in tasks do
    match ← IO.wait t with
    | .ok hs => out := out ++ hs
    | .error _ => pure ()
  return out

def resolveWith (host : String) (port : UInt16) (allowPrivate : Bool)
    (fetchJSON : String → String → NetM ByteArray) (systemResolve : String → UInt16 → IO (Array PeerEndpoint)) :
    IO (Array PeerEndpoint) := do
  let doh := endpoints (← dohHosts host fetchJSON) port allowPrivate
  if !doh.isEmpty then return doh
  let system := (← systemResolve host port).map (·.host)
  return endpoints system port allowPrivate

def live (fetchJSON : String → String → NetM ByteArray)
    (systemResolve : String → UInt16 → IO (Array PeerEndpoint) := getaddrinfo) : SeedResolver :=
  { lookup := fun host port allowPrivate => resolveWith host port allowPrivate fetchJSON systemResolve }

/-- DoH through the routed client (`Accept: application/dns-json`, 128 KiB cap). -/
def routed (client : RoutedHTTPClient) (endpoint : String := defaultDoHEndpoint)
    (systemResolve : String → UInt16 → IO (Array PeerEndpoint) := getaddrinfo) : SeedResolver :=
  live (fun name type => client.get s!"{endpoint}?name={percentEncode name}&type={percentEncode type}"
    maximumDoHBytes (accept := some "application/dns-json")) systemResolve

def resolve (r : SeedResolver) (host : String) (port : UInt16) (allowPrivate : Bool) : IO (Array PeerEndpoint) :=
  r.lookup host port allowPrivate

/-- Every seed, shuffled, in parallel; flattened and de-duplicated. -/
def resolveSeeds (r : SeedResolver) (seeds : Array String) (port : UInt16) (allowPrivate : Bool) :
    IO (Array PeerEndpoint) := do
  if seeds.isEmpty then return #[]
  let order ← shuffle seeds
  let tasks ← order.mapM fun s => IO.asTask (r.resolve s port allowPrivate)
  let mut collected := #[]
  for t in tasks do
    match ← IO.wait t with
    | .ok batch => collected := collected ++ batch
    | .error _ => pure ()
  let mut out : Array PeerEndpoint := #[]
  for e in collected do
    if !out.contains e then out := out.push e
  return out

end SeedResolver
end Winnow.IO
