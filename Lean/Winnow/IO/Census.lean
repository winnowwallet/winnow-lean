import Winnow.IO.Diversity
import Winnow.Keys.Unicode

/-! # The census peer list (`Network/Peers/CensusCatalog.swift`)

Untrusted discovery input: the census's daily list of reachable nodes (`peers.json`). Since upstream
e5ce950 the app ships the list current at build time (`scripts/import-census` fetches it into
`build/census/peers.json`, the app bundles it) and reads it with `bundled`; there is no download and no
expiry (peer churn, not a clock, ages it), and the app checks no signature: the import verifies the
census's before the list is bundled, and `census-check` holds the file to `readFile` first. Validation keeps the clearnet array only:
schema 1, a strict `yyyy-MM-dd` date, a positive tip; entries on port 8333 with a printable user agent
≤ 256 bytes, a numeric public host (canonicalized: IPv4-mapped IPv6 collapses to IPv4, IPv6 is printed
as `inet_ntop` does), within 100 blocks of the tip, unique by endpoint and by netblock; sorted by
(host, port). -/

namespace Winnow.IO
open Winnow.Net Lean

structure CensusEntry where
  host : String
  port : UInt16
  userAgent : String
  startHeight : Int32
  deriving BEq, Inhabited, Repr

def CensusEntry.endpoint (e : CensusEntry) : PeerEndpoint := { host := e.host, port := e.port }

structure CensusCatalog where
  schemaVersion : Int := 1
  date : String
  tip : Int32
  /-- Network name → entries, in the order the JSON lists them. -/
  networks : Array (String × Array CensusEntry)
  deriving BEq, Inhabited, Repr

inductive CensusInvalid where
  | schema | date | size | endpoint | height | duplicate | diversity | thin
  deriving BEq, Inhabited, Repr

def CensusInvalid.name : CensusInvalid → String
  | .schema => "schema" | .date => "date" | .size => "size"
  | .endpoint => "endpoint" | .height => "height" | .duplicate => "duplicate" | .diversity => "diversity"
  | .thin => "thin"

inductive CensusError where
  | invalid (e : CensusInvalid)
  /-- `JSONDecoder` refused the document's shape. -/
  | decoding (reason : String)
  deriving Inhabited

def CensusError.name : CensusError → String
  | .invalid e => e.name | .decoding _ => "dataCorrupted"

namespace CensusCatalog

def maximumBytes : Nat := 4 * 1_024 * 1_024
def maximumEntries : Nat := 65_536
def minimumClearnetEntries : Nat := 50

def clearnet (c : CensusCatalog) : Option (Array CensusEntry) := (c.networks.find? (·.1 == "clearnet")).map (·.2)

/-- Days since 1970-01-01 of a proleptic Gregorian date (Howard Hinnant's `days_from_civil`). -/
def daysFromCivil (y m d : Int) : Int :=
  let y := if m ≤ 2 then y - 1 else y
  let era := (if y ≥ 0 then y else y - 399) / 400
  let yoe := y - era * 400
  let mp := (m + 9) % 12
  let doy := (153 * mp + 2) / 5 + d - 1
  let doe := yoe * 365 + yoe / 4 - yoe / 100 + doy
  era * 146097 + doe - 719468

def isLeap (y : Nat) : Bool := (y % 4 == 0 && y % 100 != 0) || y % 400 == 0

/-- `CensusCatalog.day`: a strict `yyyy-MM-dd` (it must round-trip through the formatter). -/
def day (text : String) : Option Int := do
  if text.utf8ByteSize != 10 then none
  let cs := text.toList
  if cs[4]? != some '-' || cs[7]? != some '-' then none
  let digits (a b : Nat) : Option Nat :=
    let part := (cs.drop a).take (b - a)
    if part.all Char.isDigit then some (String.ofList part).toNat! else none
  let y ← digits 0 4
  let m ← digits 5 7
  let d ← digits 8 10
  if y == 0 || m == 0 || m > 12 || d == 0 then none
  let dim := match m with
    | 2 => if isLeap y then 29 else 28
    | 4 | 6 | 9 | 11 => 30
    | _ => 31
  if d > dim then none
  return daysFromCivil y m d

def nearTip (height tip : Int32) : Bool :=
  height ≥ 0 && tip > 0 && (height.toInt - tip.toInt).natAbs ≤ 100

private def publicV4 (b : Array UInt8) : Bool :=
  let (a, x, y) := (b[0]!, b[1]!, b[2]!)
  if a == 0 || a == 10 || a == 127 || a ≥ 224 then false
  else !((a == 100 && 64 ≤ x && x ≤ 127) || (a == 169 && x == 254) || (a == 172 && 16 ≤ x && x ≤ 31) ||
    (a == 192 && x == 168) || (a == 192 && x == 0 && y == 0) || (a == 192 && x == 0 && y == 2) ||
    (a == 192 && x == 88 && y == 99) || (a == 198 && (x == 18 || x == 19)) || (a == 198 && x == 51 && y == 100) ||
    (a == 203 && x == 0 && y == 113))

/-- `inet_ntop(AF_INET6)` for an address with no embedded IPv4 form (global unicast). -/
def ntop6 (b : Array UInt8) : String :=
  (PeerAddress.host { services := 0, ip := ⟨b⟩, port := 0 })

private def canonicalIP (host : String) : Option String := do
  if let some v4 := inetPton4 host then
    if publicV4 v4 then return ".".intercalate (v4.toList.map toString) else none
  let b ← inetPton6 host
  if (b.extract 0 10).all (· == 0) && b[10]! == 255 && b[11]! == 255 then
    let m := b.extract 12 16
    if publicV4 m then return ".".intercalate (m.toList.map toString) else none
  if !((b[0]! &&& 0xe0) == 0x20) then none
  if b[0]! == 0x20 && b[1]! == 0x01 && b[2]! < 2 then none
  if b[0]! == 0x20 && b[1]! == 0x01 && b[2]! == 0x0d && b[3]! == 0xb8 then none
  if b[0]! == 0x20 && b[1]! == 0x02 then none
  if b[0]! == 0x3f && b[1]! == 0xff && b[2]! < 0x10 then none
  return ntop6 b

/-- Numeric public clearnet only; never resolves a name. -/
def canonicalHost (text : String) : Option String :=
  if text.utf8ByteSize > 255 || text != Winnow.Keys.Unicode.trimWhitespace text then none
  else canonicalIP text.toLower

private def validatedEntry (tip : Int32) (e : CensusEntry) : Except CensusInvalid CensusEntry := do
  if e.port != 8333 || e.userAgent.utf8ByteSize > 256 || e.userAgent.toList.any (fun c => c.toNat < 32 || c.toNat == 127) then
    throw .endpoint
  let some host := canonicalHost e.host | throw .endpoint
  if !nearTip e.startHeight tip then throw .height
  return { e with host }

private def validatedEntries (tip : Int32) (entries : Array CensusEntry) (minimum : Nat) :
    Except CensusInvalid (Array CensusEntry) := do
  if entries.size < minimum then throw .thin
  if entries.size > maximumEntries then throw .size
  let mut seen : Array PeerEndpoint := #[]
  let mut blocks : Array String := #[]
  let mut out := #[]
  for input in entries do
    let e ← validatedEntry tip input
    if seen.contains e.endpoint then throw .duplicate
    seen := seen.push e.endpoint
    let some block := netblock e.host | throw .endpoint
    if blocks.contains block then throw .diversity
    blocks := blocks.push block
    out := out.push e
  return out.qsort fun a b => a.host < b.host || (a.host == b.host && a.port < b.port)

/-- `validatedOverlayEntries`: canonical Tor or I2P names on any port, near the tip, no duplicates; every
verified overlay peer is kept (only the bound every list has applies). -/
private def validatedOverlayEntries (tip : Int32) (entries : Array CensusEntry) (network : PeerNetwork) :
    Except CensusInvalid (Array CensusEntry) := do
  if entries.size > maximumEntries then throw .size
  let mut seen : Array PeerEndpoint := #[]
  let mut out := #[]
  for input in entries do
    if !(input.port > 0) || input.userAgent.utf8ByteSize > 256 || input.userAgent.toList.any (fun c => c.toNat < 32 || c.toNat == 127) then
      throw .endpoint
    let some host := network.canonicalOverlayHost input.host | throw .endpoint
    if !nearTip input.startHeight tip then throw .height
    let e := { input with host }
    if seen.contains e.endpoint then throw .duplicate
    seen := seen.push e.endpoint
    out := out.push e
  return out.qsort fun a b => a.host < b.host || (a.host == b.host && a.port < b.port)

/-- `validated(minimumEntries:)`: `minimumEntries` is the floor the wallet applies to a list it will use
(`minimumClearnetEntries`); the tests validate shape alone. The Tor and I2P lists are kept, validated, for
a pool that routes through gateways. -/
def validated (c : CensusCatalog) (minimumEntries : Nat := 0) : Except CensusInvalid CensusCatalog := do
  let some entries := (if c.schemaVersion == 1 then c.clearnet else none) | throw .schema
  if (day c.date).isNone then throw .date
  if !(c.tip > 0) then throw .height
  let mut networks := #[("clearnet", ← validatedEntries c.tip entries minimumEntries)]
  for n in [PeerNetwork.tor, .i2p] do
    if let some overlay := (c.networks.find? (·.1 == n.rawValue)).map (·.2) then
      networks := networks.push (n.rawValue, ← validatedOverlayEntries c.tip overlay n)
  return { c with networks }

/-- The entries of one network, if the list carries it. -/
def entries (c : CensusCatalog) (n : PeerNetwork) : Array CensusEntry :=
  ((c.networks.find? (·.1 == n.rawValue)).map (·.2)).getD #[]

private def entryOf (j : Json) : Except String CensusEntry := do
  let .str host ← j.getObjVal? "host" | throw "host"
  let some port := PersistedPeers.jsonNat? (← j.getObjVal? "port") 65535 | throw "port"
  let .str userAgent ← j.getObjVal? "userAgent" | throw "userAgent"
  let some h := PersistedPeers.jsonInt? (← j.getObjVal? "startHeight") (-2147483648) 2147483647 | throw "startHeight"
  return { host, port := port.toUInt16, userAgent, startHeight := Int32.ofInt h }

/-- `JSONDecoder().decode(CensusCatalog.self, …)`: every network must hold well-formed entries. -/
def ofJson (j : Json) : Except String CensusCatalog := do
  let some schemaVersion := PersistedPeers.jsonInt? (← j.getObjVal? "schemaVersion") (-(2 ^ 63)) (2 ^ 63 - 1) | throw "schemaVersion"
  let .str date ← j.getObjVal? "date" | throw "date"
  let some tip := PersistedPeers.jsonInt? (← j.getObjVal? "tip") (-2147483648) 2147483647 | throw "tip"
  let .obj kvs ← j.getObjVal? "networks" | throw "networks"
  let mut networks := #[]
  for (k, v) in kvs.toArray do
    let .arr xs := v | throw s!"networks.{k}"
    networks := networks.push (k, ← xs.mapM entryOf)
  return { schemaVersion, date, tip := Int32.ofInt tip, networks }

def decode (data : ByteArray) (minimumEntries : Nat := 0) : Except CensusError CensusCatalog := do
  if data.size > maximumBytes then throw (.invalid .size)
  let some text := String.fromUTF8? data | throw (.decoding "not UTF-8")
  let j ← (Json.parse text).mapError CensusError.decoding
  let c ← (ofJson j).mapError CensusError.decoding
  (c.validated minimumEntries).mapError CensusError.invalid

/-- A `peers.json` read and held to the rules `bundled` applies (at most `maximumBytes`, then `decode`
with `minimumClearnetEntries`): `census-check` runs it on the file a build is about to ship. -/
def readFile (path : System.FilePath) : IO (Except CensusError CensusCatalog) := do
  return decode (← readUpTo path maximumBytes) minimumClearnetEntries

/-- `CensusCatalog.bundled`: the census the app was built with, `peers.json` in the app bundle (beside
the executable, which on iOS is the bundle's root), held to `minimumClearnetEntries`. None when the
build carries no list or it does not validate, and outside an app bundle (the tests). -/
def bundled : IO (Option CensusCatalog) := do
  try
    let some dir := (← IO.appPath).parent | return none
    let path := dir / "peers.json"
    unless ← path.pathExists do return none
    return (← readFile path).toOption
  catch _ => return none

end CensusCatalog

end Winnow.IO
