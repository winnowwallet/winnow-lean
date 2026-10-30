import Std.Data.HashSet
import Winnow.Keys.BIP39
import Winnow.Wallet.Characters
import Winnow.Wallet.SwiftJSON
import Winnow.IO.Base
import WinnowApp.Pure

/-! # E2EMode.swift: the launch-environment test mode

Inert unless the shell reports a debug build (`build` capability; Swift compiles the mode out of
Release with `#if DEBUG`) and the app is launched with `WINNOW_E2E=1`. Then:

* storage moves to `Application Support/BTCSwiftE2E-<run>` and the Keychain to the service
  `org.btc-swift.wallet.e2e.<run>` (settings live in the storage directory, so the defaults suite moves
  with it); `WINNOW_E2E_RESET=1` wipes both;
* the wallet's entropy is pinned (`WINNOW_E2E_ENTROPY` hex or `WINNOW_E2E_MNEMONIC`) — without one the
  launch fails closed, because capture runs publish their screenshots;
* a manual peer, a custom signet challenge, the peer count, the sync interval, the network, the first
  tab, advanced mode and the clipboard can be set (the census URL and keys went with the census download,
  upstream e5ce950);
* device authentication is skipped unless `WINNOW_E2E_DEVICE_AUTH=1`;
* (Lean only) `WINNOW_E2E_LEDGER=<entropy hex>` makes a simulated Ledger with that seed the app's Ledger;
  set but unreadable, the launch fails closed;
* events are appended to `story-events.jsonl` in the run's storage directory, refusing any field that
  looks like a secret.

Differences: `safeRunID` keeps ASCII letters and digits (Swift keeps any `Character.isLetter` /
`isNumber`); the journal writes `fields` with sorted keys (Swift's dictionary order is unspecified). -/

namespace WinnowApp.E2E
open Winnow

structure Mode where
  runID : String
  peer : Option String
  challenge : Option ByteArray
  entropy : Option ByteArray
  reset : Bool
  clipboard : Option String
  forcedNetwork : Option Network
  initialTab : Option String
  requireDeviceAuthentication : Bool
  advancedMode : Bool
  controlFile : Option String
  peerCount : Option Nat
  syncIntervalSeconds : Option Float
  /-- `WINNOW_E2E_LEDGER` (Lean only; upstream's test mode has no Ledger): the entropy (hex) of a simulated
  Ledger's seed, which then answers in place of Bluetooth. `some none` when it is set but unreadable,
  which the launch refuses rather than fall back to the radio. -/
  ledgerEntropy : Option (Option ByteArray) := none
  /-- `WINNOW_E2E_LIVE_GATEWAYS=1`: let Automatic routing probe the real tailnet. Only the live gateway
  journey sets it; every other run keeps discovery off so it never depends on the developer's network. -/
  liveGateways : Bool := false

inductive Resolution where
  | inactive
  | active (m : Mode)
  | missingPinnedEntropy

def keychainServicePrefix : String := "org.btc-swift.wallet.e2e"

/-- `BitcoinNetwork(rawValue:)`. -/
def networkOfRaw : String → Option Network
  | "mainnet" => some .mainnet
  | "signet" => some .signet
  | "regtest" => some .regtest
  | _ => none

/-- `Int(String)`: an optional sign and decimal digits, nothing else, within `Int`'s 64 bits. -/
def swiftInt? (s : String) : Option Int :=
  let (neg, digits) := match s.toList with
    | '-' :: rest => (true, rest)
    | '+' :: rest => (false, rest)
    | cs => (false, cs)
  if digits.isEmpty || !digits.all Char.isDigit then none
  else
    let n : Nat := digits.foldl (fun acc c => acc * 10 + (c.toNat - '0'.toNat)) 0
    let v : Int := if neg then -(n : Int) else n
    if v < -(2 ^ 63 : Int) || v ≥ (2 ^ 63 : Int) then none else some v

/-- `entropyFrom(mnemonic:)`: words split on spaces (empty pieces dropped), each looked up in the
English list, the bits packed without a checksum check, as Swift does. -/
def entropyFrom (mnemonic : String) : Option ByteArray := do
  let words := (mnemonic.splitOn " ").filter (!·.isEmpty)
  let mut bits : Array Bool := #[]
  for w in words do
    let some i := Keys.BIP39.wordlist.idxOf? w | none
    for k in (List.range 11).reverse do bits := bits.push ((i >>> k) &&& 1 == 1)
  let checksumLength := words.length / 3
  let entropyLength := (bits.size - checksumLength) / 8
  let mut out := ByteArray.mk (Array.replicate entropyLength 0)
  for i in [0:entropyLength * 8] do
    if bits[i]! then out := out.set! (i / 8) (out[i / 8]! ||| ((1 : UInt8) <<< (7 - (i % 8)).toUInt8))
  return out

/-- `E2EMode.resolve(environment:)`, over a lookup of the launch environment. -/
def resolve (env : String → Option String) : Resolution :=
  if env "WINNOW_E2E" != some "1" then .inactive else
  let entropy : Option ByteArray :=
    match env "WINNOW_E2E_ENTROPY" with
    | some hex => Wire.dataOfHex? hex
    | none => (env "WINNOW_E2E_MNEMONIC").bind entropyFrom
  match entropy with
  | none => .missingPinnedEntropy
  | some e =>
    .active
      { runID := (env "WINNOW_E2E_RUN").getD "main"
        peer := env "WINNOW_E2E_PEER"
        challenge := (env "WINNOW_E2E_CHALLENGE").bind Wire.dataOfHex?
        entropy := some e
        reset := env "WINNOW_E2E_RESET" == some "1"
        clipboard := env "WINNOW_E2E_CLIPBOARD"
        forcedNetwork := (env "WINNOW_E2E_NETWORK").bind networkOfRaw
        initialTab := env "WINNOW_E2E_TAB"
        requireDeviceAuthentication := env "WINNOW_E2E_DEVICE_AUTH" == some "1"
        advancedMode := env "WINNOW_E2E_ADVANCED" == some "1"
        controlFile := env "WINNOW_E2E_CONTROL_FILE"
        peerCount := (env "WINNOW_E2E_PEER_COUNT").bind swiftInt? |>.bind fun n => if n > 0 then some n.toNat else none
        syncIntervalSeconds := (env "WINNOW_E2E_SYNC_INTERVAL").bind parseDouble |>.bind fun d => if d > 0 then some d else none
        ledgerEntropy := (env "WINNOW_E2E_LEDGER").map fun h =>
          (Wire.dataOfHex? h).filter fun e => 16 ≤ e.size && e.size ≤ 32 && e.size % 4 == 0
        liveGateways := env "WINNOW_E2E_LIVE_GATEWAYS" == some "1" }

namespace Mode

def safeRunID (m : Mode) : String :=
  String.ofList (m.runID.toList.map fun c => if c.isAlphanum || c == '.' || c == '-' then c else '_')

def storageDirectoryName (m : Mode) : String := s!"BTCSwiftE2E-{m.runID}"
def keychainService (m : Mode) : String := s!"{keychainServicePrefix}.{m.safeRunID}"

/-- The custom signet's parameters when a challenge was injected (`customSignet(challenge:defaultPort:)`). -/
def networkParams (m : Mode) : Option Net.NetworkParams :=
  m.challenge.bind fun c => Net.NetworkParams.customSignet c 38_401

/-- `Control`: what the runner writes to the control file while the app runs; read when needed. -/
structure Control where
  clipboard : Option String := none

def control (m : Mode) : IO (Option Control) := do
  let some path := m.controlFile | return none
  let text ← try IO.FS.readFile path catch _ => return none
  match Lean.Json.parse text with
  | .ok j => return some { clipboard := (j.getObjValAs? String "clipboard").toOption }
  | .error _ => return none

end Mode

/-! ## The journal -/

def forbiddenFieldNames : List String := ["entropy", "mnemonic", "privatekey", "secretnonce", "seedhex"]

/-- `Character.isWhitespace` of a cluster: its first scalar has Unicode White_Space. -/
def isWhitespaceCluster (c : String) : Bool :=
  match c.toList.head? with
  | some ch =>
    let n := ch.toNat
    (0x09 ≤ n && n ≤ 0x0D) || n == 0x20 || n == 0x85 || n == 0xA0 || n == 0x1680 || (0x2000 ≤ n && n ≤ 0x200A) ||
      n == 0x2028 || n == 0x2029 || n == 0x202F || n == 0x205F || n == 0x3000
  | none => false

/-- `looksSecret`: any window of 12–24 consecutive words that is a valid BIP39 mnemonic, or an extended
private key prefix anywhere. -/
def looksSecret (value : String) : Bool := Id.run do
  let mut words : Array String := #[]
  let mut cur := ""
  for c in Characters.characters value do
    if isWhitespaceCluster c then
      if !cur.isEmpty then words := words.push cur
      cur := ""
    else cur := cur ++ c
  if !cur.isEmpty then words := words.push cur
  if words.size ≤ 512 then
    for length in [24, 21, 18, 15, 12] do
      if words.size ≥ length then
        for start in [0:words.size - length + 1] do
          let candidate := " ".intercalate (words.extract start (start + length)).toList
          if (Keys.BIP39.validate candidate).isOk then return true
  let lower := value.toLower
  for p in ["xprv", "tprv", "yprv", "zprv", "vprv", "uprv"] do
    if (lower.splitOn p).length > 1 then return true
  return false

def Mode.carriesThisRunsSeed (m : Mode) (value : String) : Bool := Id.run do
  let some e := m.entropy | return false
  if e.isEmpty then return false
  let haystack := value.toLower
  if (haystack.splitOn (hex e)).length > 1 then return true
  match Keys.BIP39.mnemonic e with
  | .ok words => return (haystack.splitOn words.toLower).length > 1
  | .error _ => return false

/-- ISO 8601 (`JSONEncoder.dateEncodingStrategy = .iso8601`): `2026-10-27T05:31:00Z`. -/
def iso8601 (secondsSince1970 : Int) : String :=
  let days := secondsSince1970 / 86400
  let secs := secondsSince1970 % 86400
  -- civil-from-days (H. Hinnant)
  let z := days + 719468
  let era := (if z ≥ 0 then z else z - 146096) / 146097
  let doe := z - era * 146097
  let yoe := (doe - doe / 1460 + doe / 36524 - doe / 146096) / 365
  let doy := doe - (365 * yoe + yoe / 4 - yoe / 100)
  let mp := (5 * doy + 2) / 153
  let d := doy - (153 * mp + 2) / 5 + 1
  let mo := if mp < 10 then mp + 3 else mp - 9
  let y := yoe + era * 400 + (if mo ≤ 2 then 1 else 0)
  let pad (n : Int) (w : Nat) := let s := toString n.toNat; String.ofList (List.replicate (w - s.length) '0') ++ s
  s!"{pad y 4}-{pad mo 2}-{pad d 2}T{pad (secs / 3600) 2}:{pad (secs % 3600 / 60) 2}:{pad (secs % 60) 2}Z"

/-- The journal's field-name rule: a key whose letters, lowercased, contain a forbidden name. (Swift keeps
any `Character.isLetter`; the app's keys are ASCII literals.) -/
def refusesFieldName (key : String) : Bool :=
  let normalized := String.ofList (key.toLower.toList.filter Char.isAlpha)
  forbiddenFieldNames.any fun f => (normalized.splitOn f).length > 1

/-- `journal(_:fields:)`: one JSON line appended to `<support>/BTCSwiftE2E-<run>/story-events.jsonl`,
or nothing at all when a field name or value looks like a secret (fail closed). -/
def Mode.journal (m : Mode) (support : String) (name : String) (fields : List (String × String)) : IO Unit := do
  if fields.any (refusesFieldName ·.1) then return
  if fields.any (looksSecret ·.2) then return
  if fields.any (m.carriesThisRunsSeed ·.2) then return
  let dir := System.FilePath.mk support / m.storageDirectoryName
  try IO.FS.createDirAll dir catch _ => return
  let path := dir / "story-events.jsonl"
  let sorted := fields.toArray.qsort (fun a b => a.1 < b.1)
  let fieldsText := ",".intercalate (sorted.toList.map fun (k, v) => SwiftJSON.escape k ++ ":" ++ SwiftJSON.escape v)
  let line := "{\"version\":1,\"timestamp\":" ++ SwiftJSON.escape (iso8601 (← IO.wallSeconds)) ++
    ",\"name\":" ++ SwiftJSON.escape name ++ ",\"fields\":{" ++ fieldsText ++ "}}\n"
  try
    let h ← IO.FS.Handle.mk path .append
    h.putStr line
    h.flush
    IO.setAccessRights path { user := { read := true, write := true } }
  catch _ => pure ()

end WinnowApp.E2E
