import Winnow.Net.PeerAddress
import Winnow.Net.Inventory
import Winnow.Net.Block

/-! # P2P messages (`Network/Protocol/Messages.swift`): payload types and `PeerMessage` encode/decode -/

namespace Winnow.Net

def zeroHash : ByteArray := ByteArray.mk (Array.replicate 32 0)

/-- `version` payload (protocol 70016). -/
structure VersionMessage where
  version : Int32
  services : UInt64
  timestamp : Int64
  receiver : PeerAddress
  sender : PeerAddress
  nonce : UInt64
  userAgent : String
  startHeight : Int32
  /-- BIP37 relay flag. -/
  relay : Bool
  deriving Inhabited

namespace VersionMessage
def serialized (m : VersionMessage) : ByteArray :=
  i32LE m.version ++ u64LE m.services ++ i64LE m.timestamp ++ m.receiver.serialized false ++
    m.sender.serialized false ++ u64LE m.nonce ++ varString m.userAgent ++ i32LE m.startHeight ++
    ByteArray.mk #[if m.relay then 1 else 0]

/-- Trailing bytes after the relay flag are ignored; a missing flag (protocol < 70001) reads as true. -/
def decode (payload : ByteArray) : Except WireError VersionMessage := Wire.eval (do
  let version ← Wire.i32
  let services ← Wire.u64
  let timestamp ← Wire.i64
  let receiver ← PeerAddress.read false
  let sender ← PeerAddress.read false
  let nonce ← Wire.u64
  let userAgent ← Wire.varString 256
  let startHeight ← Wire.i32
  let relay ← if (← Wire.remaining) > 0 then (· != 0) <$> Wire.u8 else pure true
  return { version, services, timestamp, receiver, sender, nonce, userAgent, startHeight, relay }) payload
end VersionMessage

/-- `getheaders`: version, locator, stop hash (zero = as many as possible). -/
structure GetHeadersMessage where
  version : Int32
  locatorHashes : Array ByteArray
  stopHash : ByteArray := zeroHash
  deriving Inhabited

namespace GetHeadersMessage
def serialized (m : GetHeadersMessage) : ByteArray :=
  m.locatorHashes.foldl (· ++ ·) (i32LE m.version ++ compactSize m.locatorHashes.size.toUInt64) ++ m.stopHash

def decode (payload : ByteArray) : Except WireError GetHeadersMessage := Wire.eval (do
  let version ← Wire.i32
  let count ← Wire.varInt
  if count > 101 then throw (.malformed s!"locator count {count}")
  let mut hashes : Array ByteArray := #[]
  for _ in [0:count.toNat] do hashes := hashes.push (← Wire.bytes 32)
  let stopHash ← Wire.bytes 32
  Wire.requireEnd
  return { version, locatorHashes := hashes, stopHash }) payload
end GetHeadersMessage

/-- `getcfilters` / `getcfheaders` (BIP157, same layout). -/
structure GetCFiltersRequest where
  filterType : UInt8 := 0
  startHeight : UInt32
  stopHash : ByteArray
  deriving Inhabited

namespace GetCFiltersRequest
def serialized (m : GetCFiltersRequest) : ByteArray := ByteArray.mk #[m.filterType] ++ u32LE m.startHeight ++ m.stopHash
def decode (payload : ByteArray) : Except WireError GetCFiltersRequest := Wire.eval (do
  let filterType ← Wire.u8
  let startHeight ← Wire.u32
  let stopHash ← Wire.bytes 32
  Wire.requireEnd
  return { filterType, startHeight, stopHash }) payload
end GetCFiltersRequest

/-- `cfilter`: the filter is BIP158 NBytes, compactSize(N) ‖ bitstream. -/
structure CFilterMessage where
  filterType : UInt8 := 0
  blockHash : ByteArray
  filter : ByteArray
  deriving Inhabited

namespace CFilterMessage
def serialized (m : CFilterMessage) : ByteArray := ByteArray.mk #[m.filterType] ++ m.blockHash ++ varBytes m.filter
def decode (payload : ByteArray) : Except WireError CFilterMessage := Wire.eval (do
  let filterType ← Wire.u8
  let blockHash ← Wire.bytes 32
  let filter ← Wire.varData
  Wire.requireEnd
  return { filterType, blockHash, filter }) payload

/-- Splits the NBytes into (item count, bitstream) for `GCSFilter.decode`. -/
def parsedFilter (m : CFilterMessage) : Except WireError (UInt32 × ByteArray) := do
  let (n, off) ← Wire.run Wire.varInt m.filter
  if n > 0xFFFFFFFF then throw (.malformed s!"filter element count {n}")
  return (n.toUInt32, m.filter.extract off m.filter.size)
end CFilterMessage

/-- `cfheaders`: previous filter header plus one filter hash per block. -/
structure CFHeadersMessage where
  filterType : UInt8 := 0
  stopHash : ByteArray
  previousFilterHeader : ByteArray
  filterHashes : Array ByteArray
  deriving Inhabited

namespace CFHeadersMessage
def serialized (m : CFHeadersMessage) : ByteArray :=
  m.filterHashes.foldl (· ++ ·) (ByteArray.mk #[m.filterType] ++ m.stopHash ++ m.previousFilterHeader ++
    compactSize m.filterHashes.size.toUInt64)
def decode (payload : ByteArray) : Except WireError CFHeadersMessage := Wire.eval (do
  let filterType ← Wire.u8
  let stopHash ← Wire.bytes 32
  let previousFilterHeader ← Wire.bytes 32
  let count ← Wire.varInt
  if count > 2_000 then throw (.malformed s!"cfheaders count {count}")
  let mut hashes : Array ByteArray := #[]
  for _ in [0:count.toNat] do hashes := hashes.push (← Wire.bytes 32)
  Wire.requireEnd
  return { filterType, stopHash, previousFilterHeader, filterHashes := hashes }) payload
end CFHeadersMessage

/-- `getcfcheckpt`. -/
structure GetCFCheckptRequest where
  filterType : UInt8 := 0
  stopHash : ByteArray
  deriving Inhabited

namespace GetCFCheckptRequest
def serialized (m : GetCFCheckptRequest) : ByteArray := ByteArray.mk #[m.filterType] ++ m.stopHash
def decode (payload : ByteArray) : Except WireError GetCFCheckptRequest := Wire.eval (do
  let filterType ← Wire.u8
  let stopHash ← Wire.bytes 32
  Wire.requireEnd
  return { filterType, stopHash }) payload
end GetCFCheckptRequest

/-- `cfcheckpt`: filter headers at heights 1000, 2000, … up to the stop block. -/
structure CFCheckptMessage where
  filterType : UInt8 := 0
  stopHash : ByteArray
  filterHeaders : Array ByteArray
  deriving Inhabited

instance : BEq CFCheckptMessage := ⟨fun a b => a.filterType == b.filterType && a.stopHash == b.stopHash &&
  a.filterHeaders == b.filterHeaders⟩
instance : BEq CFHeadersMessage := ⟨fun a b => a.filterType == b.filterType && a.stopHash == b.stopHash &&
  a.previousFilterHeader == b.previousFilterHeader && a.filterHashes == b.filterHashes⟩

namespace CFCheckptMessage
def serialized (m : CFCheckptMessage) : ByteArray :=
  m.filterHeaders.foldl (· ++ ·) (ByteArray.mk #[m.filterType] ++ m.stopHash ++ compactSize m.filterHeaders.size.toUInt64)
def decode (payload : ByteArray) : Except WireError CFCheckptMessage := Wire.eval (do
  let filterType ← Wire.u8
  let stopHash ← Wire.bytes 32
  let count ← Wire.varInt
  if count > 100_000 then throw (.malformed s!"cfcheckpt count {count}")
  let mut hs : Array ByteArray := #[]
  for _ in [0:count.toNat] do hs := hs.push (← Wire.bytes 32)
  Wire.requireEnd
  return { filterType, stopHash, filterHeaders := hs }) payload
end CFCheckptMessage

/-- A decoded P2P message; unknown commands keep their raw payload. -/
inductive PeerMessage where
  | version (m : VersionMessage)
  | verack
  | ping (nonce : UInt64)
  | pong (nonce : UInt64)
  | sendheaders
  | getaddr
  | addr (addresses : Array PeerAddress)
  | feefilter (feeRate : Int64)
  | inv (p : InventoryPayload)
  | getdata (p : InventoryPayload)
  | notfound (p : InventoryPayload)
  | tx (t : Transaction)
  | block (b : Block)
  | getheaders (m : GetHeadersMessage)
  | headers (hs : Array BlockHeader)
  | getcfilters (r : GetCFiltersRequest)
  | cfilter (m : CFilterMessage)
  | getcfheaders (r : GetCFiltersRequest)
  | cfheaders (m : CFHeadersMessage)
  | getcfcheckpt (r : GetCFCheckptRequest)
  | cfcheckpt (m : CFCheckptMessage)
  | unknown (command : String) (payload : ByteArray)
  deriving Inhabited

namespace PeerMessage

def command : PeerMessage → String
  | .version _ => "version" | .verack => "verack" | .ping _ => "ping" | .pong _ => "pong"
  | .sendheaders => "sendheaders" | .getaddr => "getaddr" | .addr _ => "addr" | .feefilter _ => "feefilter"
  | .inv _ => "inv" | .getdata _ => "getdata" | .notfound _ => "notfound" | .tx _ => "tx" | .block _ => "block"
  | .getheaders _ => "getheaders" | .headers _ => "headers" | .getcfilters _ => "getcfilters"
  | .cfilter _ => "cfilter" | .getcfheaders _ => "getcfheaders" | .cfheaders _ => "cfheaders"
  | .getcfcheckpt _ => "getcfcheckpt" | .cfcheckpt _ => "cfcheckpt" | .unknown c _ => c

def payload : PeerMessage → ByteArray
  | .version m => m.serialized
  | .verack | .sendheaders | .getaddr => .empty
  | .addr xs => xs.foldl (fun d a => d ++ a.serialized true) (compactSize xs.size.toUInt64)
  | .ping n | .pong n => u64LE n
  | .feefilter r => i64LE r
  | .inv p | .getdata p | .notfound p => p.serialized
  | .tx t => t.serialized true
  | .block b => b.serialized
  | .getheaders m => m.serialized
  | .headers hs => hs.foldl (fun d h => d ++ h.serialized ++ compactSize 0) (compactSize hs.size.toUInt64)
  | .getcfilters r | .getcfheaders r => r.serialized
  | .cfilter m => m.serialized
  | .cfheaders m => m.serialized
  | .getcfcheckpt r => r.serialized
  | .cfcheckpt m => m.serialized
  | .unknown _ p => p

private def empty (payload : ByteArray) (m : PeerMessage) : Except WireError PeerMessage :=
  if payload.size != 0 then .error (.trailingBytes payload.size) else .ok m

private def nonce (payload : ByteArray) : Except WireError UInt64 :=
  Wire.eval (do let n ← Wire.u64; Wire.requireEnd; return n) payload

def decode (command : String) (payload : ByteArray) : Except WireError PeerMessage :=
  match command with
  | "version" => .version <$> VersionMessage.decode payload
  | "verack" => empty payload .verack
  | "ping" => .ping <$> nonce payload
  | "pong" => .pong <$> nonce payload
  | "sendheaders" => empty payload .sendheaders
  | "getaddr" => empty payload .getaddr
  | "addr" => Wire.eval (do
      let count ← Wire.varInt
      if count > 1_000 then throw (.malformed s!"addr count {count}")
      let mut xs : Array PeerAddress := #[]
      for _ in [0:count.toNat] do xs := xs.push (← PeerAddress.read true)
      Wire.requireEnd
      return PeerMessage.addr xs) payload
  | "feefilter" => Wire.eval (do let r ← Wire.i64; Wire.requireEnd; return PeerMessage.feefilter r) payload
  | "inv" => .inv <$> InventoryPayload.decode payload
  | "getdata" => .getdata <$> InventoryPayload.decode payload
  | "notfound" => .notfound <$> InventoryPayload.decode payload
  | "tx" => .tx <$> Transaction.decode payload
  | "block" => .block <$> Block.decode payload
  | "getheaders" => .getheaders <$> GetHeadersMessage.decode payload
  | "headers" => Wire.eval (do
      let count ← Wire.varInt
      if count > 2_000 then throw (.malformed s!"headers count {count}")
      let mut hs : Array BlockHeader := #[]
      for _ in [0:count.toNat] do
        hs := hs.push (← BlockHeader.read)
        let txCount ← Wire.varInt
        if txCount != 0 then throw (.malformed s!"headers txn_count {txCount}")
      Wire.requireEnd
      return PeerMessage.headers hs) payload
  | "getcfilters" => .getcfilters <$> GetCFiltersRequest.decode payload
  | "cfilter" => .cfilter <$> CFilterMessage.decode payload
  | "getcfheaders" => .getcfheaders <$> GetCFiltersRequest.decode payload
  | "cfheaders" => .cfheaders <$> CFHeadersMessage.decode payload
  | "getcfcheckpt" => .getcfcheckpt <$> GetCFCheckptRequest.decode payload
  | "cfcheckpt" => .cfcheckpt <$> CFCheckptMessage.decode payload
  | c => .ok (.unknown c payload)

end PeerMessage
end Winnow.Net
