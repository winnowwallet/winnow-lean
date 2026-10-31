import Winnow.Crypto
import Oracle.Base
import Winnow.Net

/-! Oracle ops for the Net area (Lean side of LeanOracle/Net). -/

namespace Oracle
open Lean Winnow Winnow.Net

def bytesArr (j : Json) (k : String) : Except String (Array ByteArray) := do
  let xs ← j.getObjValAs? (Array String) k
  xs.mapM fun s => match ofHex? s with
    | some b => pure b
    | none => throw s!"{k}: not hex"

def gcsReply (f : GCSFilter) (queries : Array ByteArray) : Json :=
  ok (Json.mkObj [("n", toJson f.n.toNat), ("encoded", hexJ f.encoded), ("serialized", hexJ f.serialized),
    ("contains", toJson (queries.map f.contains)), ("matchAny", toJson (f.matchAny queries))])

def gcsOps : List (String × Handler) := [
  ("gcs.build", fun j => do
    match GCSFilter.build (← bytesArr j "items") (← nat j "p").toUInt8 (← nat j "m").toUInt32 (← bytes j "key") with
    | .ok f => return gcsReply f (← bytesArr j "queries")
    | .error e => return err e.name),
  ("gcs.decode", fun j => do
    match GCSFilter.decode (← nat j "p").toUInt8 (← nat j "m").toUInt32 (← bytes j "key") (← nat j "n").toUInt32 (← bytes j "encoded") with
    | .ok f => return gcsReply f (← bytesArr j "queries")
    | .error e => return err e.name),
  ("gcs.filterHash", fun j => return ok (hexJ (GCSFilter.filterHash (← bytes j "data")))),
  ("gcs.filterHeader", fun j => return ok (hexJ (GCSFilter.filterHeader (← bytes j "data") (← bytes j "previous"))))
]

/-! ## Parameters, UInt256, headers, header chain -/

def optField (j : Json) (k : String) : Option Json :=
  match j.getObjVal? k with
  | .ok Json.null => none
  | .ok v => some v
  | .error _ => none

def u32n (j : Json) (k : String) : Except String UInt32 := return (← nat j k).toUInt32

def checkpointOf (j : Json) : Except String Checkpoint := do
  return { height := ← u32n j "height", header := ← bytes j "header", chainwork := ← bytes j "chainwork" }

def paramsOf (j : Json) : Except String NetworkParams := do
  if let some n := optField j "name" then
    match BitcoinNetwork.ofRaw? (← fromJson? n) with
    | some net => return NetworkParams.params net
    | none => throw "params: unknown network"
  if let some c := optField j "customSignet" then
    match NetworkParams.customSignet (← bytes c "challenge") (← nat c "port").toUInt16 with
    | some p => return p
    | none => throw "params: empty challenge"
  let c ← j.getObjVal? "custom"
  let some network := BitcoinNetwork.ofRaw? (← str c "network") | throw "params: network"
  let p : NetworkParams := {
    network, magic := ← bytes c "magic", defaultPort := (← nat c "defaultPort").toUInt16,
    genesisTime := ← u32n c "genesisTime", genesisBits := ← u32n c "genesisBits",
    genesisNonce := ← u32n c "genesisNonce", genesisMerkleRoot := ← bytes c "genesisMerkleRoot",
    genesisHash := ← bytes c "genesisHash", powLimit := ← bytes c "powLimit",
    dnsSeeds := ← c.getObjValAs? (Array String) "dnsSeeds",
    checkpoint := ← (optField c "checkpoint").mapM checkpointOf,
    powTargetTimespan := ← u32n c "powTargetTimespan", powTargetSpacing := ← u32n c "powTargetSpacing",
    noRetargeting := ← c.getObjValAs? Bool "noRetargeting" }
  if !p.valid then throw "params: violates NetworkParams preconditions"
  return p

def checkpointJ (c : Checkpoint) : Json :=
  Json.mkObj [("height", toJson c.height.toNat), ("header", hexJ c.header), ("chainwork", hexJ c.chainwork)]

def paramsJ (p : NetworkParams) : Json :=
  let g := HeaderChain.genesisHeader p
  Json.mkObj [("network", Json.str p.network.rawValue), ("magic", hexJ p.magic), ("defaultPort", toJson p.defaultPort.toNat),
    ("genesisTime", toJson p.genesisTime.toNat), ("genesisBits", toJson p.genesisBits.toNat),
    ("genesisNonce", toJson p.genesisNonce.toNat), ("genesisMerkleRoot", hexJ p.genesisMerkleRoot),
    ("genesisHash", hexJ p.genesisHash), ("genesisHashDisplay", Json.str (displayHex p.genesisHash)),
    ("powLimit", hexJ p.powLimit), ("powTargetTimespan", toJson p.powTargetTimespan.toNat),
    ("powTargetSpacing", toJson p.powTargetSpacing.toNat), ("interval", toJson p.difficultyAdjustmentInterval.toNat),
    ("noRetargeting", toJson p.noRetargeting), ("dnsSeeds", toJson p.dnsSeeds),
    ("checkpoint", match p.checkpoint with | some c => checkpointJ c | none => Json.null),
    ("isCustomSignet", toJson p.isCustomSignet), ("allowsPrivateSeedAddresses", toJson p.allowsPrivateSeedAddresses),
    ("genesisHeader", hexJ g.serialized), ("genesisHeaderHash", hexJ g.hash)]

def u256J (x : UInt256) : Json := hexJ x.bigEndianData
def u256Of (j : Json) (k : String) : Except String UInt256 := do
  let b ← bytes j k
  if b.size != 32 then throw s!"{k}: 32 bytes"
  return UInt256.ofBigEndian b

def headerJ (h : BlockHeader) : Json :=
  Json.mkObj [("version", toJson h.version.toInt), ("previousHash", hexJ h.previousHash), ("merkleRoot", hexJ h.merkleRoot),
    ("time", toJson h.time.toNat), ("bits", toJson h.bits.toNat), ("nonce", toJson h.nonce.toNat),
    ("hash", hexJ h.hash), ("serialized", hexJ h.serialized)]

def headerOf (j : Json) (k : String) : Except String BlockHeader := do
  match BlockHeader.decode (← bytes j k) with
  | .ok h => pure h
  | .error _ => throw s!"{k}: not an 80-byte header"

def hcErr (e : HeaderChainError) : Json :=
  let detail : Json := match e with
    | .invalidTarget h | .targetAbovePowLimit h | .insufficientProofOfWork h | .unexpectedDifficulty h
    | .timestampTooFarInFuture h => toJson h.toNat
    | .storageCorrupt s | .storageUnavailable s | .badPeerResponse s => Json.str s
    | .startMismatch a b => toJson [a.toNat, b.toNat]
    | _ => Json.null
  Json.mkObj [("error", Json.str e.name), ("detail", detail)]

def outcomeJ (o : ConnectOutcome) : Json :=
  Json.mkObj [("appended", toJson o.appended), ("forkHeight", match o.forkHeight with | some f => toJson f.toNat | none => Json.null),
    ("disconnectedHeaders", toJson o.disconnectedHeaders)]

def fileJ (f : Option ByteArray) : Json :=
  match f with
  | some b => Json.mkObj [("size", toJson b.size), ("sha256", hexJ (sha256 b))]
  | none => Json.null

def chainState (c : HeaderChain) (file : Option ByteArray) (queries : Array Nat) : Json :=
  Json.mkObj [("height", toJson c.height.toNat), ("tipHash", hexJ c.tipHash), ("tipWork", hexJ c.tipWork),
    ("startHeight", toJson c.startHeight.toNat), ("locator", toJson (c.blockLocator.map fun h => Json.str (hex h))),
    ("file", fileJ file),
    ("hashes", toJson (queries.map fun q => match c.blockHash? q.toUInt32 with | some h => hexJ h | none => Json.null))]

def headerOps : List (String × Handler) := [
  ("params.get", fun j => return ok (paramsJ (← paramsOf (← j.getObjVal? "params")))),
  ("params.signetMagic", fun j => return ok (hexJ (NetworkParams.signetMagic (← bytes j "challenge")))),
  ("u256.target", fun j => return ok (match UInt256.target (← u32n j "bits") with | some t => u256J t | none => Json.null)),
  ("u256.blockWork", fun j => return ok (match UInt256.blockWork (← u256Of j "value") with | some t => u256J t | none => Json.null)),
  ("u256.arith", fun j => do
    let a ← u256Of j "a"
    let b ← u256Of j "b"
    let bits ← nat j "bits"
    let factor ← u32n j "factor"
    let (q, r) := a.quotientAndRemainder b
    return ok (Json.mkObj [("add", u256J (a + b)), ("sub", u256J (a - b)), ("shl", u256J (a.shiftedLeft bits)),
      ("shr", u256J (a.shiftedRight bits)), ("mul", u256J (a.multiplied factor)),
      ("div", if b.isZero then Json.null else u256J q), ("rem", if b.isZero then Json.null else u256J r),
      ("lt", toJson (decide (a < b))), ("le", toJson (decide (a ≤ b))), ("bitWidth", toJson a.bitWidth),
      ("compact", toJson a.compact.toNat), ("ofLE", u256J (UInt256.ofLittleEndian a.bigEndianData))])),
  ("header.decode", fun j => do
    match BlockHeader.decode (← bytes j "data") with
    | .ok h => return ok (headerJ h)
    | .error e => return err e.name),
  ("chain.expectedBits", fun j => do
    let p ← paramsOf (← j.getObjVal? "params")
    let first ← (optField j "first").mapM fun _ => headerOf j "first"
    match HeaderChain.expectedBits (← u32n j "height") (← headerOf j "previous") first p with
    | .ok (some b) => return ok (toJson b.toNat)
    | .ok none => return ok Json.null
    | .error e => return hcErr e),
  ("chain.boundedAdjustment", fun j => do
    let p ← paramsOf (← j.getObjVal? "params")
    match HeaderChain.requireBoundedAdjustment (← headerOf j "header") (← headerOf j "previous") p (← u32n j "height") with
    | .ok () => return ok Json.null
    | .error e => return hcErr e),
  ("chain.checkedWork", fun j => do
    let p ← paramsOf (← j.getObjVal? "params")
    match HeaderChain.checkedWork (← headerOf j "header") p (← u32n j "height") with
    | .ok w => return ok (u256J w)
    | .error e => return hcErr e),
  ("chain.forWallet", fun j => do
    let birthday := (optField j "birthday").bind fun v => (fromJson? v : Except String Nat).toOption |>.map (·.toUInt32)
    let checkpoint ← (optField j "checkpoint").mapM checkpointOf
    let s := ChainStart.forWallet birthday checkpoint (← j.getObjValAs? Bool "verifyFromGenesis")
    return ok (Json.str (if s == .genesis then "genesis" else "checkpoint"))),
  ("chain.run", fun j => do
    let p ← paramsOf (← j.getObjVal? "params")
    let start := if (← str j "start") == "checkpoint" then ChainStart.checkpoint else .genesis
    let now := (← u64 j "now").toUInt32
    let storage ← j.getObjValAs? Bool "storage"
    let stored ← if storage then (optField j "file").mapM fun _ => bytes j "file" else pure none
    let batches ← j.getObjValAs? (Array (Array String)) "batches"
    let queries ← j.getObjValAs? (Array Nat) "queries"
    match HeaderChain.create p stored start storage with
    | .error e => return hcErr e
    | .ok c0 =>
      let mut c := c0
      let mut file := stored
      let mut outs : Array Json := #[]
      for batch in batches do
        let hs ← batch.mapM fun s => match ofHex? s >>= fun b => (BlockHeader.decode b).toOption with
          | some h => pure h
          | none => throw "batches: not an 80-byte header"
        match c.connect hs now with
        | .ok (c', o, writes) =>
          c := c'
          for w in writes do file := some (w.apply file)
          outs := outs.push (ok (outcomeJ o))
        | .error e => outs := outs.push (hcErr e)
      return ok (Json.mkObj [("outcomes", Json.arr outs), ("state", chainState c file queries)]))
]

/-! ## Protocol: addresses, inventory, framing, messages, blocks -/

def addrJ (a : PeerAddress) (includeTime : Bool) : Json :=
  Json.mkObj [("time", match a.time with | some t => toJson t.toNat | none => Json.null),
    ("services", Json.str (toString a.services.toNat)), ("ip", hexJ a.ip), ("port", toJson a.port.toNat),
    ("host", Json.str a.host), ("endpoint", Json.str a.endpointDescription),
    ("serialized", hexJ (a.serialized includeTime))]

def blockJ (b : Block) : Json :=
  Json.mkObj [("hash", hexJ b.hash), ("txids", toJson (b.transactions.map fun t => hex t.txid)),
    ("merkleRoot", match b.computedMerkleRoot with | some r => hexJ r | none => Json.null),
    ("hasValidMerkleRoot", toJson b.hasValidMerkleRoot), ("serialized", hexJ b.serialized)]

def messageExtra : PeerMessage → Json
  | .version m => Json.mkObj [("userAgent", Json.str m.userAgent), ("relay", toJson m.relay)]
  | .cfilter m => match m.parsedFilter with
    | .ok (n, enc) => Json.mkObj [("n", toJson n.toNat), ("encoded", hexJ enc)]
    | .error e => Json.mkObj [("error", Json.str e.name)]
  | .block b => blockJ b
  | .tx t => Json.mkObj [("txid", hexJ t.txid), ("wtxid", hexJ t.wtxid)]
  | .headers hs => toJson (hs.map fun h => hex h.hash)
  | .addr xs => toJson (xs.map fun a => a.endpointDescription)
  | _ => Json.null

def protocolOps : List (String × Handler) := [
  ("addr.decode", fun j => do
    let includeTime ← j.getObjValAs? Bool "includeTime"
    match Wire.run (PeerAddress.read includeTime) (← bytes j "data") with
    | .ok (a, off) => return ok (Json.mkObj [("address", addrJ a includeTime), ("consumed", toJson off)])
    | .error e => return err e.name),
  ("addr.host", fun j => do
    let ip ← bytes j "ip"
    if ip.size != 16 then throw "ip: 16 bytes"
    let a : PeerAddress := { services := 0, ip, port := (← nat j "port").toUInt16 }
    return ok (Json.mkObj [("host", Json.str a.host), ("endpoint", Json.str a.endpointDescription)])),
  ("inv.decode", fun j => do
    match InventoryPayload.decode (← bytes j "data") with
    | .ok p => return ok (Json.mkObj [("vectors", toJson (p.vectors.map fun v => Json.mkObj [
        ("type", toJson v.type.rawValue.toNat), ("hash", hexJ v.hash), ("baseType", toJson v.type.baseType.rawValue.toNat),
        ("isWitness", toJson v.type.isWitness)])), ("serialized", hexJ p.serialized)])
    | .error e => return err e.name),
  ("framer.feed", fun j => do
    let magic ← bytes j "magic"
    let chunks ← bytesArr j "chunks"
    let mut f : MessageFramer := { magic }
    let mut events : Array Json := #[]
    let mut failed := false
    for c in chunks do
      if failed then break
      f := f.append c
      let mut more := true
      while more do
        match f.nextMessage with
        | .ok (some (cmd, payload), f') =>
          f := f'
          events := events.push (Json.mkObj [("command", Json.str cmd), ("payload", hexJ payload)])
        | .ok (none, _) => more := false
        | .error e => events := events.push (err e.name); more := false; failed := true
    return ok (Json.mkObj [("events", Json.arr events), ("buffered", toJson f.bufferedCount)])),
  ("framer.frame", fun j => return ok (hexJ (MessageFramer.frame (← str j "command") (← bytes j "payload") (← bytes j "magic")))),
  ("msg.decode", fun j => do
    match PeerMessage.decode (← str j "command") (← bytes j "payload") with
    | .ok m => return ok (Json.mkObj [("command", Json.str m.command), ("payload", hexJ m.payload), ("extra", messageExtra m)])
    | .error e => return err e.name),
  ("block.decode", fun j => do
    match Block.decode (← bytes j "data") with
    | .ok b => return ok (blockJ b)
    | .error e => return err e.name)
]

/-! ## Filter sync and the mempool window (their pure parts) -/

def headersOf (j : Json) : Except String (Std.HashMap String String) := do
  let .obj kvs := j | throw "headers: object"
  kvs.toArray.foldlM (fun m (k, v) => do return m.insert k (← fromJson? v)) {}

def headersJ (h : Std.HashMap String String) : Json :=
  Json.mkObj ((h.toArray.qsort (fun a b => a.1 < b.1)).toList.map fun (k, v) => (k, Json.str v))

def progressJ (p : Progress) (queries : Array Nat) : Json :=
  Json.mkObj [("next", toJson p.nextScanHeight.toNat),
    ("last", match FilterSync.lastScannedHeight p with | some h => toJson h.toNat | none => Json.null),
    ("headers", headersJ p.filterHeaders),
    ("queries", toJson (queries.map fun q => match FilterSync.filterHeader? p.filterHeaders q.toUInt32 with
      | some b => hexJ b | none => Json.null))]

def fsErr (e : FilterSyncStorageError) : Json := err e.name

def filterOps : List (String × Handler) := [
  ("fs.scanCeiling", fun j => do
    let maxBlocks := (optField j "maxBlocks").bind fun v => (fromJson? v : Except String Nat).toOption |>.map (·.toUInt32)
    return ok (match FilterSync.scanCeiling (← u32n j "frontier") maxBlocks (← u32n j "tip") with
      | some c => toJson c.toNat | none => Json.null)),
  ("fs.pruned", fun j => return ok (headersJ (FilterSync.prunedFilterHeaders (← headersOf (← j.getObjVal? "headers")) (← u32n j "frontier")))),
  ("fs.crossSourceSet", fun j => do
    let peers ← (← j.getObjValAs? (Array Json) "peers").mapM fun p => do
      let id ← nat p "id"
      let src ← match optField p "source" with
        | some (.str s) => match PeerSource.ofRaw? s with
          | some x => pure (some x)
          | none => throw "source"
        | _ => pure none
      return (id, src)
    return ok (toJson (FilterSync.crossSourceSet peers (← nat j "limit")))),
  ("fs.progress", fun j => do
    let startHeight ← u32n j "startHeight"
    let storage ← j.getObjValAs? Bool "storage"
    let mut file ← (optField j "file").mapM fun v => (fromJson? v : Except String String)
    let queries ← j.getObjValAs? (Array Nat) "queries"
    let chunk := FilterSync.clampFiltersPerChunk (← u32n j "filtersPerChunk")
    match FilterSync.initialProgress storage file startHeight with
    | .error e => return fsErr e
    | .ok (state, p0) =>
      let mut p := p0
      let mut steps : Array Json := #[]
      for op in ← j.getObjValAs? (Array Json) "ops" do
        if let some h := optField op "rollBack" then
          let h ← (fromJson? h : Except String Nat)
          if let some p' := FilterSync.rollBack p h.toUInt32 then
            p := p'
            if storage then file := some p.toJson.compress
        else
          let r ← op.getObjVal? "record"
          p := { nextScanHeight := ← u32n r "next", filterHeaders := ← headersOf (← r.getObjVal? "headers") }
          if storage then file := some p.toJson.compress
        steps := steps.push (progressJ p queries)
      let reload := if !storage then Json.null else match FilterSync.load file startHeight with
        | .ok (st, q) => Json.mkObj [("state", Json.str st.name), ("progress", progressJ q queries)]
        | .error e => fsErr e
      return ok (Json.mkObj [("state", Json.str state.name), ("filtersPerChunk", toJson chunk.toNat),
        ("initial", progressJ p0 queries), ("steps", Json.arr steps), ("reload", reload)])),
  ("mempool.lifecycle", fun j => do
    let mut w : MempoolWindow := { watchScripts := {} }
    let mut out : Array Json := #[]
    for op in ← j.getObjValAs? (Array String) "ops" do
      match op.splitOn ":" with
      | ["start", n] => w := (w.start n.toNat!).1
      | ["extend", n] => w := (w.extend n.toNat!).1
      | ["stop"] => w := w.stop.1
      | ["watchEcho", h] => w := w.watchEcho (ofHex! h)
      | ["unwatchEcho", h] => w := w.unwatchEcho (ofHex! h)
      | _ => throw s!"op {op}"
      out := out.push (toJson w.running)
    return ok (Json.arr out))
]

def netOps : List (String × Handler) := gcsOps ++ headerOps ++ protocolOps ++ filterOps

end Oracle
