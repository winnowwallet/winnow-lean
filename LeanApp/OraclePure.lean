import Lean.Data.Json
import WinnowApp.Pure
import WinnowApp.Real.Wallet

/-! `oracle-pure`: the Lean side of `LeanOracle/Pure/main.swift` (lockstep generator
`LeanOracle/gen/f_pure.py`): the app's pure helpers (`WinnowApp/Pure.lean`). One JSON request per
line on stdin, one reply per line.

Ops: `sync`, `history.order`, `history.row` (the entry decoded through `Real.historyItem`, the records
built the way `Real.summaryOf` builds them), `explorer`, `url.host`, `loopback`, `settings.shows`,
`peer.parse`, `label.normalize`, `fee.proportion`, `rate.parse`, `rate.suggest` (from the unrounded pending
rate, as `Real.pendingFeeRate` computes it). The vault, savings, approval and MuSig2 ops (`threshold`,
`vault.rule`, `names.join`, `maturity`, `pay.title`, `approval`, `musig.labels`) went with vaults. -/

open Lean Winnow WinnowApp

def str (j : Json) (k : String) : Except String String := j.getObjValAs? String k
def optS (j : Json) (k : String) : Option String := (j.getObjValAs? String k).toOption
def jstr (s : String) : Json := .str s
def jopt {α} (f : α → Json) : Option α → Json | some a => f a | none => .null
def jnat (n : Nat) : Json := (n : Json)
def ok (v : Json) : Json := Json.mkObj [("ok", v)]
def errJ (name : String) : Json := Json.mkObj [("error", .str name)]
def arr (xs : List Json) : Json := .arr xs.toArray

def bad {α} (what : String) : IO α := throw (IO.userError s!"bad-request: {what}")
def need {α} (r : Except String α) : IO α := match r with | .ok a => pure a | .error e => bad e
def natJ (j : Json) (k : String) : IO Nat := need (j.getObjValAs? Nat k)
def boolJ (j : Json) (k : String) : Bool := (j.getObjValAs? Bool k).toOption.getD false
def intS (j : Json) (k : String) : IO Int := do
  match (← need (str j k)).toInt? with
  | some n => pure n
  | none => bad k

def netJ (j : Json) : IO WinnowApp.Network := do
  match ← need (str j "network") with
  | "mainnet" => pure .mainnet | "signet" => pure .signet | "regtest" => pure .regtest
  | _ => bad "network"

def pairsJ (j : Json) (k : String) : List (String × String) :=
  ((j.getObjValAs? (Array (Array String)) k).toOption.getD #[]).toList.filterMap fun p =>
    if p.size == 2 then some (p[0]!, p[1]!) else none

def stringsJ (j : Json) (k : String) : List String := ((j.getObjValAs? (Array String) k).toOption.getD #[]).toList

/-! ## Sync -/

def phaseJ (j : Json) : IO SyncPhase := do
  let p ← need (j.getObjVal? "phase")
  let a := (p.getObjValAs? Nat "a").toOption.getD 0
  let b := (p.getObjValAs? Nat "b").toOption.getD 0
  match ← need (str p "k") with
  | "idle" => pure .idle | "connecting" => pure (.connecting a b) | "headers" => pure (.headers a b)
  | "filters" => pure (.filters a b) | "synced" => pure .synced | "peerDiscoveryFailed" => pure .peerDiscoveryFailed
  | _ => bad "phase"

def syncOp (j : Json) : IO Json := do
  let p ← phaseJ j
  let summary := match p.summary (boolJ j "syncing") with
    | .syncing => "syncing" | .synced => "synced" | .peersUnavailable => "peersUnavailable"
  return ok (Json.mkObj [("status", jopt jstr (syncStatusText p)),
    ("scan", jopt jstr (filterScanText p (← natJ j "fallbackScanned") (← natJ j "fallbackTip"))),
    ("summary", jstr summary), ("lags", .bool p.headerTipMayLagNetwork)])

/-! ## History -/

def historyOrder (j : Json) : IO Json := do
  let entries ← need (j.getObjValAs? (Array Json) "entries")
  -- each entry's position travels as its fee, so the order can be read back
  let items : List HistoryItem := entries.toList.zipIdx.map fun (e, i) =>
    { txid := (optS e "txid").getD "", height := (e.getObjValAs? Nat "height").toOption.getD 0,
      received := 0, spent := 0, fee := some i, replacedBy := optS e "replacedBy" }
  return ok (arr ((historyForDisplay items).map fun h => jnat (h.fee.getD 0).toNat))

def scriptSet (xs : List String) : Std.HashSet ByteArray := xs.foldl (fun s h => match ofHex? h with
  | some b => s.insert b | none => s) {}

def historyRow (j : Json) : IO Json := do
  let network ← netJ j
  let txNet := Real.Network.tx network
  let some txid := ofHex? (← need (str j "txid")) | bad "txid"
  let height ← natJ j "height"
  let received ← intS j "received"
  let spent ← intS j "spent"
  let entry : HistoryEntry :=
    { txid := ByteArray.reverse txid, height := height.toUInt32,
      received := Int64.ofInt received, spent := Int64.ofInt spent,
      rawTransaction := (optS j "raw").bind ofHex?,
      fundingScripts := ((stringsJ j "fundingScripts").filterMap ofHex?).toArray }
  let h := Real.historyItem entry (scriptSet (stringsJ j "owned")) txNet
  let people : List Person := (pairsJ j "people").map fun (id, name) => { id, name }
  -- `Real.summaryOf`: labels keyed by the address their script renders as
  let labels := (pairsJ j "labels").filterMap fun (s, note) =>
    (ofHex? s).bind fun sc => (AddressDecoder.address sc txNet).map (·, note)
  let records : Records :=
    { people, senderByTxid := pairsJ j "senderByTxid", recipientByScript := pairsJ j "recipientByScript",
      receiveLabels := labels }
  return ok (Json.mkObj [
    ("sender", jopt (jstr ·.id) (receivedSender records h)),
    ("recipients", arr ((paymentRecipients records h).map fun r =>
      arr [jnat r.id, jstr r.address, jstr (toString r.amount), jopt (jstr ·.id) r.person])),
    ("labeled", arr ((labeledReceiveOutputs records h).map fun o =>
      arr [jnat o.id, jstr o.address, jstr o.label, jstr (toString o.amount)])),
    ("title", jstr (historyTitle records h)), ("labels", jstr (historyLabels records h)),
    ("amount", jstr (signedSatsText h.net))])

/-! ## Explorer -/

def providerJ (j : Json) : IO Explorer := do
  match ← need (str j "provider") with
  | "blockstream" => pure .blockstream | "mempool" => pure .mempool | "custom" => pure .custom
  | _ => bad "provider"

def settingsWith (network : WinnowApp.Network) (f : NetworkSettings → NetworkSettings) : Settings :=
  ({ network } : Settings).withScoped f

def explorerOp (j : Json) : IO Json := do
  let provider ← providerJ j
  let custom ← need (str j "custom")
  let s := settingsWith (← netJ j) fun n => { n with explorer := provider, esploraURL := custom }
  let base := s.esploraBaseURL
  return ok (Json.mkObj [("base", jstr base), ("host", jopt jstr (urlHost base)),
    ("tx", jstr (s.transactionURL (← need (str j "txid")))), ("address", jstr (s.addressURL (← need (str j "address")))),
    ("explorerHost", jstr s.explorerHost)])

def urlHostOp (j : Json) : IO Json := do return ok (jopt jstr (urlHost (← need (str j "url"))))
def loopbackOp (j : Json) : IO Json := do return ok (.bool (isLoopback (← need (str j "host"))))

/-! ## Settings, labels -/

def settingsShows (j : Json) : IO Json := do
  let s := { settingsWith (← netJ j) fun n => { n with manualPeers := stringsJ j "manualPeers", esploraURL := (optS j "esploraURL").getD "" }
             with advancedMode := boolJ j "advancedMode", verifyFromGenesis := boolJ j "verifyFromGenesis" }
  return ok (arr [.bool s.showsNetworkPicker, .bool s.showsManualPeers, .bool s.showsChainVerification,
                  .bool s.showsExplorerSettings])

def peerParse (j : Json) : IO Json := do
  match parsePeer (← need (str j "text")) with
  | .ok p => return ok (jstr p)
  | .error m => return Json.mkObj [("error", jstr "invalidPeer"), ("message", jstr m)]

def labelNormalize (j : Json) : IO Json := do
  match normalizedLabel (← need (str j "text")) with
  | .ok l => return ok (jstr l)
  | .error m => return Json.mkObj [("error", jstr "invalidLabel"), ("message", jstr m)]

/-! ## Fees -/

def feeProportion (j : Json) : IO Json := do
  let amount ← intS j "amount"
  let fee ← intS j "fee"
  return ok (jopt jstr (feeProportionWarning amount.toNat fee.toNat))

def rateParse (j : Json) : IO Json := do
  -- the bump sheet trims newlines too (HomeView.swift:12), the send override does not (SendView.swift:150)
  let bump := (← need (str j "site")) == "bump"
  return ok (jopt (jstr ∘ toString) (parseRateMilli (← need (str j "text")) (trimNewlines := bump)))

def rateSuggest (j : Json) : IO Json := do
  let fee ← intS j "fee"
  let vsize ← natJ j "vsize"
  -- `Real.pendingFeeRate`: from the wallet's `Double(fee) / Double(vsize)`, before rounding to thousandths
  return ok (jstr (suggestedBumpText (Float.ofInt fee / vsize.toFloat)))

def ops : Std.HashMap String (Json → IO Json) := Std.HashMap.ofList [
  ("sync", syncOp), ("history.order", historyOrder), ("history.row", historyRow), ("explorer", explorerOp),
  ("url.host", urlHostOp), ("loopback", loopbackOp), ("settings.shows", settingsShows), ("peer.parse", peerParse),
  ("label.normalize", labelNormalize), ("fee.proportion", feeProportion), ("rate.parse", rateParse),
  ("rate.suggest", rateSuggest)]

def answer (line : String) : IO Json := do
  match Json.parse line with
  | .error e => return errJ s!"bad-json: {e}"
  | .ok j =>
    match j.getObjValAs? String "op" with
    | .error _ => return errJ "bad-json: op"
    | .ok op =>
      match ops[op]? with
      | none => return errJ "unsupported"
      | some h =>
        try h j catch e =>
          let m := toString e
          return errJ (if m.startsWith "bad-request" then m else s!"bad-request: {m}")

partial def loop (stdin stdout : IO.FS.Stream) : IO Unit := do
  let line ← stdin.getLine
  if line.isEmpty then return
  stdout.putStrLn (← answer line.trimAscii.copy).compress
  stdout.flush
  loop stdin stdout

def main : IO Unit := do loop (← IO.getStdin) (← IO.getStdout)
