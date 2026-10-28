import Lean.Data.Json
import WinnowApp.Real.Records

/-! `oracle-records`: the Lean side of `LeanOracle/Records/main.swift` (lockstep generator
`LeanOracle/gen/f_records.py`). One JSON request per line on stdin, one reply per line.

Ops: `seal.seal` / `seal.open` (the sealed file format), `store.open` (configure a people store over a
given file: result, records, the file afterwards), `people.script` (a sequence of people-store mutations,
person ids renamed by creation order), `records.derive` (AppModel's derived data over a given people
file), `own.key` (`ownKeyExpression` and the own card), `paste` (the Add-person preview), `labels.run` (the
receive-label store over a given file), `lookup.parse` (an explorer answer). The vault store, the
shared-savings reading and signer fingerprints went with vaults (upstream 1cf93fb); the archived Swift
generator needs the same trim. -/

open Lean Winnow WinnowApp WinnowApp.RecordsReal
open Tx (BitcoinNetwork)

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

def netJ (j : Json) : IO BitcoinNetwork := do
  match BitcoinNetwork.ofString? (← need (str j "network")) with
  | some n => pure n
  | none => bad "network"

def bytesJ (j : Json) (k : String) : IO ByteArray := do
  match ofHex? (← need (str j k)) with
  | some b => pure b
  | none => bad s!"{k}: not hex"

def tempDir : IO System.FilePath := IO.FS.createTempDir

def withTemp {α} (f : System.FilePath → IO α) : IO α := do
  let d ← tempDir
  try f d finally try IO.FS.removeDirAll d catch _ => pure ()

def memoryKeys : IO (IO.Ref (Std.HashMap String ByteArray) × StoreKeyVault) := do
  let ref ← IO.mkRef {}
  return (ref, StoreKeyVault.inMemory ref)

/-! ## Files -/

def otherNetwork (n : BitcoinNetwork) : BitcoinNetwork := if n == .regtest then .signet else .regtest

def fileBytes (j : Json) (store : String) (network : BitcoinNetwork) (key : Option ByteArray) : IO (Option ByteArray) := do
  let some template := optS j "payload" | return none
  let payload := (((optS j "prefix").bind ofHex?).getD .empty) ++ template.toUTF8
  let k := key.getD (ByteArray.mk (Array.replicate 32 7))
  match (optS j "wrap").getD "plain" with
  | "plain" => return some payload
  | "sealed" => return some (SealedStoreFile.sealed payload store network k)
  | "badmac" => return some (SealedStoreFile.sealed payload store network (k.set! 0 (k[0]! ^^^ 1)))
  | "othernet" => return some (SealedStoreFile.sealed payload store (otherNetwork network) k)
  | "otherstore" => return some (SealedStoreFile.sealed payload (if store == "people" then "vaults" else "people") network k)
  | "truncated" => return some "winnow-store-mac-v1 abcd".toUTF8
  | "tampered" =>
    let s := SealedStoreFile.sealed payload store network k
    return some (s.set! (s.size - 1) (s[s.size - 1]! ^^^ 1))
  | "big" => return some (payload ++ ByteArray.mk (Array.replicate (4 * 1_024 * 1_024 + 1) 0x20))
  | _ => bad "wrap"

/-! ## Summaries -/

def payToJ : Option PersonPayTo → Json
  | some (.descriptor t) => arr [jstr "descriptor", jstr t]
  | some (.address t) => arr [jstr "address", jstr t]
  | some (.silentPayment t) => arr [jstr "silentPayment", jstr t]
  | none => .null

def personJ (p : PersonRecord) (ids : String → String := id) : Json :=
  arr [jstr (ids p.id), jstr p.name, payToJ p.payTo, jnat p.nextPaymentIndex.toNat,
    jopt Json.bool p.savedRecipient, jopt (jstr ∘ PersonRecord.provenanceRaw) p.destinationProvenance,
    jopt jstr p.destinationSource]

def sortStrings (xs : List String) : List String := xs.mergeSort (fun a b => decide (a ≤ b))

def labelsJ (labels : Array (String × String)) (ids : String → String := id) : Json :=
  let sorted := labels.toList.mergeSort (fun a b => decide (a.1 ≤ b.1))
  arr (sorted.map fun (k, v) => arr [jstr k, jstr (ids v)])

def resultJ : OpenResult → List (String × Json)
  | .missing => [("result", jstr "missing"), ("message", .null)]
  | .loaded => [("result", jstr "loaded"), ("message", .null)]
  | .damaged m => [("result", jstr "damaged"), ("message", jstr m)]

def afterJ (path : System.FilePath) (store : String) (network : BitcoinNetwork)
    (keys : IO.Ref (Std.HashMap String ByteArray)) : IO Json := do
  unless ← path.pathExists do return Json.mkObj [("exists", .bool false)]
  let data ← IO.FS.readBinFile path
  let mut out : List (String × Json) := [("exists", .bool true), ("sealed", .bool (SealedStoreFile.isSealed data))]
  let opened := match (← keys.get)[s!"{store}.{networkRaw network}"]? with
    | some key => (SealedStoreFile.open data store network key).toOption
    | none => none
  match opened with
  | some payload =>
    out := out ++ [("verifies", .bool true), ("payload", jstr (hex payload))]
  | none => out := out ++ [("verifies", .bool false)]
  return Json.mkObj out

/-! ## Ops -/

def sealSeal (j : Json) : IO Json := do
  return ok (jstr (hex (SealedStoreFile.sealed (← bytesJ j "payload") (← need (str j "store")) (← netJ j) (← bytesJ j "key"))))

def sealOpen (j : Json) : IO Json := do
  match SealedStoreFile.open (← bytesJ j "data") (← need (str j "store")) (← netJ j) (← bytesJ j "key") with
  | .ok p => return ok (jstr (hex p))
  | .error e => return errJ e.name

def storeOpen (j : Json) : IO Json := do
  let network ← netJ j
  let store ← need (str j "kind")
  let (ref, keys) ← memoryKeys
  let key := (optS j "key").bind ofHex?
  if let some k := key then ref.modify (·.insert s!"{store}.{networkRaw network}" k)
  withTemp fun dir => do
    let path := dir / s!"{store}.json"
    if let some b ← fileBytes j store network key then IO.FS.writeBinFile path b
    unless store == "people" do bad "kind: only the people store remains"
    let (s, r) ← PeopleStore.configure keys (some path) network
    let mut out : List (String × Json) :=
      resultJ r ++ [("records", arr (s.records.toList.map (personJ ·))), ("labels", labelsJ s.senderByTxid)]
    out := out ++ [("keyNow", .bool ((← ref.get).contains s!"{store}.{networkRaw network}")),
                   ("after", ← afterJ path store network ref)]
    return ok (Json.mkObj out)

def provenanceOf (s : String) : Option Provenance :=
  match s with
  | "supplied" => some .supplied | "localFunding" => some .localFunding | "explorerFunding" => some .explorerFunding
  | _ => none

def replaceAll (text old new : String) : String := new.intercalate (text.splitOn old)

def peopleScript (j : Json) : IO Json := do
  let network ← netJ j
  let (ref, keys) ← memoryKeys
  let steps ← need (j.getObjValAs? (Array Json) "steps")
  withTemp fun dir => do
    let path := dir / "people.json"
    let wd := writeAtomically
    let (s0, _) ← PeopleStore.configure keys (some path) network
    let mut store := s0
    let mut ids : Array String := #[]
    let mut replies : Array Json := #[]
    for step in steps do
      let op := (optS step "op").getD ""
      let k := (step.getObjValAs? Int "ref").toOption.getD (-1)
      let refId := if k ≥ 0 && k.toNat < ids.size then ids[k.toNat]! else "nobody"
      let mut extra : List (String × Json) := []
      let attempt : RM (PeopleStore × Option String × List (String × Json)) := do
        match op with
        | "add" =>
          let payTo ← match optS step "paste" with
            | some paste => do pure (← liftNamed network (PersonPaste.parse paste network)).payTo
            | none => pure none
          let provenance := (optS step "provenance").bind provenanceOf
          let id ← RM.io uuidString
          let (s, r) ← store.add keys wd id ((optS step "name").getD "") payTo provenance (optS step "source")
          return (s, some r.id, [])
        | "update" =>
          let (s, _) ← store.updateRecipient keys wd refId (optS step "name") ((step.getObjValAs? Bool "saved").toOption.getD true)
          return (s, none, [])
        | "remove" => return (← store.remove keys wd refId, none, [])
        | "attach" =>
          let parsed ← liftNamed network (PersonPaste.parse ((optS step "paste").getD "") network)
          let some payTo := parsed.payTo | throw (namedError "unrecognised" network)
          let provenance := ((optS step "provenance").bind provenanceOf).getD .supplied
          return (← store.attachDestination keys wd refId payTo provenance (optS step "source"), none, [])
        | "label" => return (← store.labelSender keys wd ((optS step "txid").getD "") refId, none, [])
        | "unlabel" => return (← RM.io (store.removeSenderLabel keys wd ((optS step "txid").getD "")), none, [])
        | "advance" =>
          let index := ((step.getObjValAs? Nat "index").toOption.getD 0).toUInt32
          return (← store.advancePaymentIndex keys wd refId index, none, [])
        | "tamper" | "reopen" =>
          if op == "tamper" then
            if ← RM.io path.pathExists then
              let data ← RM.io (IO.FS.readBinFile path)
              if data.size ≥ 2 then RM.io (IO.FS.writeBinFile path (data.set! (data.size - 2) (data[data.size - 2]! ^^^ 1)))
          let (s, r) ← RM.io (PeopleStore.configure keys (some path) network)
          return (s, none, resultJ r)
        | _ => RM.io (bad "step")
      match ← attempt.run with
      | .ok (s, newId, more) =>
        store := s
        if let some nid := newId then
          if !ids.contains nid then ids := ids.push nid
          extra := [("id", jstr s!"#{ids.idxOf nid}")]
        extra := extra ++ more ++ [("ok", .bool true)]
      | .error (.io e) => if (toString e).startsWith "bad-request" then throw e else extra := [("error", jstr "ioError")]
      | .error e => extra := [("error", jstr e.name)]
      let rename : String → String := fun x => if ids.contains x then s!"#{ids.idxOf x}" else x
      let after ← afterJ path "people" network ref
      let payload := match (after.getObjValAs? String "payload").toOption.bind ofHex? with
        | some b =>
          let t := Keys.Unicode.decodeUTF8Lossy b
          jstr (ids.toList.zipIdx.foldl (fun acc (id, i) => replaceAll acc id s!"#{i}") t)
        | none => .null
      replies := replies.push (Json.mkObj (extra ++ [("people", arr (store.records.toList.map (personJ · rename))),
        ("labels", labelsJ store.senderByTxid rename), ("payload", payload)]))
    return ok (.arr replies)

def recordsDerive (j : Json) : IO Json := do
  let network ← netJ j
  let (_, keys) ← memoryKeys
  withTemp fun dir => do
    let pp := dir / "people.json"
    if let some p := optS j "people" then IO.FS.writeFile pp p
    let (ps, pr) ← PeopleStore.configure keys (some pp) network
    let people := ps.records
    let recipients := (recipientByScript people network).toList.map fun (s, p) => (hex s, p.id)
    let resultName : OpenResult → String | .missing => "missing" | .loaded => "loaded" | .damaged _ => "damaged"
    return ok (Json.mkObj [
      ("peopleResult", jstr (resultName pr)),
      ("recipients", arr ((recipients.mergeSort (fun a b => decide (a.1 ≤ b.1))).map fun (s, i) => arr [jstr s, jstr i])),
      ("people", arr (people.toList.map fun p => arr [jstr p.id,
        .bool p.derivesFreshAddresses, .bool p.isSavedRecipient, .bool p.hasUnverifiedFundingDestination,
        jopt jstr (p.payTo.bind fun t => (t.addressAt p.nextPaymentIndex network).toOption)]))])

def ownKey (j : Json) : IO Json := do
  let network ← netJ j
  let d ← match Descriptor.parse (← need (str j "descriptor")) with
    | .ok d => pure d
    | .error e => return errJ e.name
  let r : RM Json := do
    let bare ← ownKeyExpressionOf d false
    let multipath ← ownKeyExpressionOf d true
    let card ← ownPersonCardOf d network (← RM.io (need (str j "name")))
    return ok (arr [jstr bare, jstr multipath, jstr card.serialized])
  match ← r.run with
  | .ok v => return v
  | .error e => return errJ e.name

def paste (j : Json) : IO Json := do
  match ← (parsePaste (← netJ j) (← need (str j "text"))).run with
  | .ok p => return ok (arr [jopt jstr p.name, jopt Json.bool p.payTo])
  | .error e => return errJ e.name

def labelsRun (j : Json) : IO Json := do
  let network ← netJ j
  let walletID ← need (str j "walletID")
  let steps := ((j.getObjValAs? (Array Json) "steps").toOption).getD #[]
  withTemp fun dir => do
    let path := dir / "receive-labels.json"
    if let some f := optS j "file" then IO.FS.writeBinFile path ((((optS j "prefix").bind ofHex?).getD .empty) ++ f.toUTF8)
    let mut store ← LabelStore.open (some path) walletID network
    let labelsOut (s : LabelStore) : Json :=
      arr ((s.labels.toList.map fun (k, v) => (hex k, v)).mergeSort (fun a b => decide (a.1 ≤ b.1)) |>.map fun (k, v) => arr [jstr k, jstr v])
    let mut replies : Array Json := #[]
    for step in steps do
      let mut reply : List (String × Json) := []
      match ← (store.setLabel writeAtomically ((optS step "label").getD "") ((optS step "address").getD "")).run with
      | .ok s => store := s; reply := [("ok", .bool true)]
      | .error e => reply := [("error", jstr e.name)]
      let file ← if ← path.pathExists then pure (jstr (Keys.Unicode.decodeUTF8Lossy (← IO.FS.readBinFile path))) else pure .null
      replies := replies.push (Json.mkObj (reply ++ [("labels", labelsOut store), ("file", file)]))
    return ok (Json.mkObj [("notice", jopt jstr store.notice), ("labels", labelsOut store), ("steps", .arr replies)])

def lookupParse (j : Json) : IO Json := do
  let data := (((optS j "prefix").bind ofHex?).getD .empty) ++ (← need (str j "data")).toUTF8
  match ← (parseFundingAddresses data (← netJ j) (optS j "expected")).run with
  | .ok xs => return ok (arr (xs.map jstr))
  | .error (.lookup m) => return Json.mkObj [("error", jstr "unavailable"), ("message", jstr m)]
  | .error e => return errJ e.name

def ops : Std.HashMap String (Json → IO Json) := Std.HashMap.ofList [
  ("seal.seal", sealSeal), ("seal.open", sealOpen), ("store.open", storeOpen), ("people.script", peopleScript),
  ("records.derive", recordsDerive), ("own.key", ownKey), ("paste", paste), ("labels.run", labelsRun),
  ("lookup.parse", lookupParse)]

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
