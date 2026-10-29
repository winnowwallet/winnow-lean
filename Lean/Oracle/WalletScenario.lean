import Oracle.Wallet

/-! Wallet scenarios (Lean side of `LeanOracle/Wallet/Scenario.swift`): one request runs a seeded
sequence of wallet operations — create / open / import, fund and apply blocks, addresses, sends and
commits, fee bumps, rollbacks, export, verification — and reports every step's result together with the
wallet's view and its wallet file, canonicalized.

Signatures carry BIP340 auxiliary randomness the Swift wallet draws itself, so signed bytes are never
compared: transactions are reported without witnesses (plus the witness item lengths), PSBT signature and
witness values by length, and pending sends in the wallet file without witnesses. The change position is
pinned by the request (the Swift driver rebuilds until its random draw agrees). -/

namespace Oracle.WalletScenario
open Lean Winnow

structure Ctx where
  dir : System.FilePath
  network : Tx.BitcoinNetwork
  secrets : IO.Ref Keys.InMemorySecrets
  draws : IO.Ref (List Float)
  changePos : IO.Ref Nat
  aux : IO.Ref Nat
  wallets : Std.HashMap String Wallet := {}
  txs : Std.HashMap String Transaction := {}
  sends : Std.HashMap String PreparedSend := {}
  bumps : Std.HashMap String PreparedFeeBump := {}
  bundles : Std.HashMap String String := {}

def Ctx.random (c : Ctx) : Randomness where
  entropy := pure (ByteArray.mk (Array.replicate 16 0))
  draw := do
    match ← c.draws.get with
    | x :: rest => c.draws.set rest; pure x
    | [] => pure 0.5
  changePosition _ := c.changePos.get
  auxRand := do
    let n ← c.aux.modifyGet fun n => (n, n + 1)
    pure (ByteArray.mk (Array.replicate 32 (n % 256).toUInt8))

def Ctx.keyStore (c : Ctx) : Keys.KeyStore IO := inMemoryKeyStore c.secrets

def wname (st : Json) : String := (str st "w").toOption.getD "a"
def walletPath (c : Ctx) (n : String) : System.FilePath := c.dir / s!"{n}.json"

/-! ## Reporting -/

def outpointS (o : Transaction.Outpoint) : Json := Json.str (hex o.txid ++ ":" ++ toString o.vout)
def i64S (v : Int64) : Json := Json.str (toString v.toInt)
def utxoS (u : WalletUTXO) : Json := Json.str (SwiftJSON.write u.toJV)

def witnessShape (tx : Transaction) : Json :=
  Json.arr (tx.inputs.map fun i => Json.arr (i.witness.map fun w => Json.num w.size))

def unsignedHex (tx : Transaction) : Json := hexJ (tx.serialized false)

/-- Input values that carry signatures, nonces or witnesses: reported by length. -/
def randomInputTypes : List UInt8 := [0x08, 0x13, 0x14, 0x1B, 0x1C]

def pairsJ (ps : Array PSBT.KeyValue) (random : Bool) : Json :=
  Json.arr (ps.map fun kv =>
    let v := if random && randomInputTypes.contains kv.type then Json.str s!"len:{kv.value.size}" else hexJ kv.value
    Json.arr #[hexJ kv.key, v])

def psbtShape (p : PSBT) : Json :=
  Json.mkObj [("globals", pairsJ p.globals false), ("inputs", Json.arr (p.inputs.map (pairsJ ·.pairs true))),
    ("outputs", Json.arr (p.outputs.map (pairsJ ·.pairs false)))]

def builtJ (b : BuiltTransaction) : List (String × Json) :=
  [("txid", hexJ b.transaction.txid), ("tx", unsignedHex b.transaction), ("witness", witnessShape b.transaction),
   ("fee", i64S b.fee), ("change", optJ i64S b.changeAmount), ("psbt", psbtShape b.psbt)]

def effectJ (e : MatchEffect) : Json :=
  Json.mkObj [("received", Json.arr (e.received.map utxoS)),
    ("spent", Json.arr (e.spent.map fun s => Json.mkObj [("txid", hexJ s.txid), ("vout", Json.num s.vout.toNat),
      ("spentBy", hexJ s.spentBy), ("height", Json.num s.height.toNat)])),
    ("discarded", Json.arr (e.discardedReplacements.map hexJ))]

def reportJ (r : ImportReport) : Json :=
  Json.mkObj [("from", Json.num r.scannedFromHeight.toNat), ("to", optJ (fun (h : UInt32) => Json.num h.toNat) r.scannedToHeight),
    ("matches", Json.bool r.matchesBundle), ("confirmed", Json.arr (r.confirmedUTXOs.map utxoS)),
    ("spentSince", Json.arr (r.spentSinceBundle.map fun s => Json.mkObj [("txid", hexJ s.txid), ("vout", Json.num s.vout.toNat),
      ("spentBy", hexJ s.spentBy), ("height", Json.num s.height.toNat)])),
    ("discovered", Json.arr (r.discoveredUTXOs.map utxoS))]

/-- The wallet file, decoded and re-encoded with pending sends' witnesses stripped. -/
def canonicalFile (path : System.FilePath) : IO Json := do
  unless ← path.pathExists do return Json.null
  let text ← IO.FS.readFile path
  match WalletState.decode text with
  | .error e => return Json.str s!"undecodable:{e}"
  | .ok s =>
    let strip (p : PendingSend) : PendingSend := match Transaction.decode p.rawTransaction with
      | .ok tx => { p with rawTransaction := tx.serialized false }
      | .error _ => p
    let s := { s with pendingSends := s.pendingSends.map strip }
    match s.encode with
    | .ok t => return Json.str t
    | .error e => return Json.str s!"unencodable:{e}"

def viewJ (w : Wallet) : IO Json := do
  let s ← w.state
  return Json.mkObj [("balance", i64S (← w.balance)), ("spendable", Json.arr ((Wallet.spendableUtxosOf s).map (outpointS ·.outpoint))),
    ("bumpable", Json.arr ((← w.feeBumpableTxids).map hexJ)),
    ("indices", Json.arr #[Json.num s.creationHeight.toNat, Json.num s.nextScanHeight.toNat, Json.num s.nextReceiveIndex.toNat,
      Json.num s.nextChangeIndex.toNat]),
    ("rows", Json.arr #[Json.num s.utxos.size, Json.num s.allUtxos.size, Json.num s.history.size]),
    ("rates", Json.arr (s.observedFeeRates.map bitsJ))]

/-! ## Requests -/

def bad {α} (what : String) : IO α := throw (IO.userError s!"bad-request: {what}")

def unknownRef {α} (what : String) : IO α := throw (IO.userError s!"unknownRef: {what}")

def need {α} (r : Except String α) : IO α := match r with | .ok a => pure a | .error e => bad e

def wallet (c : Ctx) (n : String) : IO Wallet := match c.wallets[n]? with
  | some w => pure w
  | none => unknownRef s!"no wallet {n}"

def chainOf (n : Nat) : AddressChain := if n == 1 then .change else .receive

/-- An output's script: `{"script": hex}` or `{"to": {"chain", "index", "w"?}}` (derived by the wallet). -/
def scriptOf (c : Ctx) (cur : String) (o : Json) : IO (Except String ByteArray) := do
  match field o "script" with
  | .str _ => return .ok (← need (hxJ (field o "script")))
  | _ =>
    let to := field o "to"
    let w ← wallet c ((str to "w").toOption.getD cur)
    match ← (w.scriptPubKey (chainOf ((nat to "chain").toOption.getD 0)) ((nat to "index").toOption.getD 0).toUInt32).run with
    | .ok s => return .ok s
    | .error e => return .error e.name

def coinbaseInput : Transaction.Input :=
  { previousOutput := ⟨ByteArray.mk (Array.replicate 32 0), 0xFFFF_FFFF⟩, scriptSig := ByteArray.mk #[0x01], sequence := 0xFFFF_FFFF }

def txOf (c : Ctx) (cur : String) (spec : Json) : IO (Except String Transaction) := do
  if let .ok r := str spec "ref" then
    match c.txs[r]? with
    | some t => return .ok t
    | none => unknownRef s!"no tx {r}"
  let ins := match field spec "inputs" with | .arr xs => xs | _ => #[]
  let mut inputs : Array Transaction.Input := #[]
  for i in ins do
    if i == Json.str "coinbase" then inputs := inputs.push coinbaseInput; continue
    let txid ← match str i "ref" with
      | .ok r => match c.txs[r]? with
        | some t => pure t.txid
        | none => unknownRef s!"no tx {r}"
      | .error _ => need (hxJ (field i "txid"))
    let witness ← need (listJ hxJ (field i "witness"))
    inputs := inputs.push {
      previousOutput := ⟨txid, ((nat i "vout").toOption.getD 0).toUInt32⟩, scriptSig := .empty,
      sequence := ((nat i "seq").toOption.getD 0xFFFF_FFFD).toUInt32, witness := witness }
  let outs := match field spec "outputs" with | .arr xs => xs | _ => #[]
  let mut outputs : Array Transaction.Output := #[]
  for o in outs do
    match ← scriptOf c cur o with
    | .ok s => outputs := outputs.push { value := ← need (i64J (field o "amount")), scriptPubKey := s }
    | .error e => return .error e
  return .ok { version := 2, inputs := inputs, outputs := outputs, locktime := ((nat spec "locktime").toOption.getD 0).toUInt32 }

def fakeMatch (height : UInt32) (txs : Array Transaction) : Net.BlockMatch :=
  let header : Net.BlockHeader := {
    version := 2, previousHash := ByteArray.mk (Array.replicate 32 0),
    merkleRoot := ByteArray.mk (Array.replicate 32 0xAA), time := 1_700_000_000 + height, bits := 0x207F_FFFF, nonce := 0,
    hash := .empty }
  { height := height, blockHash := .empty, block := { header := header, transactions := txs } }

def blockOf (c : Ctx) (cur : String) (b : Json) : IO (Except String Net.BlockMatch) := do
  let specs := match field b "txs" with | .arr xs => xs | _ => #[]
  let mut txs := #[]
  for t in specs do
    match ← txOf c cur t with
    | .ok tx => txs := txs.push tx
    | .error e => return .error e
  return .ok (fakeMatch ((nat b "height").toOption.getD 0).toUInt32 txs)

def paymentsOf (c : Ctx) (cur : String) (st : Json) : IO (Except String (Array Payment)) := do
  let ps := match field st "payments" with | .arr xs => xs | _ => #[]
  let mut out := #[]
  for p in ps do
    match ← scriptOf c cur p with
    | .ok s => out := out.push { amount := ← need (i64J (field p "amount")), scriptPubKey := s }
    | .error e => return .error e
  return .ok out

def txRef (c : Ctx) (st : Json) : IO ByteArray := do
  match str st "ref" with
  | .ok r => match c.txs[r]? with
    | some t => pure t.txid
    | none => unknownRef s!"no tx {r}"
  | .error _ => need (hxJ (field st "txid"))

def setDraws (c : Ctx) (st : Json) : IO Unit := do
  let ds ← need (listJ dblJ (field st "draws"))
  c.draws.set ds.toList
  c.changePos.set ((nat st "changePos").toOption.getD 0)

/-- One step: the updated context and the step's result (`.ok` value, or the error name). -/
def step (c : Ctx) (st : Json) : IO (Ctx × Except String Json) := do
  let cur := wname st
  let run {α} (x : WM α) (k : α → IO (Ctx × Json)) : IO (Ctx × Except String Json) := do
    match ← x.run with
    | .ok a => let (c', j) ← k a; pure (c', .ok j)
    | .error e => pure (c, .error e.name)
  let fail (e : String) : IO (Ctx × Except String Json) := pure (c, .error e)
  match ← need (str st "do") with
  | "create" =>
    let entropy ← match field st "entropy" with | .str _ => some <$> need (hxJ (field st "entropy")) | _ => pure none
    let persist := (st.getObjValAs? Bool "persist").toOption.getD true
    let path := if persist then some (walletPath c cur) else none
    run (Wallet.create c.network c.keyStore path entropy ((nat st "height").toOption.getD 0).toUInt32
        ((nat st "account").toOption.getD 0).toUInt32 c.random) fun w =>
      pure ({ c with wallets := c.wallets.insert cur w }, Json.mkObj [("id", Json.str w.id), ("descriptor", Json.str w.descriptor.serialized)])
  | "writeFile" =>
    IO.FS.writeFile (walletPath c cur) (← need (str st "json"))
    pure (c, .ok Json.null)
  | "open" =>
    let src := (str st "from").toOption.getD cur
    run (Wallet.«open» (walletPath c src) c.keyStore c.random) fun w =>
      pure ({ c with wallets := c.wallets.insert cur w }, Json.mkObj [("id", Json.str w.id), ("descriptor", Json.str w.descriptor.serialized)])
  | "importing" =>
    let text ← match str st "bundle" with
      | .ok b => match c.bundles[b]? with | some t => pure t | none => unknownRef s!"no bundle {b}"
      | .error _ => need (str st "json")
    match ImportBundle.decode text with
    | .error e => fail e.name
    | .ok bundle =>
      let persist := (st.getObjValAs? Bool "persist").toOption.getD true
      run (Wallet.importing bundle c.keyStore (if persist then some (walletPath c cur) else none) c.random) fun w =>
        pure ({ c with wallets := c.wallets.insert cur w }, Json.mkObj [("id", Json.str w.id), ("descriptor", Json.str w.descriptor.serialized)])
  | "apply" =>
    let w ← wallet c cur
    match ← blockOf c cur st with
    | .error e => fail e
    | .ok m =>
      let mut c := c
      if let .ok n := str st "name" then
        for i in [0:m.block.transactions.size] do
          c := { c with txs := c.txs.insert s!"{n}.{i}" m.block.transactions[i]! }
      match ← (w.apply m).run with
      | .ok e => pure (c, .ok (effectJ e))
      | .error e => pure (c, .error e.name)
  | "recordScanHeight" =>
    let w ← wallet c cur
    run (w.recordScanHeight ((nat st "h").toOption.getD 0).toUInt32) fun _ => pure (c, Json.null)
  | "freshReceiveAddress" =>
    let w ← wallet c cur
    run w.freshReceiveAddress fun a => pure (c, Json.str a)
  | "address" =>
    let w ← wallet c cur
    let chain := chainOf ((nat st "chain").toOption.getD 0)
    let index := ((nat st "index").toOption.getD 0).toUInt32
    run (do return (← w.address chain index, ← w.scriptPubKey chain index)) fun (a, s) =>
      pure (c, Json.mkObj [("address", Json.str a), ("spk", hexJ s)])
  | "watchScripts" =>
    let w ← wallet c cur
    run w.watchScripts fun xs => pure (c, Json.arr ((xs.map hex).qsort (· < ·) |>.map Json.str))
  | "buildSend" =>
    let w ← wallet c cur
    match ← paymentsOf c cur st with
    | .error e => fail e
    | .ok payments =>
      setDraws c st
      let rate ← need (dblJ (field st "rate"))
      run (w.buildSend payments rate ((nat st "tip").toOption.getD 0).toUInt32) fun p => do
        let name := (str st "name").toOption.getD "send"
        pure ({ c with sends := c.sends.insert name p, txs := c.txs.insert name p.built.transaction },
          Json.mkObj (builtJ p.built ++ [("selected", Json.arr (p.selected.map (outpointS ·.outpoint))),
            ("changeIndex", Json.num p.changeIndex.toNat),
            ("changeOutputIndex", optJ (fun (i : UInt32) => Json.num i.toNat) p.changeOutputIndex)]))
  | "commit" =>
    let w ← wallet c cur
    let some p := c.sends[(str st "name").toOption.getD "send"]? | unknownRef "no send"
    run (w.commit p) fun _ => pure (c, Json.null)
  | "pendingFeeRate" =>
    let w ← wallet c cur
    run (w.pendingFeeRate (← txRef c st)) fun r => pure (c, bitsJ r)
  | "previewFeeBump" =>
    let w ← wallet c cur
    run (w.previewFeeBump (← txRef c st) (← need (dblJ (field st "rate")))) fun p =>
      pure (c, Json.mkObj [("current", bitsJ p.currentFeeRateSatPerVByte), ("rate", bitsJ p.feeRateSatPerVByte),
        ("fee", i64S p.fee), ("change", optJ i64S p.changeAmount), ("tx", unsignedHex p.replacementTransaction)])
  | "buildFeeBump" =>
    let w ← wallet c cur
    let txid ← txRef c st
    let rate ← need (dblJ (field st "rate"))
    run (do
        let b ← w.buildFeeBump txid rate
        let preview ← ExceptT.lift (w.previewFeeBump txid rate).run
        let authorized := match preview with
          | Except.ok p => p.authorizes b.built
          | Except.error _ => false
        return (b, authorized)) fun (b, authorized) => do
      let name := (str st "name").toOption.getD "bump"
      pure ({ c with bumps := c.bumps.insert name b, txs := c.txs.insert name b.built.transaction },
        Json.mkObj (builtJ b.built ++ [("authorized", Json.bool authorized),
          ("changeOutputIndex", optJ (fun (i : UInt32) => Json.num i.toNat) b.changeOutputIndex)]))
  | "commitFeeBump" =>
    let w ← wallet c cur
    let some b := c.bumps[(str st "name").toOption.getD "bump"]? | unknownRef "no bump"
    run (w.commitFeeBump b) fun _ => pure (c, Json.null)
  | "rollBack" =>
    let w ← wallet c cur
    run (w.rollBack ((nat st "h").toOption.getD 0).toUInt32) fun _ => pure (c, Json.null)
  | "exportBundle" =>
    let w ← wallet c cur
    run (w.exportBundle ((st.getObjValAs? Bool "mnemonic").toOption.getD false)) fun b => do
      let text := b.serialized
      pure ({ c with bundles := c.bundles.insert ((str st "name").toOption.getD "bundle") text }, Json.str text)
  | "rememberTransaction" =>
    let w ← wallet c cur
    let some tx := c.txs[(← need (str st "ref"))]? | unknownRef "no tx"
    run (w.rememberTransaction tx) fun _ => pure (c, Json.null)
  | "verifyImport" =>
    let w ← wallet c cur
    let some text := c.bundles[(str st "bundle").toOption.getD "bundle"]? | unknownRef "no bundle"
    match ImportBundle.decode text with
    | .error e => fail e.name
    | .ok bundle =>
      let specs := match field st "blocks" with | .arr xs => xs | _ => #[]
      let mut blocks := #[]
      for b in specs do
        match ← blockOf c cur b with
        | .ok m => blocks := blocks.push m
        | .error e => return (c, .error e)
      let toH : Option UInt32 := (nat st "to").toOption.map (·.toUInt32)
      let source := ScanSource.scripted ((nat st "from").toOption.getD 0).toUInt32 blocks toH
      run (w.verifyImport bundle source (← need (listJ hxJ (field st "additional")))) fun r => pure (c, reportJ r)
  | "keystore" =>
    let w ← wallet c cur
    match ← need (str st "action") with
    | "delete" => discard (w.keyStore.delete w.id).run; pure (c, .ok Json.null)
    | "toXprv" =>
      match ← (w.keyStore.load w.id).run with
      | .ok (.mnemonic words) =>
        let some master := (Keys.HDKey.ofSeed (Keys.BIP39.seed words)).toOption | bad "seed"
        discard (w.keyStore.delete w.id).run
        discard (w.keyStore.store (.masterKey (master.serialized (Wallet.hdNetwork c.network))) w.id).run
        pure (c, .ok Json.null)
      | _ => pure (c, .error "notMnemonic")
    | a => bad s!"keystore {a}"
  | d => bad s!"step {d}"

def scenario (j : Json) : IO Json := do
  let some network := Tx.BitcoinNetwork.ofString? ((str j "network").toOption.getD "signet") | return err "bad-request: network"
  let tmp := (← IO.getEnv "TMPDIR").getD "/tmp"
  let dir := System.FilePath.mk tmp / s!"winnow-lean-scenario-{hex (← IO.getRandomBytes 8)}"
  IO.FS.createDirAll dir
  let mut c : Ctx := { dir, network, secrets := ← IO.mkRef {}, draws := ← IO.mkRef [], changePos := ← IO.mkRef 0, aux := ← IO.mkRef 1 }
  let steps := match field j "steps" with | .arr xs => xs | _ => #[]
  let mut out : Array Json := #[]
  try
    for st in steps do
      let (c', r) ← try step c st catch e =>
        if (toString e).startsWith "unknownRef" then pure (c, .error "unknownRef") else throw e
      c := c'
      let cur := wname st
      let mut o : List (String × Json) := match r with
        | .ok v => [("r", v)]
        | .error e => [("e", Json.str e)]
      if let some w := c.wallets[cur]? then
        let file ← match w.storagePath with
          | some p => canonicalFile p
          | none => pure Json.null
        o := o ++ [("view", ← viewJ w), ("file", file)]
      out := out.push (Json.mkObj o)
    IO.FS.removeDirAll dir
    return ok (Json.arr out)
  catch e =>
    try IO.FS.removeDirAll dir catch _ => pure ()
    let msg := toString e
    return err (if msg.startsWith "bad-request" then msg else s!"bad-request: {msg}")

def ops : List (String × (Json → IO Json)) := [("wallet.scenario", scenario)]

end Oracle.WalletScenario
