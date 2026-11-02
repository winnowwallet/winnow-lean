import Winnow.Ledger
import TestKit.Check
import TestKit.Fixtures
open Winnow Winnow.Ledger Winnow.Keys Winnow.SwiftJSON TestKit

/-! `ledger-test`: the Ledger signer's tests (Phase C).

Ports `Tests/WalletCoreTests/LedgerTests.swift` (upstream 1cf93fb), all of it (pairAndSpend,
storedRegistration, twoOfThreeWithRecovery, ledgerSignsFirst, refusals, wrongKeyRefused and the pure
tests), the three Ledger cases of upstream d2ca878's `NestedMultisigTests.swift` (`nestedLedgerTests`),
and checks the port against Swift itself through recorded sessions:

* `Vectors/ledger-bitcoin-app.json` — Ledger's own vectors (policy ids, Taproot addresses), copied
  unchanged from upstream's `Tests/WalletCoreTests/Vectors` (provenance in its README there).
* `Vectors/ledger-sessions.json` — whole sessions recorded from the Swift at 1cf93fb: Swift's
  `LedgerBitcoinClient`/`LedgerMultisig` against Swift's `LedgerSimulator`, every APDU and reply in
  order, for a 2-of-2 (pair, register, show an address, the Ledger signs a two-input spend, a
  refusal on the device, a mainnet key request) and a 2-of-3 with a recovery leaf. Recorded by
  `LedgerRecordTests.swift`, kept with the oracle harness outside this tree
  (`~/src/winnow-lean-swift-archive/LedgerRecorder/`; add it to the tests of a copy of the Swift at
  1cf93fb and run `LEDGER_RECORD_OUT=… swift test --filter LedgerRecordTests`).

  - client replay: the Lean client must send byte-identical APDUs and reach the same results and
    signed PSBT from the recorded replies;
  - simulator replay: the Lean simulator, fed the recorded APDUs, must answer byte-identical replies;
  - live: the Lean client against the Lean simulator.

Usage: `lake exe ledger-test [vectors directory]` (default `Vectors`, run from `Lean/`). -/

def h (s : String) : ByteArray := ofHex! s
def bytes (xs : List Nat) : ByteArray := ByteArray.mk (xs.map (·.toUInt8)).toArray

def isErr {α ε} : Except ε α → Bool | .error _ => true | .ok _ => false
def errName {α} : Except LedgerError α → String | .error e => e.name | .ok _ => "ok"

/-! ## JSON access -/

def field (v : JV) (k : String) : JV := match v with
  | .obj kvs => (lookup kvs k).getD .null
  | _ => .null
def str (v : JV) : String := match v with | .str s => s | _ => ""
def num (v : JV) : Nat := match v with | .num t => t.toNat?.getD 0 | _ => 0
def arr (v : JV) : Array JV := match v with | .arr xs => xs | _ => #[]
def strs (v : JV) : Array String := (arr v).map str
def steps (v : JV) : Array (ByteArray × ByteArray) :=
  (arr (field v "exchanges")).map fun e => let xs := arr e; (h (str xs[0]!), h (str xs[1]!))

/-! ## Transports -/

/-- Over the Lean simulator, as a state. -/
abbrev SimM := StateT Simulator (Except LedgerError)

def simExchange (apdu : ByteArray) : SimM ByteArray :=
  modifyGet fun s => let (s', reply) := s.exchange apdu; (reply, s')

def runSim {α} (p : Program α) (s : Simulator) : Except LedgerError (α × Simulator) := (p.run simExchange).run s

/-- Over a recording: each APDU must be the recorded one; the recorded reply comes back. -/
abbrev ReplayM := ExceptT LedgerError (StateM (Array (ByteArray × ByteArray) × Nat))

def replayExchange (apdu : ByteArray) : ReplayM ByteArray := do
  let (log, i) ← get
  let some (expected, reply) := log[i]? | throw (.transport s!"replay: APDU {i} past the recording")
  unless apdu == expected do throw (.transport s!"replay: APDU {i} differs: {hex apdu} vs {hex expected}")
  set (log, i + 1)
  return reply

/-- Runs `p` against a recording; the result, and whether every recorded exchange was used. -/
def replay {α} (p : Program α) (log : Array (ByteArray × ByteArray)) : Except LedgerError α × Bool :=
  let (r, (_, used)) := ((p.run replayExchange).run).run (log, 0)
  (r, used == log.size)

/-- Feeds recorded APDUs to the simulator; the index of the first reply that differs, if any. -/
def replaySimulator (s : Simulator) (log : Array (ByteArray × ByteArray)) : Simulator × Option Nat := Id.run do
  let mut s := s
  for h : i in [0:log.size] do
    let (apdu, reply) := log[i]
    let (s', got) := s.exchange apdu
    s := s'
    if got != reply then return (s, some i)
  return (s, none)

/-! ## Fixtures -/

/-- The three signers (`TestKit.masters`): the phone 0xA1, the Ledger 0xB2, a third 0xC3. -/
initialize testMasters : Array HDKey ← masters

def get! {α} [Inhabited α] (e : Except LedgerError α) : α := match e with | .ok a => a | .error _ => default

/-- The template with each `@i/**` replaced by its key and `/<0;1>/*` (LedgerTests.descriptor). -/
def templateDescriptor (template : String) (keys : Array String) : String := Id.run do
  let mut text := template
  for index in (List.range keys.size).reverse do
    text := (text.replace s!"@{index}/**" (keys[index]! ++ "/<0;1>/*")).replace s!"@{index}/<" (keys[index]! ++ "/<")
  return text

/-- A key expression as a descriptor key (via `tr(KEY)`). -/
def singleKey (text : String) : Descriptor.SingleKey :=
  match Descriptor.parse s!"tr({text})" with
  | .ok { expression := .tr k } => k
  | _ => default

/-! ## Ledger's published vectors -/

def vectorTests (dir : String) : IO Unit := do
  say "ledger's vectors"
  let some v := parse? (← IO.FS.readFile s!"{dir}/ledger-bitcoin-app.json") | check "vectors parse" false; return
  let registers := arr (field v "register")
  check "at least 10 register vectors" (registers.size ≥ 10) s!"{registers.size}"
  for r in registers do
    let policy := WalletPolicy.make (str (field r "walletName")) (str (field r "template")) (strs (field r "keys"))
    check s!"policy id {str (field r "name")}" ((policy.map (hex ·.id)).toOption == some (str (field r "walletID")))
  let addresses := arr (field v "addresses")
  check "an address vector uses sortedmulti_a" (addresses.any fun a => ((str (field a "template")).splitOn "sortedmulti_a").length > 1)
  for a in addresses do
    let text := templateDescriptor (str (field a "template")) (strs (field a "keys"))
    let derived := (Descriptor.parse text).toOption.bind fun d =>
      ((d.derived (num (field a "index")).toUInt32 .signet).toOption.bind (·[num (field a "change")]?)).map (·.address)
    check s!"address {str (field a "name")}" (derived == some (str (field a "address"))) s!"{derived}"
  say s!"  {registers.size} policy ids, {addresses.size} addresses"

/-! ## Merkle, framing, interpreter -/

def merkleTests : IO Unit := do
  say "merkle"
  let expected := #[
    "0000000000000000000000000000000000000000000000000000000000000000",
    "96a296d224f285c67bee93c30f8a309157f0daa35dc5b87e410b78630a09cfc7",
    "a20bf9a7cc2dc8a08f5f415a71b19f6ac427bab54d24eec868b5d3103449953a",
    "3b6cccd7e3e023ff393006f030315ee7ad9eb111b022b41fba7e5b7a3973f688",
    "9bcd51240af4005168f033121ba85be5a6ed4f0e6a5fac262066729b8fbfdecb",
    "b855b42d6c30f5b087e05266783fbd6e394f7b926013ccaa67700a8b0c5a596f",
    "bb36e7d3d4cee5720cbd323d02fab15962e2ba1dadf5f8fc6eeef4fd6ad056a8",
    "3560191803028444b232018ac047fdb561c09c23a7a6876c85e08b5e4d48e9f3",
    "ef7f49b620f6c7ea9b963a214da34b5021c6ded8ed57734380a311ab726aa907",
    "162a21c2230e0284ea38cb8739ee4bb75947a1acd5d529c638ec068969fb3c4a"]
  for count in [0:expected.size] do
    let leaves := (Array.range count).map fun i => Merkle.elementHash (bytes [i])
    check s!"root of {count} leaves" (hex (Merkle.root leaves) == expected[count]!)
  let seven := (Array.range 7).map fun i => Merkle.elementHash (bytes [i])
  check "proof of leaf 5 of 7" ((Merkle.proof seven 5).map hex == #[
    "4f35212d12f9ad2036492c95f1fe79baf4ec7bd9bef3dffa7579f2293ff546a4",
    "40d88127d4d31a3891f41598eeed41174e5bc89b1eb9bbd66a8cbfc09956a3fd",
    "9bcd51240af4005168f033121ba85be5a6ed4f0e6a5fac262066729b8fbfdecb"])
  -- Every proof of every tree up to 40 leaves recomputes the root (the simulator's checker).
  let mut ok := true
  for n in [1:41] do
    let leaves := (Array.range n).map fun i => Merkle.elementHash (bytes [i])
    for i in [0:n] do
      if Simulator.rootOf leaves[i]! i n (Merkle.proof leaves i).toList.reverse != some (Merkle.root leaves) then ok := false
  check "proofs recompute their roots, 1 to 40 leaves" ok

def framingTests : IO Unit := do
  say "framing"
  for length in [5, 15, 16, 17, 150, 260] do
    let apdu := ByteArray.mk ((Array.range length).map (·.toUInt8))
    for frameSize in [20, 23, 156] do
      match BluetoothFraming.frames apdu frameSize with
      | .error _ => check s!"frames {length}/{frameSize}" false
      | .ok frames =>
        check s!"frame sizes {length}/{frameSize}" (frames.all fun f => f.size ≤ frameSize && f[0]! == 0x05)
        let mut r : BluetoothFraming.Reassembler := {}
        let mut reply : Option ByteArray := none
        for f in frames do
          match r.receive f with
          | .ok (r', out) => r := r'; reply := out
          | .error _ => reply := none
        check s!"round trip {length} bytes in {frameSize}-byte frames" (reply == some apdu)
  let frames := get! (BluetoothFraming.frames (ByteArray.mk (Array.replicate 100 7)) 20)
  let r1 := get! ((({} : BluetoothFraming.Reassembler).receive frames[0]!).map (·.1))
  check "a frame out of sequence is refused" (isErr (r1.receive frames[2]!))
  check "MTU reply 153" (BluetoothFraming.frameSize? (bytes [0x08, 0, 0, 0, 1, 153]) == some 153)
  check "not an MTU reply" (BluetoothFraming.frameSize? (bytes [0x05, 0, 0, 0, 1, 153]) == none)
  -- Beyond the Swift test: exact frames, an empty APDU, refusals.
  check "two frames of a 20-byte APDU at 20" ((get! (BluetoothFraming.frames (ByteArray.mk (Array.replicate 20 1)) 20)).map hex ==
    #["0500000014" ++ String.join (List.replicate 15 "01"), "050001" ++ String.join (List.replicate 5 "01")])
  check "an empty APDU is one frame" ((get! (BluetoothFraming.frames .empty 20)).map hex == #["0500000000"])
  check "frame size 5 is refused" (isErr (BluetoothFraming.frames (bytes [1]) 5))
  check "a frame without the tag" (isErr (({} : BluetoothFraming.Reassembler).receive (bytes [0x06, 0, 0, 0, 1, 9])))
  check "a first frame without a length" (isErr (({} : BluetoothFraming.Reassembler).receive (bytes [0x05, 0, 0, 0])))
  check "write frame size is capped" (Bluetooth.writeFrameSize 153 (some 100) == 100 && Bluetooth.writeFrameSize 153 none == 153)
  check "notify characteristic" (Bluetooth.notifyCharacteristic Bluetooth.serviceIdentifiers[0]! == "13D63400-2C97-0004-0001-4C6564676572")
  check "write characteristic" (Bluetooth.writeCharacteristic Bluetooth.serviceIdentifiers[1]! == "13D63400-2C97-6004-0002-4C6564676572")
  let router : Bluetooth.NotificationRouter := {}
  check "router: MTU reply while asking for the frame size"
    ((router.receive (bytes [0x08, 0, 0, 0, 1, 153]) (some .frameSize)).2.map (·.toOption) == some (some (bytes [0x08, 0, 0, 0, 1, 153])))
  check "router: other notifications are ignored" ((router.receive (bytes [0x05, 0, 0]) (some .written)).2.isNone)
  let replyFrames := get! (BluetoothFraming.frames (bytes [0x90, 0x00]) 20)
  check "router: a reply while awaiting one"
    ((router.receive replyFrames[0]! (some .reply)).2.map (·.toOption) == some (some (bytes [0x90, 0x00])))

def interpreterTests : IO Unit := do
  say "interpreter"
  let long := ByteArray.mk ((Array.range 300).map (·.toUInt8))
  let mut i := ({} : Interpreter).addKnownPreimage long
  let (i1, first) := get! (i.execute (bytes [0x40, 0x00] ++ sha256 long))
  i := i1
  let firstParsed := (do
    let total ← Reader.compact
    let n ← Reader.u8
    return (total, ← Reader.bytes n.toNat) : Reader _).run first
  let (total, chunk) := match firstParsed with | .ok (r, _) => r | .error _ => (0, .empty)
  check "preimage length 300" (total == 300)
  let mut received := chunk
  let mut rounds := 0
  let mut allOneByte := true
  while received.size < 300 && rounds < 10 do
    rounds := rounds + 1
    let (i2, more) := get! (i.execute (bytes [0xA0]))
    i := i2
    if more.size < 2 then break
    if more[1]! != 1 then allOneByte := false
    received := received ++ more.extract 2 (2 + more[0]!.toNat)
  check "long preimage over GET_MORE_ELEMENTS" (received == long && allOneByte)

  let elements := (Array.range 200).map fun k => s!"key {k}".toUTF8
  i := i.addKnownList elements
  let leaves := elements.map Merkle.elementHash
  let root := Merkle.root leaves
  let (i3, proofReply) := get! (i.execute (bytes [0x41] ++ root ++ bytes [0xC8, 0x9B]))
  i := i3
  check "leaf 155 of 200" (proofReply.extract 0 32 == leaves[155]!)
  check "proof length and six sent" (proofReply[32]!.toNat == (Merkle.proof leaves 155).size && proofReply[33]! == 6)
  check "a request before the queue is drained is refused" (isErr (i.execute (bytes [0x40, 0x00] ++ ByteArray.mk (Array.replicate 32 0))))
  for _ in [0:10] do
    let (i4, more) := get! (i.execute (bytes [0xA0]))
    i := i4
    if more[0]!.toNat < 7 then break
  check "leaf index 42" ((i.execute (bytes [0x42] ++ root ++ leaves[42]!)).toOption.map (hex ·.2) == some "012a")
  check "leaf not found" ((i.execute (bytes [0x42] ++ root ++ ByteArray.mk (Array.replicate 32 0))).toOption.map (hex ·.2) == some "0000")
  check "leaf search in an unknown tree" (isErr (i.execute (bytes [0x42] ++ ByteArray.mk (Array.replicate 64 0))))

  let fresh : Interpreter := {}
  check "unknown preimage" (errName (fresh.execute (bytes [0x40, 0x00] ++ ByteArray.mk (Array.replicate 32 0))) == "protocolViolation")
  check "unknown tree" (isErr (fresh.execute (bytes [0x41] ++ root ++ bytes [0xC8, 0x00])))
  check "unknown command" (isErr (fresh.execute (bytes [0x99])))
  match fresh.execute (bytes [0x10, 0x01, 0x02]) with
  | .ok (y, reply) => check "yield" (reply.isEmpty && y.yielded.map hex == #["0102"])
  | .error _ => check "yield" false
  -- Beyond the Swift test: malformed and unsupported requests, by message.
  let msg {α} : Except LedgerError α → String | .error (.protocolViolation m) => m | _ => ""
  check "empty request" (msg (fresh.execute .empty) == "an unknown client command")
  check "short preimage request" (msg (fresh.execute (bytes [0x40])) == "a malformed client command")
  check "unsupported preimage request" (msg (fresh.execute (bytes [0x40, 0x01])) == "an unsupported preimage request")
  check "trailing bytes" (msg (fresh.execute (bytes [0x40, 0x00] ++ ByteArray.mk (Array.replicate 33 0))) == "a malformed client command")
  check "more elements with nothing queued" (msg (fresh.execute (bytes [0xA0])) == "a request for elements that were never queued")
  check "non-canonical size" (msg (fresh.execute (bytes [0x41] ++ root ++ bytes [0xFD, 0xC8, 0x00, 0x00])) == "a malformed client command")

/-! ## Errors, yields, the program, the registration record -/

def unitTests : IO Unit := do
  say "errors, yields, programs"
  check "status words" ([0x6985, 0x5515, 0x6E00, 0x6E01, 0x6D00, 0x6D02, 0x6511, 0x6A82].map (fun w => (LedgerError.ofStatus w).name) ==
    ["rejectedOnDevice", "deviceLocked", "appNotOpen", "appNotOpen", "appNotOpen", "appNotOpen", "appNotOpen", "status"])
  check "status description" ((LedgerError.status 0x6a82).description == "The Ledger refused the request (status 6A82).")
  check "short reply" (errName (Response.parse (bytes [0x90])) == "transport")
  check "overlong APDU" (errName (APDU.bitcoin .signPSBT (ByteArray.mk (Array.replicate 256 0))).serialized == "protocolViolation")
  check "APDU bytes" ((APDU.bitcoin .getMasterFingerprint).serialized.toOption.map hex == some "e105000100")
  let key := ByteArray.mk (Array.replicate 32 2)
  let leaf := ByteArray.mk (Array.replicate 32 3)
  let sig := ByteArray.mk (Array.replicate 64 4)
  check "a script-path yield" ((Client.signatureOfYield (bytes [1, 64] ++ key ++ leaf ++ sig) 2).toOption ==
    some (some { inputIndex := 1, publicKey := key, leafHash := some leaf, signature := sig }))
  check "a key-path yield" ((Client.signatureOfYield (bytes [0, 32] ++ key ++ sig) 1).toOption ==
    some (some { inputIndex := 0, publicKey := key, leafHash := none, signature := sig }))
  check "a MuSig2 yield is skipped" ((Client.signatureOfYield (bytes [0xFE, 0, 0, 0, 0x80, 1, 2]) 1).toOption == some none)
  check "an input that does not exist" (errName (Client.signatureOfYield (bytes [2, 32] ++ key ++ sig) 2) == "protocolViolation")
  check "a signature of the wrong length" (errName (Client.signatureOfYield (bytes [0, 32] ++ key ++ bytes [1, 2, 3]) 1) == "protocolViolation")
  check "a key of the wrong length" (errName (Client.signatureOfYield (bytes [0, 31] ++ key.extract 0 31 ++ sig) 1) == "protocolViolation")
  check "a malformed yield" (errName (Client.signatureOfYield (bytes [0, 40] ++ key) 1) == "protocolViolation")
  check "names" (WalletPolicy.isValidName "Savings" &&
    ["", " leading", "trailing ", String.ofList (List.replicate 65 'x'), "café"].all (!WalletPolicy.isValidName ·))
  check "a policy needs keys" (errName (WalletPolicy.make "A" "tr(@0/**)" #[]) == "mismatch")
  let r : Registration :=
    { policyName := "Winnow 2-of-2"
      policyID := ByteArray.mk (Array.replicate 32 1)
      hmac := ByteArray.mk (Array.replicate 32 2)
      masterFingerprint := 0x08914939
      keyPath := Multisig.keyPath .signet }
  check "registration JSON round trip" ((LedgerRegistration.ofJV r.toJV).toOption == some r)
  -- The step interface gives what `run` gives.
  let sim := Simulator.new testMasters[1]!
  let mut p := Client.masterFingerprint
  let mut s := sim
  let mut sent := 0
  while sent < 5 do
    let some apdu := p.pending? | break
    let (s', reply) := s.exchange apdu
    s := s'
    p := p.feed reply
    sent := sent + 1
  check "step interface" (sent == 1 && (match p with | .done fp => fp == testMasters[1]!.fingerprint | _ => false))

/-! ## Recorded Swift sessions -/

def sessionTests (dir : String) : IO Unit := do
  let some v := parse? (← IO.FS.readFile s!"{dir}/ledger-sessions.json") | check "sessions parse" false; return
  -- 2-of-2
  say "swift sessions: 2-of-2"
  let c := field v "twoOfTwo"
  let name := "Winnow 2-of-2"
  let template := str (field c "template")
  let keys := strs (field c "keys")
  let expression := str (field (field c "signerExpression") "expression")
  let fingerprint := (num (field (field c "signerExpression") "fingerprint")).toUInt32
  -- The policy from the account's descriptor, as LedgerWalletPolicy(name:account:) builds it.
  let descriptor := (Descriptor.parse (str (field c "descriptor"))).toOption
  let fromDescriptor := descriptor.bind fun d => (WalletPolicy.ofDescriptor name d).toOption
  check "policy from the account descriptor" (fromDescriptor.map (fun p => (p.template, p.keys)) == some (template, keys))
  let some policy := fromDescriptor | return
  check "policy id" (hex policy.id == str (field c "policyId"))
  let firstAddress := str (field c "firstAddress")
  check "the descriptor's first address" ((descriptor.bind fun d => (d.derived 0 .signet).toOption.bind (·[0]?)).map (·.address) == some firstAddress)
  let makePolicy := fun n => WalletPolicy.make n template keys

  let (r1, used1) := replay (Multisig.signerExpression .signet) (steps (field c "signerExpression"))
  check "client replay: signer expression" (r1.toOption == some (expression, fingerprint) && used1) s!"{errName r1}"
  let path := Multisig.keyPath .signet
  let signers := match descriptor with
    | some { expression := .trTree _ (.leaf (.sortedMultiA _ ks)) } => ks
    | _ => #[]
  check "the account has a signer for this Ledger" (Multisig.ledgerSigner signers fingerprint path).isSome
  let (r2, used2) := replay (Multisig.registerWith signers .signet makePolicy name fingerprint firstAddress) (steps (field c "register"))
  let hmac := h (str (field (field c "register") "hmac"))
  check "client replay: register" ((r2.toOption.map fun r => (hex r.policyID, r.hmac, r.policyName, r.keyPath)) ==
    some (str (field c "policyId"), hmac, name, path) && used2) s!"{errName r2}"
  let registration := get! r2
  let d := field c "display"
  let (r3, used3) := replay (Multisig.displayAddressWith makePolicy registration (num (field d "choice")) (num (field d "index")).toUInt32
    (str (field d "address"))) (steps d)
  check "client replay: display address" (r3.toOption == some (str (field d "address")) && used3) s!"{errName r3}"
  let sf := field c "signFirst"
  let unsigned := (PSBT.parse (h (str (field sf "psbt")))).toOption.get!
  let (r4, used4) := replay (Multisig.signWith unsigned makePolicy registration) (steps sf)
  check "client replay: sign" used4 s!"{errName r4}"
  match r4 with
  | .ok (.ok (signed, added)) =>
    check "the Ledger's two signatures are applied as Swift applies them"
      (hex signed.serialized == str (field sf "signed") && added == num (field sf "added"))
  | _ => check "the Ledger's signatures verify" false
  let rj := field c "reject"
  let (r5, used5) := replay (Multisig.signWith unsigned makePolicy registration) (steps rj)
  check "client replay: refused on the device" (errName r5 == "rejectedOnDevice" && used5) s!"{match r5 with | .error e => toString e | _ => "ok"} {used5}"
  let (r6, used6) := replay (Multisig.signerExpression .mainnet) (steps (field c "mainnet"))
  check "client replay: a mainnet key request" ((match r6 with | .error (.status 0x6A82) => true | _ => false) && used6) s!"{match r6 with | .error e => toString e | _ => "ok"} {used6}"

  -- The same recordings into the Lean simulator.
  let mut s := Simulator.new testMasters[1]!
  for (label, log) in [("signer expression", steps (field c "signerExpression")), ("register", steps (field c "register")),
      ("display", steps d), ("sign", steps sf)] do
    let (s', bad) := replaySimulator s log
    s := s'
    check s!"simulator replay: {label} ({log.size} exchanges)" bad.isNone s!"first difference at {bad}"
  s := s.setDecision .reject
  let (s', bad) := replaySimulator s (steps rj)
  check "simulator replay: refused on the device" bad.isNone s!"first difference at {bad}"
  s := s'.setDecision .approve
  let (s', bad) := replaySimulator s (steps (field c "mainnet"))
  check "simulator replay: a mainnet key request" bad.isNone
  check "simulator state" (s'.registeredNames == #[name] && s'.displayedAddresses == #[str (field d "address")])

  -- Live: the Lean client against the Lean simulator.
  say "live: Lean client and Lean simulator"
  let sim := Simulator.new testMasters[1]!
  match runSim (Multisig.signerExpression .signet) sim with
  | .error e => check "live: signer expression" false e.name
  | .ok ((expr, fp), sim) =>
    check "live: signer expression" (expr == expression && fp == testMasters[1]!.fingerprint &&
      expr.startsWith s!"[{Descriptor.hex8 testMasters[1]!.fingerprint}/87'/1'/0']tpub")
    match runSim (Multisig.registerWith signers .signet makePolicy name fp firstAddress) sim with
    | .error e => check "live: register" false e.name
    | .ok (reg, sim) =>
      check "live: register" (reg.policyID == policy.id && sim.registeredNames == #[name])
      let expected4 := (descriptor.bind fun d => (d.derived 4 .signet).toOption.bind (·[0]?)).map (·.address)
      match runSim (Multisig.displayAddressWith makePolicy reg 0 4 (expected4.getD "")) sim with
      | .error e => check "live: display" false e.name
      | .ok (shown, sim) =>
        check "live: display" (some shown == expected4 && sim.displayedAddresses == #[shown])
        match runSim (Multisig.signWith unsigned makePolicy reg) sim with
        | .ok (.ok (signed, added), sim) =>
          check "live: the Ledger signs both inputs" (added == 2 && hex signed.serialized == str (field sf "signed"))
          -- Signing again adds nothing.
          match runSim (Multisig.signWith signed makePolicy reg) sim with
          | .ok (.error (.ledger (.mismatch m)), _) => check "live: a second signing adds nothing" (m == "the Ledger added no signature")
          | _ => check "live: a second signing adds nothing" false
        | _ => check "live: the Ledger signs both inputs" false
        -- Refusals leave the PSBT alone (the caller keeps it).
        match runSim (Multisig.signWith unsigned makePolicy reg) (sim.setDecision .reject) with
        | .error .rejectedOnDevice => check "live: refused on the device" true
        | _ => check "live: refused on the device" false
        let other := { reg with policyName := "Another account" }
        check "live: another account's registration" (match runSim (Multisig.signWith unsigned makePolicy other) sim with
          | .error (.mismatch _) => true | _ => false)
        -- A device that flips one bit in every yielded signature.
        let tamper : ByteArray → SimM ByteArray := fun apdu => do
          let reply ← simExchange apdu
          if reply.size > 70 && reply[0]! == 0x10 && reply[reply.size - 2]! == 0xE0 && reply[reply.size - 1]! == 0x00 then
            return reply.set! (reply.size - 3) (reply[reply.size - 3]! ^^^ 0x01)
          return reply
        match ((Multisig.signWith unsigned makePolicy reg).run tamper).run sim with
        | .ok (.error (.ledger (.mismatch m)), _) => check "live: a bad signature is refused" (m == "a Ledger signature does not verify")
        | _ => check "live: a bad signature is refused" false
        match runSim (Multisig.displayAddressWith makePolicy reg 0 5 (expected4.getD "")) sim with
        | .error (.mismatch m) => check "live: a different address is refused" (m == "the Ledger shows a different address")
        | _ => check "live: a different address is refused" false
  check "live: a mainnet key is refused" (isErr (runSim (Multisig.signerExpression .mainnet) (Simulator.new testMasters[1]!)))
  check "live: an account without this Ledger" (match runSim (Multisig.registerWith #[] .signet makePolicy name fingerprint firstAddress)
    (Simulator.new testMasters[1]!) with | .error (.mismatch m) => m == "this account has no signer for this Ledger" | _ => false)
  check "live: a wrong first address" (match runSim (Multisig.registerWith signers .signet makePolicy name fingerprint "tb1q")
    (Simulator.new testMasters[1]!) with | .error (.mismatch m) => m == "the Ledger derives a different first address" | _ => false)

  -- 2-of-3 with a recovery leaf.
  say "swift sessions: 2-of-3 with recovery"
  let c := field v "twoOfThreeRecovery"
  let name := "Family 2-of-3"
  let template := str (field c "template")
  let keys := strs (field c "keys")
  check "the recovery template" (template ==
    "tr(@0/**,{sortedmulti_a(2,@1/**,@2/**,@3/**),and_v(v:multi_a(1,@1/<2;3>/*,@2/<2;3>/*,@3/<2;3>/*),older(10))})" && keys.size == 4)
  -- The tree as the account holds it: its signers on /<0;1>/* and again on /<2;3>/* in the recovery leaf.
  let signerKeys := (keys.extract 1 4).map fun k => singleKey (k ++ "/<0;1>/*")
  let recoveryKeys := (keys.extract 1 4).map fun k => singleKey (k ++ "/<2;3>/*")
  let tree : Descriptor.ScriptTree := .branch (.leaf (.sortedMultiA 2 signerKeys)) (.leaf (.timelocked (.multiA 1 recoveryKeys) 10))
  let fromTree := WalletPolicy.ofTree name (singleKey (keys[0]! ++ "/<0;1>/*")) tree
  check "policy from the account tree" ((fromTree.toOption.map fun p => (p.template, p.keys, hex p.id)) ==
    some (template, keys, str (field c "policyId")))
  check "timelocked pk leaf" ((WalletPolicy.ofTree name (singleKey (keys[0]! ++ "/<0;1>/*"))
    (.branch (.leaf (.multiA 1 (signerKeys.extract 0 2))) (.leaf (.timelocked (.pk recoveryKeys[2]!) 144)))).toOption.map (·.template) ==
    some "tr(@0/**,{multi_a(1,@1/**,@2/**),and_v(v:pk(@3/<2;3>/*),older(144))})")
  -- Upstream d2ca878 (nested accounts): any tree is templated in the descriptor's shape.
  check "a three-leaf tree keeps its shape" ((WalletPolicy.ofTree name (singleKey (keys[0]! ++ "/<0;1>/*"))
    (.branch (.leaf (.multiA 1 signerKeys)) (.branch (.leaf (.multiA 1 recoveryKeys)) (.leaf (.multiA 1 signerKeys))))).toOption.map (·.template) ==
    some "tr(@0/**,{multi_a(1,@1/**,@2/**,@3/**),{multi_a(1,@1/<2;3>/*,@2/<2;3>/*,@3/<2;3>/*),multi_a(1,@1/**,@2/**,@3/**)}})")
  check "a plain pk leaf is refused" (errName (WalletPolicy.ofTree name (singleKey (keys[0]! ++ "/<0;1>/*")) (.leaf (.pk signerKeys[0]!))) == "mismatch")
  check "a key under another suffix is refused" (errName (WalletPolicy.ofTree name (singleKey (keys[0]! ++ "/0/*"))
    (.leaf (.multiA 1 signerKeys))) == "mismatch")
  let makePolicy := fun n => WalletPolicy.make n template keys
  let expression := str (field (field c "signerExpression") "expression")
  let fingerprint := (num (field (field c "signerExpression") "fingerprint")).toUInt32
  let (r1, used1) := replay (Multisig.signerExpression .signet) (steps (field c "signerExpression"))
  check "client replay: signer expression" (r1.toOption == some (expression, fingerprint) && used1)
  let (r2, used2) := replay (Multisig.registerWith signerKeys .signet makePolicy name fingerprint
    (str (field c "firstAddress"))) (steps (field c "register"))
  check "client replay: register" ((r2.toOption.map (hex ·.hmac)) == some (str (field (field c "register") "hmac")) && used2) s!"{errName r2}"
  let registration := get! r2
  let d := field c "display"
  let (r3, used3) := replay (Multisig.displayAddressWith makePolicy registration (num (field d "choice")) (num (field d "index")).toUInt32
    (str (field d "address"))) (steps d)
  check "client replay: display a change address" (r3.toOption == some (str (field d "address")) && used3) s!"{errName r3}"
  let sf := field c "signFirst"
  let unsigned := (PSBT.parse (h (str (field sf "psbt")))).toOption.get!
  -- Applying recovery-leaf signatures needs Phase B's leaf policies; the exchange itself is checked.
  let (r4, used4) := replay (do
    let p ← Program.ofExcept (Multisig.policy makePolicy registration)
    Client.signPSBT unsigned p registration.hmac) (steps sf)
  check "client replay: sign on the recovery path (two yielded signatures)" ((r4.toOption.map (·.size)) == some 2 && used4) s!"{errName r4}"
  -- Only up to the registration's reply: `LedgerMultisig.register` then asks for the first address,
  -- which the simulator derives through a descriptor with the recovery leaf (Phase B).
  let registerLog := steps (field c "register")
  let registered := (registerLog.findIdx? fun (_, reply) => reply.size ≥ 2 && reply[reply.size - 2]! == 0x90).getD 0
  let mut s3 := Simulator.new testMasters[1]!
  for (label, log) in [("signer expression", steps (field c "signerExpression")),
      (s!"registration ({registered + 1} of {registerLog.size} exchanges)", registerLog.extract 0 (registered + 1))] do
    let (s', bad) := replaySimulator s3 log
    s3 := s'
    check s!"simulator replay: {label}" bad.isNone s!"first difference at {bad}"

def ioTests : IO Unit := do
  say "IO transport"
  let ref ← IO.mkRef (Simulator.new testMasters[1]!)
  let r ← (Multisig.signerExpression .signet |>.runIO (Simulator.transport ref)).run
  check "runIO over the shared simulator" ((r.toOption.map (·.2)) == some testMasters[1]!.fingerprint)
  let r ← (Multisig.signerExpression .mainnet |>.runIO (Simulator.transport ref)).run
  check "runIO returns the device's refusal" (match r with | .error (.status 0x6A82) => true | _ => false)

/-! ## Over `MultisigAccount` (upstream's account-level Ledger tests) -/

def ownedChange : Array MultisigAccount.OutputCoordinate := #[{ choice := 1, index := 0 }]

def mam {α} [Inhabited α] (r : MAM α) : α := match r with | .ok a => a | .error _ => default
def mamOk {α} (r : MAM α) : Bool := match r with | .ok _ => true | .error _ => false

/-- Upstream's `spend`: two 60,000-sat coins at receive 0 and 1, 90,000 to an outside key, 2 sat/vB. -/
def twoCoins (a : MultisigAccount) : Array WalletUTXO :=
  (Array.range 2).map fun i =>
    { txid := ByteArray.mk (Array.replicate 32 (0x40 + i.toUInt8)), vout := 0, amount := 60_000,
      scriptPubKey := mam (a.scriptPubKey i.toUInt32 0), chain := .receive, index := i.toUInt32, height := 100 }

def twoCoinSpend (a : MultisigAccount) (utxos : Array WalletUTXO) : MAM PSBT :=
  a.createSpend utxos #[{ amount := 90_000, scriptPubKey := destination }] 0 2 200

structure Pairing where
  account : MultisigAccount
  registration : Registration
  sim : Simulator

/-- Upstream's `pair`: the Ledger's key, a 2-of-2 with the phone's, registered on the simulator. -/
def pair (sessions : JV) : IO (Option Pairing) := do
  let sim := Simulator.new testMasters[1]!
  let .ok ((ledgerKey, fingerprint), sim) := runSim (Multisig.signerExpression .signet) sim | return none
  let .ok d := MultisigAccount.makeDescriptor 2 #[← keyExpression testMasters[0]!, ledgerKey] none .signet | return none
  let .ok account := MultisigAccount.make d .signet | return none
  check "pair: the account is the one Swift built" (d.serialized == str (field (field sessions "twoOfTwo") "descriptor"))
  match runSim (Multisig.register account "Winnow 2-of-2" fingerprint) sim with
  | .ok (registration, sim) => return some { account, registration, sim }
  | .error e => check "pair: register" false e.name; return none

def accountTests (dir : String) : IO Unit := do
  let some sessions := parse? (← IO.FS.readFile s!"{dir}/ledger-sessions.json") | check "sessions parse" false; return
  say "pair and spend (MultisigAccount)"
  let some p ← pair sessions | check "pair" false; return
  check "pair: registered on the device" (p.sim.registeredNames == #["Winnow 2-of-2"])
  check "pair: the registration is the account's policy"
    ((WalletPolicy.ofAccount "Winnow 2-of-2" p.account).toOption.map (·.id) == some p.registration.policyID)
  match runSim (Multisig.displayAddress p.account p.registration 0 4) p.sim with
  | .ok (shown, sim) =>
    check "display address 4" (some shown == (p.account.address 4).toOption && sim.displayedAddresses == #[shown])
  | .error e => check "display address 4" false e.name
  let utxos := twoCoins p.account
  let unsigned := mam (twoCoinSpend p.account utxos)
  let phoneSigned := mam (p.account.sign unsigned testMasters[0]! utxos ownedChange 200 aux0)
  check "the phone's approval" ((p.account.approvals phoneSigned utxos).toOption == some #[0])
  match runSim (Multisig.sign phoneSigned p.account p.registration) p.sim with
  | .ok (.ok (both, added), _) =>
    check "the Ledger adds two signatures" (added == 2)
    check "both approve" ((p.account.approvals both utxos).toOption == some #[0, 1])
    match p.account.finalizeSpend both utxos ownedChange 200 with
    | .ok (_, tx) => check "finalized: four witness items per input" (tx.inputs.all (·.witness.size == 4))
    | .error e => check "finalize" false e.name
  | _ => check "the Ledger signs" false

  say "the Ledger signs first"
  match runSim (Multisig.sign unsigned p.account p.registration) p.sim with
  | .ok (.ok (ledgerSigned, _), _) =>
    check "the Ledger's approval" ((p.account.approvals ledgerSigned utxos).toOption == some #[1])
    let both := mam (p.account.sign ledgerSigned testMasters[0]! utxos ownedChange 200 aux0)
    check "the phone completes it" (mamOk (p.account.finalizeSpend both utxos ownedChange 200))
  | _ => check "the Ledger signs first" false

  say "refusals"
  check "refused on the device" (match runSim (Multisig.sign unsigned p.account p.registration) (p.sim.setDecision .reject) with
    | .error .rejectedOnDevice => true | _ => false)
  check "another account's registration" (match runSim (Multisig.sign unsigned p.account
      { p.registration with policyName := "Another account" }) p.sim with
    | .error (.mismatch _) => true | _ => false)
  let tamper : ByteArray → SimM ByteArray := fun apdu => do
    let reply ← simExchange apdu
    if reply.size > 70 && reply[0]! == 0x10 && reply[reply.size - 2]! == 0xE0 && reply[reply.size - 1]! == 0x00 then
      return reply.set! (reply.size - 3) (reply[reply.size - 3]! ^^^ 0x01)
    return reply
  check "a bad signature" (match ((Multisig.sign unsigned p.account p.registration).run tamper).run p.sim with
    | .ok (.error (.ledger (.mismatch m)), _) => m == "a Ledger signature does not verify" | _ => false)

  say "stored registration"
  let record : MultisigAccountRecord :=
    { id := p.account.id, name := "Winnow 2-of-2", descriptor := p.account.descriptor.serialized, createdAtHeight := 0,
      ledger := some p.registration }
  check "the stored registration belongs" (mamOk (record.checkLedgerRegistration p.account))
  check "the record round-trips" ((MultisigAccountRecord.ofJV record.toJV).toOption == some record)
  let tampered : List (String × (Registration → Registration)) := [
    ("policy id", fun r => { r with policyID := ByteArray.mk (Array.replicate 32 1) }),
    ("name", fun r => { r with policyName := "Renamed" }),
    ("fingerprint", fun r => { r with masterFingerprint := r.masterFingerprint ^^^ 1 }),
    ("key path", fun r => { r with keyPath := #[HDKey.hardenedOffset + 86, HDKey.hardenedOffset + 1, HDKey.hardenedOffset] }),
    ("hmac", fun r => { r with hmac := ByteArray.mk (Array.replicate 31 0) })]
  for (label, f) in tampered do
    check s!"a tampered registration ({label})" (match MultisigAccountRecord.checkLedgerRegistration { record with ledger := some (f p.registration) } p.account with
      | .error (.account (.invalidDescriptor _)) => true | _ => false)
  check "no registration" (mamOk (MultisigAccountRecord.checkLedgerRegistration { record with ledger := none } p.account))

  say "two Winnows and a Ledger: 2-of-3 now, the Ledger alone after 10 blocks"
  let sim := Simulator.new testMasters[1]!
  let .ok ((ledgerKey, fingerprint), sim) := runSim (Multisig.signerExpression .signet) sim | check "signer" false; return
  let .ok d := MultisigAccount.makeDescriptor 2 #[← keyExpression testMasters[0]!, ← keyExpression testMasters[2]!, ledgerKey]
    (some (.fewerSigners 1 10)) .signet | check "2-of-3 descriptor" false; return
  check "the account is the one Swift built" (d.serialized == str (field (field sessions "twoOfThreeRecovery") "descriptor"))
  let account := mam (MultisigAccount.make d .signet)
  let policy := WalletPolicy.ofAccount "Family 2-of-3" account
  check "the recovery template" ((policy.toOption.map fun p => (p.template, p.keys.size)) == some
    ("tr(@0/**,{sortedmulti_a(2,@1/**,@2/**,@3/**),and_v(v:multi_a(1,@1/<2;3>/*,@2/<2;3>/*,@3/<2;3>/*),older(10))})", 4))
  let .ok (registration, sim) := runSim (Multisig.register account "Family 2-of-3" fingerprint) sim
    | check "register the 2-of-3" false; return
  let .ok (_, sim) := runSim (Multisig.displayAddress account registration 1 3) sim
    | check "display change address 3" false; return
  let coin : WalletUTXO :=
    { txid := ByteArray.mk (Array.replicate 32 0x61), vout := 0, amount := 90_000,
      scriptPubKey := mam (account.scriptPubKey 0 0), chain := .receive, index := 0, height := 100 }
  let payment : Payment := { amount := 50_000, scriptPubKey := destination }
  let phoneKey := ((testMasters[0]!.derived "m/86'/1'/0'").toOption.get!).publicKey
  let phone := (account.signers.findIdx? fun s => (MultisigAccount.extendedKey? s).map (·.1.publicKey) == some phoneKey).getD 99
  let ledger := (account.signers.findIdx? fun s => s.origin.map (fun o => o.fingerprint == registration.masterFingerprint
    && o.path == registration.keyPath) == some true).getD 99
  let now := mam (account.createSpend #[coin] #[payment] 0 2 101)
  let now := mam (account.sign now testMasters[0]! #[coin] ownedChange 101 aux0)
  match runSim (Multisig.sign now account registration) sim with
  | .ok (.ok (now, _), _) =>
    check "now: one Winnow and the Ledger" ((account.approvals now #[coin]).toOption == some (#[phone, ledger].qsort (· < ·)))
    check "now: finalized" (mamOk (account.finalizeSpend now #[coin] ownedChange 101))
  | _ => check "now: the Ledger signs" false
  let later := mam (account.createSpend #[coin] #[payment] 0 2 109 .recovery)
  match runSim (Multisig.sign later account registration) sim with
  | .ok (.ok (later, _), _) =>
    check "later: the Ledger alone" ((account.approvals later #[coin] .recovery).toOption == some #[ledger])
    match account.finalizeSpend later #[coin] ownedChange 109 with
    | .ok (_, tx) => check "later: finalized with sequence 10" (tx.inputs[0]!.sequence == 10)
    | .error e => check "later: finalized" false e.name
  | _ => check "later: the Ledger signs" false

  say "swift sessions over the account: 2-of-3 with recovery, in full"
  let c := field sessions "twoOfThreeRecovery"
  let recorded := mam (MultisigAccount.parse (str (field c "descriptor")) .signet)
  let fingerprint := (num (field (field c "signerExpression") "fingerprint")).toUInt32
  let (r2, used2) := replay (Multisig.register recorded "Family 2-of-3" fingerprint) (steps (field c "register"))
  check "client replay: register" ((r2.toOption.map (hex ·.hmac)) == some (str (field (field c "register") "hmac")) && used2)
  let reg := get! r2
  let dj := field c "display"
  let (r3, used3) := replay (Multisig.displayAddress recorded reg (num (field dj "choice")) (num (field dj "index")).toUInt32) (steps dj)
  check "client replay: display" (r3.toOption == some (str (field dj "address")) && used3)
  let sf := field c "signFirst"
  let unsignedRecovery := (PSBT.parse (h (str (field sf "psbt")))).toOption.get!
  let (r4, used4) := replay (Multisig.sign unsignedRecovery recorded reg) (steps sf)
  check "client replay: the recovery-path signatures are applied as Swift applies them" (used4 && match r4 with
    | .ok (.ok (signed, added)) => hex signed.serialized == str (field sf "signed") && added == num (field sf "added")
    | _ => false)
  let mut s := Simulator.new testMasters[1]!
  for (label, log) in [("signer expression", steps (field c "signerExpression")), ("register", steps (field c "register")),
      ("display", steps dj), ("sign", steps sf)] do
    let (s', bad) := replaySimulator s log
    s := s'
    check s!"simulator replay: {label} ({log.size} exchanges)" bad.isNone s!"first difference at {bad}"
  -- And the 2-of-2 recordings through the account wrappers.
  let c := field sessions "twoOfTwo"
  let recorded := mam (MultisigAccount.parse (str (field c "descriptor")) .signet)
  let (r2, used2) := replay (Multisig.register recorded "Winnow 2-of-2" (num (field (field c "signerExpression") "fingerprint")).toUInt32)
    (steps (field c "register"))
  check "client replay over the account: register (2-of-2)" (r2.toOption.isSome && used2)
  let sf := field c "signFirst"
  let (r4, used4) := replay (Multisig.sign ((PSBT.parse (h (str (field sf "psbt")))).toOption.get!) recorded (get! r2)) (steps sf)
  check "client replay over the account: sign (2-of-2)" (used4 && match r4 with
    | .ok (.ok (signed, _)) => hex signed.serialized == str (field sf "signed") | _ => false)

/-! ## Nested accounts with Ledgers (upstream d2ca878's NestedMultisigTests: ledgerPolicy,
thresholdMemberLedgerPolicy, twoLedgers) -/

def occurrences (s t : String) : Nat := (s.splitOn t).length - 1

def nestedCoin (a : MultisigAccount) : WalletUTXO :=
  { txid := ByteArray.mk (Array.replicate 32 0x6E), vout := 0, amount := 100_000,
    scriptPubKey := mam (a.scriptPubKey 0 0), chain := .receive, index := 0, height := 100 }

def nestedSpend (a : MultisigAccount) (coin : WalletUTXO) : PSBT :=
  mam (a.createSpend #[coin] #[{ amount := 40_000, scriptPubKey := destination }] 0 2 101)

def finishedPaths (a : MultisigAccount) (p : PSBT) (coin : WalletUTXO) : Array MultisigAccount.SpendPath :=
  a.signersPaths.filter fun path => match a.approvals p #[coin] path with
    | .ok ap => (ap.size : Int) ≥ a.thresholdOn path
    | .error _ => false

def phoneSign (a : MultisigAccount) (p : PSBT) (m : HDKey) (coin : WalletUTXO) : PSBT :=
  mam (a.sign p m #[coin] ownedChange 101 aux0)

def nestedLedgerTests : IO Unit := do
  say "nested: the Ledger policy carries the whole tree; a Ledger signs both leaves it is in"
  let ms ← #[0xA1, 0xB2, 0xC3, 0xD4].mapM master
  let sim := Simulator.new ms[1]!
  let .ok ((ledgerKey, fingerprint), sim) := runSim (Multisig.signerExpression .signet) sim | check "nested: signer" false; return
  let keys ← ms.mapM keyExpression
  let .ok d := MultisigAccount.makeNestedDescriptor (#[#[keys[0]!, ledgerKey], #[keys[2]!], #[keys[3]!]].map .all) 2 none .signet
    | check "nested: descriptor" false; return
  let account := mam (MultisigAccount.make d .signet)
  let policy := get! (WalletPolicy.ofAccount "Three households" account)
  check "nested: five policy keys" (policy.keys.size == 5)
  check "nested: the template" (policy.template.startsWith "tr(@0/**,{{sortedmulti_a(") policy.template
  check "nested: five keys on /**, four on /<2;3>/*"
    (occurrences policy.template "/**" == 5 && occurrences policy.template "/<2;3>/*" == 4) policy.template
  check "nested: hasLedgerSigner" (Multisig.hasLedgerSigner account fingerprint)
  check "nested: namesALedgerKey" (Multisig.namesALedgerKey account)
  let .ok (registration, sim) := runSim (Multisig.register account "Three households" fingerprint) sim
    | check "nested: register" false; return
  match runSim (Multisig.displayAddress account registration 0 2) sim with
  | .ok (shown, _) => check "nested: the Ledger shows the phone's address" (some shown == (account.address 2).toOption)
  | .error e => check "nested: display" false e.name
  let record : MultisigAccountRecord :=
    { id := account.id, name := "Three households", descriptor := d.serialized, createdAtHeight := 0, ledger := some registration }
  check "nested: the stored registration belongs" (mamOk (record.checkLedgerRegistration account))
  check "nested: another key path does not"
    (!mamOk (MultisigAccountRecord.checkLedgerRegistration { record with ledger := some { registration with
      keyPath := #[HDKey.hardenedOffset + 86, HDKey.hardenedOffset + 1, HDKey.hardenedOffset] } } account))
  let coin := nestedCoin account
  let psbt := phoneSign account (nestedSpend account coin) ms[0]! coin
  match runSim (Multisig.sign psbt account registration) sim with
  | .ok (.ok (signed, added), _) =>
    check "nested: the Ledger signs both of its leaves" (added == 2) s!"{added}"
    check "nested: one member is not enough" (!signed.finalize.toBool)
    let signed := phoneSign account signed ms[3]! coin
    match account.finalizeSpend signed #[coin] ownedChange 101 with
    | .ok (_, tx) => check "nested: the phone's, the Ledger's and C's signatures" (tx.inputs[0]!.witness.size == 5)
    | .error e => check "nested: finalize" false e.name
  | _ => check "nested: the Ledger signs" false

  say "nested: a Ledger inside the 2-of-3 member: the policy fits 512 characters; 27 leaves do not"
  let ms ← #[0xA1, 0xB2, 0xC3, 0xD4, 0xE5].mapM master
  let sim := Simulator.new ms[1]!
  let .ok ((ledgerKey, fingerprint), sim) := runSim (Multisig.signerExpression .signet) sim | check "estate: signer" false; return
  let keys ← ms.mapM keyExpression
  let members : Array MultisigAccount.Member :=
    #[{ keys := #[keys[0]!, ledgerKey, keys[2]!], threshold := 2 }, .all #[keys[3]!], .all #[keys[4]!]]
  let account := mam (do MultisigAccount.make (← MultisigAccount.makeNestedDescriptor members 2 none .signet) .signet)
  let policy := get! (WalletPolicy.ofAccount "Estate" account)
  check "estate: six policy keys" (policy.keys.size == 6)
  check "estate: 335 characters" (policy.template.utf8ByteSize == 335) s!"{policy.template.utf8ByteSize}"
  check "estate: within the limit" (policy.template.utf8ByteSize ≤ WalletPolicy.maximumTemplateLength)
  check "estate: seven leaves" (occurrences policy.template "sortedmulti_a(" == 7)
  check "estate: pairs up to /<6;7>/*" ((policy.template.splitOn "/<6;7>/*").length > 1 && (policy.template.splitOn "/<8;9>/*").length == 1)
  let .ok (registration, sim) := runSim (Multisig.register account "Estate" fingerprint) sim
    | check "estate: register" false; return
  match runSim (Multisig.displayAddress account registration 0 1) sim with
  | .ok (shown, _) => check "estate: the Ledger shows the phone's address" (some shown == (account.address 1).toOption)
  | .error e => check "estate: display" false e.name
  let coin := nestedCoin account
  let psbt := phoneSign account (nestedSpend account coin) ms[0]! coin
  match runSim (Multisig.sign psbt account registration) sim with
  | .ok (.ok (signed, added), _) =>
    check "estate: the Ledger's key is in four leaves" (added == 4) s!"{added}"
    check "estate: nothing finishes yet" (finishedPaths account signed coin).isEmpty
    let signed := phoneSign account signed ms[3]! coin
    check "estate: one leaf finishes" ((finishedPaths account signed coin).size == 1)
    match account.finalizeSpend signed #[coin] ownedChange 101 with
    | .ok (_, tx) => check "estate: five witness items" (tx.inputs[0]!.witness.size == 5)
    | .error e => check "estate: finalize" false e.name
  | _ => check "estate: the Ledger signs" false
  let more ← (Array.range 4).mapM fun i => do keyExpression (← master (0x20 + i.toUInt8))
  let families : Array MultisigAccount.Member := #[members[0]!, { keys := #[keys[3]!, keys[4]!, more[0]!], threshold := 2 },
    { keys := more.extract 1 4, threshold := 2 }]
  let large := mam (do MultisigAccount.make (← MultisigAccount.makeNestedDescriptor families 2 none .signet) .signet)
  check "estate: three families, 27 leaves" (large.signersLeaves.size == 27)
  check "estate: their policy is refused" (errName (WalletPolicy.ofAccount "Estate" large) == "mismatch")
  check "estate: registering it is refused before the device is asked"
    (match runSim (Multisig.register large "Estate" fingerprint) sim with | .error (.mismatch _) => true | _ => false)
  let recovering := mam (do
    MultisigAccount.make (← MultisigAccount.makeNestedDescriptor members 2 (some (.fewerSigners 1 4_320)) .signet) .signet)
  check "estate: five recovery leaves" (recovering.recoveryLeaves.size == 5)
  check "estate: twelve leaves are refused" (errName (WalletPolicy.ofAccount "Estate" recovering) == "mismatch")
  let separate := mam (do
    MultisigAccount.make (← MultisigAccount.makeNestedDescriptor members 2 (some (.separateKeys 1 #[more[0]!] 4_320)) .signet) .signet)
  check "estate: a separate recovery key fits, 368 characters"
    ((WalletPolicy.ofAccount "Estate" separate).toOption.map (·.template.utf8ByteSize) == some 368)
  check "estate: registered once" (sim.registeredNames == #["Estate"])

  say "nested: two phones, each with its Ledger, and a third key"
  let phones ← #[0xA1, 0xC3].mapM master
  let sims := #[Simulator.new (← master 0xB2), Simulator.new (← master 0xD5)]
  let mut ledgerKeys : Array (String × UInt32) := #[]
  for s in sims do
    let .ok (key, _) := runSim (Multisig.signerExpression .signet) s | check "two ledgers: signer" false; return
    ledgerKeys := ledgerKeys.push key
  let third ← master 0xD4
  let members := #[#[← keyExpression phones[0]!, ledgerKeys[0]!.1], #[← keyExpression phones[1]!, ledgerKeys[1]!.1], #[← keyExpression third]]
  let account := mam (do MultisigAccount.make (← MultisigAccount.makeNestedDescriptor (members.map .all) 2 none .signet) .signet)
  let mut registrations : Array Registration := #[]
  for (s, (_, fp)) in sims.zip ledgerKeys do
    let .ok (r, _) := runSim (Multisig.register account "Two households" fp) s | check "two ledgers: register" false; return
    registrations := registrations.push r
  let coin := nestedCoin account
  let psbt := phoneSign account (nestedSpend account coin) phones[0]! coin
  let .ok (.ok (psbt, _), _) := runSim (Multisig.sign psbt account registrations[0]!) sims[0]!
    | check "two ledgers: the first Ledger signs" false; return
  let psbt := phoneSign account psbt phones[1]! coin
  check "two ledgers: not yet" (!psbt.finalize.toBool)
  let .ok (.ok (psbt, _), _) := runSim (Multisig.sign psbt account registrations[1]!) sims[1]!
    | check "two ledgers: the second Ledger signs" false; return
  let complete := account.signersPaths.filter fun path =>
    ((account.approvals psbt #[coin] path).toOption.map (·.size : Array Nat → Int)) == some (account.thresholdOn path)
  check "two ledgers: one four-key leaf finishes" (complete.size == 1 && (account.keysOn complete[0]!).size == 4)
  match account.finalizeSpend psbt #[coin] ownedChange 101 with
  | .ok (_, tx) => check "two ledgers: six witness items" (tx.inputs[0]!.witness.size == 6)
  | .error e => check "two ledgers: finalize" false e.name

def main (args : List String) : IO UInt32 := runMain "ledger-test" do
  let dir := args.headD "Vectors"
  ioTests
  vectorTests dir
  merkleTests
  framingTests
  interpreterTests
  unitTests
  sessionTests dir
  accountTests dir
  nestedLedgerTests
