import Winnow.Ledger.Multisig

/-! # A software stand-in for Ledger's Bitcoin app

Port of `Tests/Support/LedgerSimulator.swift` (upstream 1cf93fb), kept in the library so the app's
test mode can use it as its Ledger. It plays the device side of the app's interactive protocol,
written from the app's documentation separately from the phone's client: it asks for every preimage
and Merkle proof it needs, checks each against the commitment, and signs Taproot script-path inputs
for its own key with a test seed.

It shows the phone speaks the protocol consistently. It does not show a real device agrees:
Ledger's published vectors and a real Nano X do that.

Each interrupted command is replayed from the start with the answers received so far, so the device
logic stays one function. Swift's actor is a value here: `exchange` returns the next state with the
reply; `transport` wraps an `IO.Ref` for callers that want Swift's shared object.

It derives addresses through `Descriptor.parse` (recovery leaves `and_v(…,older(N))` included) and
signs with `PSBT.signScriptPath`, which signs every leaf holding its key whose timelock the input's
sequence meets, as Swift's simulator does.
-/

namespace Winnow.Ledger
open Keys

namespace Simulator

inductive Decision where
  | approve | reject
  deriving Inhabited, BEq, Repr

end Simulator

/-- `LedgerSimulator`. -/
structure Simulator where
  master : HDKey
  decision : Simulator.Decision := .approve
  /-- Addresses shown on the "screen" after a request with display set. -/
  displayedAddresses : Array String := #[]
  /-- Policies the user approved, by name. -/
  registeredNames : Array String := #[]
  registrationKey : ByteArray
  command : Option ByteArray := none
  answers : Array ByteArray := #[]
  /-- The network whose addresses the device shows: signet, as Swift's simulator and Ledger's "Bitcoin
  Test" app do (`tb1…`); regtest for a device built for regtest (`bcrt1…`, as Ledger's regtest build of
  the app shows), which a regtest node's tests need. -/
  network : Tx.BitcoinNetwork := .signet
  deriving Inhabited

namespace Simulator

def new (master : HDKey) (network : Tx.BitcoinNetwork := .signet) : Simulator :=
  { master, registrationKey := sha256 ("winnow-ledger-simulator".toUTF8 ++ master.publicKey), network }

def setDecision (s : Simulator) (decision : Decision) : Simulator := { s with decision }

/-- Why a command stopped: it needs the client's answer to `request` (status 0xE000), or it fails
with a status word. -/
inductive Halt where
  | interrupt (request : ByteArray)
  | failure (status : UInt16)
  deriving Inhabited

/-- The answers the client has given to this command so far, served in order; the first question
past them interrupts the command. -/
structure Session where
  answers : Array ByteArray
  cursor : Nat := 0
  deriving Inhabited

/-- A command's work: the simulator (for what it records) and the session, or a halt. -/
abbrev H := StateT (Simulator × Session) (Except Halt)

def fail {α} (status : UInt16) : H α := throw (.failure status)

/-- Any parse failure is 0x6A80, as Swift's catch-all is. -/
def parse {α} (r : Reader α) (b : ByteArray) (exact : Bool := false) : H α :=
  match (if exact then Reader.runAll r b else (·.1) <$> r.run b) with
  | .ok a => pure a
  | .error _ => fail 0x6A80

def ask (request : ByteArray) : H ByteArray := do
  let (sim, session) ← get
  let some answer := session.answers[session.cursor]? | throw (.interrupt request)
  set (sim, { session with cursor := session.cursor + 1 })
  return answer

def statusBytes (word : UInt16) : ByteArray := ByteArray.mk #[(word >>> 8).toUInt8, (word &&& 0xFF).toUInt8]

def readBE32 : Reader UInt32 := do return (readBE (← Reader.bytes 4) 0 4).toUInt32

def ascii? (b : ByteArray) : Option String := Client.ascii? b

/-- GET_PREIMAGE, then GET_MORE_ELEMENTS until the whole preimage is in; its SHA-256 must be the hash
asked for. -/
def preimage (hash : ByteArray) : H ByteArray := do
  let (total, first) ← parse (do
    let total ← Reader.compact
    let n ← Reader.u8
    return (total, ← Reader.bytes n.toNat)) (← ask (ByteArray.mk #[0x40, 0x00] ++ hash)) (exact := true)
  let mut pre := first
  -- Each answer adds at least one byte, so `total` rounds suffice.
  for _ in [0:total.toNat] do
    if pre.size ≥ total.toNat then break
    let chunk ← parse (do
      let count ← Reader.u8
      unless (← Reader.u8) == 1 && count > 0 do throw "bad"
      Reader.bytes count.toNat) (← ask (ByteArray.mk #[0xA0])) (exact := true)
    pre := pre ++ chunk
  unless pre.size == total.toNat && sha256 pre == hash do fail 0x6A80
  return pre

/-- Recomputes a root from a leaf and its bottom-up proof given top first: the first hash is the
sibling nearest the root. -/
def rootOf (leaf : ByteArray) : (index size : Nat) → (topFirst : List ByteArray) → Option ByteArray
  | _, size, [] => if size ≤ 1 then some leaf else none
  | index, size, top :: rest =>
    if size ≤ 1 then none
    else
      let left := Merkle.leftCount size
      if index < left then (rootOf leaf index left rest).map (Merkle.combine · top)
      else (rootOf leaf (index - left) (size - left) rest).map (Merkle.combine top ·)

/-- GET_MERKLE_LEAF_PROOF (and more elements), checked against `root`. -/
def leaf (root : ByteArray) (size index : Nat) : H ByteArray := do
  let request := ByteArray.mk #[0x41] ++ root ++ compactSize size.toUInt64 ++ compactSize index.toUInt64
  let (leaf, proofLength, first) ← parse (do
    let leaf ← Reader.bytes 32
    let proofLength ← Reader.u8
    let sent ← Reader.u8
    let mut proof : Array ByteArray := #[]
    for _ in [0:sent.toNat] do proof := proof.push (← Reader.bytes 32)
    return (leaf, proofLength.toNat, proof)) (← ask request) (exact := true)
  let mut proof := first
  for _ in [0:proofLength] do
    if proof.size ≥ proofLength then break
    let more ← parse (do
      let count ← Reader.u8
      unless (← Reader.u8) == 32 && count > 0 do throw "bad"
      let mut hashes : Array ByteArray := #[]
      for _ in [0:count.toNat] do hashes := hashes.push (← Reader.bytes 32)
      return hashes) (← ask (ByteArray.mk #[0xA0])) (exact := true)
    proof := proof ++ more
  unless proof.size == proofLength && rootOf leaf index size proof.toList.reverse == some root do fail 0x6A80
  return leaf

/-- A committed list element: its leaf, then its 0x00-prefixed preimage. -/
def element (root : ByteArray) (size index : Nat) : H ByteArray := do
  let pre ← preimage (← leaf root size index)
  unless pre[0]? == some 0x00 do fail 0x6A80
  return pre.extract 1 pre.size

structure Commitment where
  count : Nat
  keysRoot : ByteArray
  valuesRoot : ByteArray

def readCommitment : Reader Commitment := do
  return { count := (← Reader.compact).toNat, keysRoot := ← Reader.bytes 32, valuesRoot := ← Reader.bytes 32 }

def map (c : Commitment) : H (Array (ByteArray × ByteArray)) := do
  let mut pairs := #[]
  for index in [0:c.count] do
    let key ← element c.keysRoot c.count index
    let value ← element c.valuesRoot c.count index
    pairs := pairs.push (key, value)
  return pairs

def serializedMap (pairs : Array (ByteArray × ByteArray)) : ByteArray := Id.run do
  let mut data := ByteArray.empty
  for (k, v) in pairs do data := data ++ compactSize k.size.toUInt64 ++ k ++ compactSize v.size.toUInt64 ++ v
  return data.push 0x00

/-- A registered policy, rebuilt from what the client serves. -/
structure Policy where
  name : String
  template : String
  keys : Array String

def policy (serialized : ByteArray) : H Policy := do
  let (name, templateLength, templateHash, keyCount, keysRoot) ← parse (do
    unless (← Reader.u8) == 0x02 do throw "version"
    let nameLength ← Reader.u8
    let some name := ascii? (← Reader.bytes nameLength.toNat) | throw "name"
    let templateLength ← Reader.compact
    let templateHash ← Reader.bytes 32
    let keyCount ← Reader.compact
    let keysRoot ← Reader.bytes 32
    return (name, templateLength.toNat, templateHash, keyCount.toNat, keysRoot)) serialized (exact := true)
  -- The app's wallet.h limits: a template of at most 512 bytes (read_wallet_policy_header refuses the
  -- header), at most 15 keys (register_wallet answers SW_NOT_SUPPORTED).
  unless templateLength ≤ 512 do fail 0x6A80
  unless keyCount ≤ 15 do fail 0x6A82
  let templateBytes ← preimage templateHash
  let some template := ascii? templateBytes | fail 0x6A80
  unless templateBytes.size == templateLength do fail 0x6A80
  let mut keys := #[]
  for index in [0:keyCount] do
    let some key := ascii? (← element keysRoot keyCount index) | fail 0x6A80
    keys := keys.push key
  return { name, template, keys }

/-- The template with each `@i/**` replaced by its key and `/<0;1>/*`. -/
def Policy.descriptorText (p : Policy) : String := Id.run do
  let mut text := p.template
  for index in (List.range p.keys.size).reverse do
    text := (text.replace s!"@{index}/**" (p.keys[index]! ++ "/<0;1>/*")).replace s!"@{index}/<" (p.keys[index]! ++ "/<")
  return text

def derive (master : HDKey) (path : Array UInt32) : H HDKey := do
  let mut key := master
  for step in path do
    match key.child step with
    | .ok k => key := k
    | .error _ => fail 0x6A80
  return key

def hmac (s : Simulator) (id : ByteArray) : ByteArray := hmacSha256 s.registrationKey id

/-- The app's rule for keys it exports without asking: BIP44/45/49/84/86/87 accounts and BIP48
script types 1' and 2', on the test coin. -/
def isStandard (path : Array UInt32) : Bool := Id.run do
  let hardened : UInt32 := 0x8000_0000
  if path.size < 3 then return false
  let purpose := path[0]! &&& ~~~hardened
  let hardenedSteps := if ([44, 45, 49, 84, 86, 87] : List UInt32).contains purpose then 3 else if purpose == 48 then 4 else 0
  if hardenedSteps == 0 then return false
  unless path.size ≥ hardenedSteps && (path.extract 0 hardenedSteps).all (· ≥ hardened)
      && (path.extract hardenedSteps path.size).all (· < hardened)
      && path[1]! &&& ~~~hardened == 1 && path[2]! &&& ~~~hardened ≤ 100 do return false
  return purpose != 48 || ([1, 2] : List UInt32).contains (path[3]! &&& ~~~hardened)

def sim : H Simulator := return (← get).1

def extendedPublicKey (body : ByteArray) : H ByteArray := do
  let (display, path) ← parse (do
    let display := (← Reader.u8) == 1
    let count ← Reader.u8
    if count > 8 then throw "deep"
    let mut path : Array UInt32 := #[]
    for _ in [0:count.toNat] do path := path.push (← readBE32)
    return (display, path)) body
  unless display || isStandard path do fail 0x6A82
  let s ← sim
  if display && s.decision == .reject then fail 0x6985
  return ((← derive s.master path).neutered.serialized .testnet).toUTF8

def register (body : ByteArray) : H ByteArray := do
  let serialized ← parse (do
    let length ← Reader.compact
    Reader.bytes length.toNat) body
  let p ← policy serialized
  let s ← sim
  unless s.decision == .approve do fail 0x6985
  modify fun (s, session) => ({ s with registeredNames := s.registeredNames.push p.name }, session)
  let id := sha256 serialized
  return id ++ s.hmac id

def address (body : ByteArray) : H ByteArray := do
  let (display, id, tag, change, index) ← parse (do
    let display := (← Reader.u8) == 1
    let id ← Reader.bytes 32
    let tag ← Reader.bytes 32
    let change ← Reader.u8
    let index ← readBE32
    return (display, id, tag, change, index)) body
  let s ← sim
  unless tag == s.hmac id && change ≤ 1 do fail 0xB008
  let p ← policy (← preimage id)
  let .ok d := Descriptor.parse p.descriptorText | fail 0x6A80
  let .ok outputs := d.derived index s.network | fail 0x6A80
  let some output := outputs[change.toNat]? | fail 0x6A80
  if display then
    unless s.decision == .approve do fail 0x6985
    modify fun (s, session) => ({ s with displayedAddresses := s.displayedAddresses.push output.address }, session)
  return output.address.toUTF8

def sign (body : ByteArray) : H ByteArray := do
  let (global, inputCount, inputsRoot, outputCount, outputsRoot, id, tag) ← parse (do
    let global ← readCommitment
    let inputCount ← Reader.compact
    let inputsRoot ← Reader.bytes 32
    let outputCount ← Reader.compact
    let outputsRoot ← Reader.bytes 32
    let id ← Reader.bytes 32
    let tag ← Reader.bytes 32
    return (global, inputCount.toNat, inputsRoot, outputCount.toNat, outputsRoot, id, tag)) body
  let s ← sim
  unless tag == s.hmac id do fail 0xB008
  let _ ← policy (← preimage id)
  let mut document := ByteArray.mk #[0x70, 0x73, 0x62, 0x74, 0xFF] ++ serializedMap (← map global)
  for index in [0:inputCount] do
    let c ← parse readCommitment (← element inputsRoot inputCount index)
    document := document ++ serializedMap (← map c)
  for index in [0:outputCount] do
    let c ← parse readCommitment (← element outputsRoot outputCount index)
    document := document ++ serializedMap (← map c)
  let .ok parsed := PSBT.parse document | fail 0x6A80
  let mut psbt := parsed
  unless s.decision == .approve do fail 0x6985
  for index in [0:psbt.inputs.size] do
    let mut ownKeys : Array ByteArray := #[]
    let mut secrets : Array ByteArray := #[]
    for (xonly, origin) in psbt.inputs[index]!.tapBIP32Derivation do
      if origin.masterFingerprint != s.master.fingerprint then continue
      let key ← derive s.master origin.path
      let some secret := key.privateKey | continue
      if key.publicKey.extract 1 key.publicKey.size != xonly then continue
      ownKeys := ownKeys.push xonly
      secrets := secrets.push secret
    if secrets.isEmpty then continue
    let .ok signed := psbt.signScriptPath index secrets (ByteArray.mk (Array.replicate 32 0)) | fail 0x6A80
    psbt := signed
    -- A fixed order: each replay must yield the same signature at the same step.
    let own := sortBytes (fun (id, _) => id.leafHash ++ id.publicKey)
      (psbt.inputs[index]!.tapScriptSignatures.filter fun (id, _) => ownKeys.contains id.publicKey)
    for (signer, signature) in own do
      let yielded := compactSize index.toUInt64 |>.push 64 |>.append signer.publicKey |>.append signer.leafHash
        |>.append signature
      let _ ← ask (ByteArray.mk #[0x10] ++ yielded)
  return .empty

def handle (apdu : ByteArray) : H ByteArray := do
  unless apdu[0]! == 0xE1 do fail 0x6E00
  unless apdu[3]! == 1 do fail 0x6A86
  let body := apdu.extract 5 apdu.size
  match apdu[1]! with
  | 0x05 => return u32BE (← sim).master.fingerprint
  | 0x00 => extendedPublicKey body
  | 0x02 => register body
  | 0x03 => address body
  | 0x04 => sign body
  | _ => fail 0x6D00

/-- `exchange(_:)`: one APDU in, the whole reply out (status word included), and the next state. -/
def exchange (s : Simulator) (apdu : ByteArray) : Simulator × ByteArray := Id.run do
  unless apdu.size ≥ 5 && apdu.size == 5 + apdu[4]!.toNat do return (s, statusBytes 0x6A87)
  let mut s := s
  if apdu[0]! == 0xF8 && apdu[1]! == 0x01 then
    if s.command.isNone then return (s, statusBytes 0x6D00)
    s := { s with answers := s.answers.push (apdu.extract 5 apdu.size) }
  else
    s := { s with command := some apdu, answers := #[] }
  let command := s.command.getD .empty
  match (handle command).run (s, { answers := s.answers }) with
  | .ok (reply, (s', _)) => return ({ s' with command := none }, reply ++ statusBytes 0x9000)
  | .error (.interrupt request) => return (s, request ++ statusBytes 0xE000)
  | .error (.failure status) => return ({ s with command := none }, statusBytes status)

/-- The simulator as a shared object (Swift's actor), for an `IO` transport. -/
def transport (ref : IO.Ref Simulator) (apdu : ByteArray) : IO ByteArray :=
  ref.modifyGet fun s => let (s', reply) := s.exchange apdu; (reply, s')

end Simulator
end Winnow.Ledger
