import Winnow.Ledger.ClientCommands
import Winnow.Keys.BIP32

/-! # The Ledger Bitcoin app client

Port of `Sources/WalletCore/Ledger/LedgerBitcoinClient.swift` (upstream 1cf93fb): Ledger's Bitcoin app
(version 2.1.2 or later), command by command. Every answer the device gives is checked where the
phone can check it; nothing is trusted because the device said it.

Swift's client is `async` over a `LedgerTransport`. Here every operation is a `Program`: a pure,
resumable description of the exchange, either finished (`done`/`fail`) or waiting for the reply to
one APDU (`exchange apdu next`). An Elm-style app keeps the `Program` in its model, writes `apdu`
(framed, `Ledger/Framing.lean`) to the device and feeds the reassembled reply to `next`;
`Program.run` drives it over any transport function instead (the tests, the simulator). -/

namespace Winnow.Ledger
open Keys

/-- A Ledger conversation in progress. -/
inductive Program (α : Type) where
  | done (value : α)
  | fail (error : LedgerError)
  /-- Send the serialized APDU `apdu`; the whole reply (status word included) goes to `next`. -/
  | exchange (apdu : ByteArray) (next : ByteArray → Program α)

namespace Program

instance {α} : Inhabited (Program α) := ⟨.fail (.transport "no program")⟩

def bind {α β} : Program α → (α → Program β) → Program β
  | .done a, f => f a
  | .fail e, _ => .fail e
  | .exchange apdu next, f => .exchange apdu fun reply => bind (next reply) f

instance : Monad Program where
  pure := .done
  bind := bind

def tryCatch {α} : Program α → (LedgerError → Program α) → Program α
  | .done a, _ => .done a
  | .fail e, h => h e
  | .exchange apdu next, h => .exchange apdu fun reply => tryCatch (next reply) h

instance : MonadExceptOf LedgerError Program where
  throw := .fail
  tryCatch := tryCatch

def ofExcept {α} : Except LedgerError α → Program α
  | .ok a => .done a
  | .error e => .fail e

/-- The APDU this program waits to send, if it waits for one. -/
def pending? {α} : Program α → Option ByteArray
  | .exchange apdu _ => some apdu
  | _ => none

/-- Feeds the reply to the pending APDU (a finished program stays as it is). -/
def feed {α} : Program α → ByteArray → Program α
  | .exchange _ next, reply => next reply
  | p, _ => p

/-- Runs the program over a transport: `exchange` carries one APDU to the device and returns its
whole reply, status word included. -/
def run {m : Type → Type} [Monad m] [MonadExceptOf LedgerError m] {α} (exchange : ByteArray → m ByteArray) :
    Program α → m α
  | .done a => pure a
  | .fail e => throw e
  | .exchange apdu next => do
    let reply ← exchange apdu
    run exchange (next reply)

/-- `run` over an `IO` transport (Bluetooth through the shell, `Simulator.transport`); the device's
and the protocol's failures come back as `LedgerError`s, the transport's own as `IO` errors. -/
def runIO {α} (exchange : ByteArray → IO ByteArray) (p : Program α) : ExceptT LedgerError IO α :=
  p.run fun apdu => ExceptT.lift (exchange apdu)

end Program

/-- A signature the device yielded while signing a PSBT (`LedgerSignature`). -/
structure Signature where
  inputIndex : Nat
  /-- 33-byte compressed (segwit v0), 32-byte x-only (key path or leaf). -/
  publicKey : ByteArray
  /-- Present for a script-path signature: the leaf it signs for. -/
  leafHash : Option ByteArray
  /-- 64 bytes, or 65 with a sighash byte. -/
  signature : ByteArray
  deriving Inhabited, BEq

namespace Client

/-- A real PSBT needs a few thousand rounds at most; a hostile or broken device could ask forever. -/
def maximumRounds : Nat := 100_000

/-- The rest of one command once `reply` has arrived: answers every interruption from the
interpreter, and returns the final data (and the interpreter, for its yields) on success. -/
def answer (fuel : Nat) (interpreter : Interpreter) (reply : ByteArray) : Program (ByteArray × Interpreter) :=
  match Response.parse reply with
  | .error e => .fail e
  | .ok response =>
    if response.status == Response.interrupted then
      match fuel with
      | 0 => .fail (.protocolViolation "a command that never finishes")
      | fuel + 1 =>
        match interpreter.execute response.data with
        | .error e => .fail e
        | .ok (interpreter, data) =>
          match (APDU.continueInterrupted data).serialized with
          | .error e => .fail e
          | .ok bytes => .exchange bytes (answer fuel interpreter)
    else if response.status == Response.ok then .done (response.data, interpreter)
    else .fail (LedgerError.ofStatus response.status)

/-- `request(_:interpreter:)`: sends `apdu`, answers every interruption from `interpreter`, and
returns the final data once the device reports success. -/
def requestWith (apdu : APDU) (interpreter : Interpreter) : Program (ByteArray × Interpreter) := do
  let bytes ← Program.ofExcept apdu.serialized
  .exchange bytes (answer maximumRounds interpreter)

def request (apdu : APDU) : Program ByteArray := do
  return (← requestWith apdu {}).1

/-- `String(data:encoding: .ascii)`: every byte below 0x80. -/
def ascii? (b : ByteArray) : Option String :=
  if b.data.all (· < 0x80) then String.fromUTF8? b else none

def masterFingerprint : Program UInt32 := do
  let data ← request (.bitcoin .getMasterFingerprint)
  unless data.size == 4 do throw (LedgerError.protocolViolation "a fingerprint that is not four bytes")
  return (readBE data 0 4).toUInt32

/-- The extended public key at `path`. Paths the app calls non-standard are only answered with
`display`, after the user confirms on the device. -/
def extendedPublicKey (path : Array UInt32) (display : Bool) : Program String := do
  unless path.size ≤ 8 do throw (LedgerError.protocolViolation "a path deeper than the app accepts")
  let mut data := ByteArray.mk #[if display then 1 else 0, path.size.toUInt8]
  for step in path do data := data ++ u32BE step
  let reply ← request (.bitcoin .getExtendedPublicKey data)
  let some text := ascii? reply | throw (LedgerError.protocolViolation "an extended key that does not parse")
  unless (HDKey.deserialize text).toOption.isSome do
    throw (LedgerError.protocolViolation "an extended key that does not parse")
  return text

/-- Registers `policy` after the user approves it on the device. The id the device returns must be
the policy's own. Returns (id, hmac). -/
def register (policy : WalletPolicy) : Program (ByteArray × ByteArray) := do
  let interpreter := policy.registerIn {}
  let serialized := policy.serialized
  let data := compactSize serialized.size.toUInt64 ++ serialized
  let (reply, _) ← requestWith (.bitcoin .registerWallet data) interpreter
  unless reply.size == 64 do throw (LedgerError.protocolViolation "a registration that is not 64 bytes")
  let id := reply.extract 0 32
  unless id == policy.id do throw (LedgerError.mismatch "the registered policy is not the one this phone sent")
  return (id, reply.extract 32 64)

/-- The address at (change, index), shown on the device when `display`. -/
def address (policy : WalletPolicy) (hmac : ByteArray) (change : Bool) (index : UInt32) (display : Bool) :
    Program String := do
  unless hmac.size == 32 do throw (LedgerError.protocolViolation "an HMAC that is not 32 bytes")
  let interpreter := policy.registerIn {}
  let data := ByteArray.mk #[if display then 1 else 0] ++ policy.id ++ hmac
    |>.push (if change then 1 else 0) |>.append (u32BE index)
  let (reply, _) ← requestWith (.bitcoin .getWalletAddress data) interpreter
  let some address := ascii? reply | throw (LedgerError.protocolViolation "an address that is not text")
  return address

/-- `signature(fromYield:inputCount:)`: decodes one yielded value. MuSig2 nonces and partial
signatures, and tags this client does not know, are skipped (`none`). -/
def signatureOfYield (value : ByteArray) (inputCount : Nat) : Except LedgerError (Option Signature) := do
  let parsed : Reader (Option (UInt64 × Nat × ByteArray × ByteArray)) := do
    let tag ← Reader.compact
    if tag ≥ 0x8000_0000 then return none
    if tag.toNat ≥ inputCount then return some (tag, 0, .empty, .empty)  -- refused below
    let keyLength := (← Reader.u8).toNat
    let augmented ← Reader.bytes keyLength
    let signature ← Reader.bytes (← Reader.remaining)
    return some (tag, keyLength, augmented, signature)
  match parsed.run value with
  | .error _ => throw (.protocolViolation "a malformed yielded signature")
  | .ok (none, _) => return none
  | .ok (some (tag, keyLength, augmented, signature), _) =>
    unless tag.toNat < inputCount do throw (.protocolViolation "a signature for an input that does not exist")
    unless signature.size == 64 || signature.size == 65 || (keyLength == 33 && 9 ≤ signature.size && signature.size ≤ 73) do
      throw (.protocolViolation "a signature of the wrong length")
    match keyLength with
    | 64 => return some { inputIndex := tag.toNat, publicKey := augmented.extract 0 32,
                          leafHash := some (augmented.extract 32 64), signature }
    | 32 | 33 => return some { inputIndex := tag.toNat, publicKey := augmented, leafHash := none, signature }
    | _ => throw (.protocolViolation "a signing key of the wrong length")

/-- Asks the device to sign every input it can, after the user reviews the payment on its screen;
returns the signatures it yields. -/
def signPSBT (psbt : PSBT) (policy : WalletPolicy) (hmac : ByteArray) : Program (Array Signature) := do
  unless psbt.version == some 2 do throw (LedgerError.protocolViolation "the app signs PSBTv2 only")
  unless hmac.size == 32 do throw (LedgerError.protocolViolation "an HMAC that is not 32 bytes")
  let mut interpreter := policy.registerIn {}
  interpreter := interpreter.addKnownMapping psbt.globals
  for input in psbt.inputs do interpreter := interpreter.addKnownMapping input.pairs
  for output in psbt.outputs do interpreter := interpreter.addKnownMapping output.pairs
  let inputCommitments := psbt.inputs.map (Merkle.mapCommitment ·.pairs)
  let outputCommitments := psbt.outputs.map (Merkle.mapCommitment ·.pairs)
  interpreter := (interpreter.addKnownList inputCommitments).addKnownList outputCommitments
  let data := Merkle.mapCommitment psbt.globals
    ++ compactSize psbt.inputs.size.toUInt64 ++ Merkle.root (inputCommitments.map Merkle.elementHash)
    ++ compactSize psbt.outputs.size.toUInt64 ++ Merkle.root (outputCommitments.map Merkle.elementHash)
    ++ policy.id ++ hmac
  let (_, finished) ← requestWith (.bitcoin .signPSBT data) interpreter
  let mut signatures : Array Signature := #[]
  for value in finished.yielded do
    if let some s ← Program.ofExcept (signatureOfYield value psbt.inputs.size) then signatures := signatures.push s
  return signatures

end Client
end Winnow.Ledger
