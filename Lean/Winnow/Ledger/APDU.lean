import Winnow.Bytes

/-! # Ledger APDUs, replies and errors

Port of `Sources/WalletCore/Ledger/LedgerAPDU.swift` (the APDU and the reply) and of `LedgerError` from
`LedgerClientCommands.swift` (upstream 1cf93fb). The Bluetooth framing of the same Swift file is
`Winnow.Ledger.BluetoothFraming` (`Ledger/Framing.lean`). -/

namespace Winnow

/-- Why a Ledger exchange failed (`LedgerError`): each case names a step the user can act on, or a
protocol fault the phone refuses to work around. The strings are developer-written literals. -/
inductive LedgerError where
  /-- Bluetooth or framing failed: the device went away or sent malformed frames. -/
  | transport (reason : String)
  /-- The Ledger is locked; unlock it with its PIN. -/
  | deviceLocked
  /-- The Bitcoin app (Bitcoin Test on test networks) is not open on the Ledger. -/
  | appNotOpen
  /-- The user declined on the Ledger's screen. -/
  | rejectedOnDevice
  /-- Any other status word the device returned. -/
  | status (word : UInt16)
  /-- The device asked for data the phone never committed to, or answered in a shape the protocol
  does not allow. -/
  | protocolViolation (reason : String)
  /-- The device's answer disagrees with what the phone derives itself. -/
  | mismatch (reason : String)
  deriving Inhabited, BEq, Repr

namespace LedgerError

/-- The case name, as the lockstep convention prints errors. -/
def name : LedgerError → String
  | .transport _ => "transport" | .deviceLocked => "deviceLocked" | .appNotOpen => "appNotOpen"
  | .rejectedOnDevice => "rejectedOnDevice" | .status _ => "status"
  | .protocolViolation _ => "protocolViolation" | .mismatch _ => "mismatch"

/-- Four uppercase hex digits (`String(format: "%04X", word)`). -/
def hex4Upper (w : UInt16) : String :=
  let h := (String.ofList (Nat.toDigits 16 w.toNat)).toUpper
  String.ofList (List.replicate (4 - h.length) '0') ++ h

/-- `errorDescription`. -/
def description : LedgerError → String
  | .transport reason => s!"The Ledger connection failed: {reason}."
  | .deviceLocked => "The Ledger is locked. Unlock it with its PIN and try again."
  | .appNotOpen => "Open the Bitcoin app on the Ledger (Bitcoin Test on signet) and try again."
  | .rejectedOnDevice => "The request was declined on the Ledger."
  | .status word => s!"The Ledger refused the request (status {hex4Upper word})."
  | .protocolViolation reason => s!"The Ledger broke its protocol: {reason}."
  | .mismatch reason => s!"The Ledger disagrees with this phone: {reason}."

instance : ToString LedgerError := ⟨description⟩

/-- `from(status:)`: maps a non-success status word to the step the user can take. -/
def ofStatus (word : UInt16) : LedgerError :=
  match word with
  | 0x6985 => .rejectedOnDevice
  | 0x5515 => .deviceLocked
  -- Wrong or no app: the dashboard and other apps refuse the class or instruction, or report that
  -- no app is running.
  | 0x6E00 | 0x6E01 | 0x6D00 | 0x6D02 | 0x6511 => .appNotOpen
  | w => .status w

end LedgerError

namespace Ledger

/-- One command to a Ledger app (`LedgerAPDU`): class, instruction, two parameters and at most 255
bytes of data, as ISO 7816-4 short APDUs are. -/
structure APDU where
  cla : UInt8
  ins : UInt8
  p1 : UInt8 := 0
  p2 : UInt8 := 1
  data : ByteArray := .empty
  deriving Inhabited

namespace APDU

/-- The Bitcoin app's commands, and the framework's CONTINUE. -/
def bitcoinClass : UInt8 := 0xE1
def frameworkClass : UInt8 := 0xF8
/-- Protocol version 1 of the Bitcoin app, sent as P2 on every command. -/
def protocolVersion : UInt8 := 1

inductive Instruction where
  | getExtendedPublicKey | registerWallet | getWalletAddress | signPSBT | getMasterFingerprint
  deriving Inhabited, BEq, Repr

def Instruction.rawValue : Instruction → UInt8
  | .getExtendedPublicKey => 0x00 | .registerWallet => 0x02 | .getWalletAddress => 0x03
  | .signPSBT => 0x04 | .getMasterFingerprint => 0x05

def bitcoin (instruction : Instruction) (data : ByteArray := .empty) : APDU :=
  { cla := bitcoinClass, ins := instruction.rawValue, data }

/-- The answer to an interrupted command (status 0xE000). -/
def continueInterrupted (data : ByteArray) : APDU := { cla := frameworkClass, ins := 0x01, data }

def serialized (a : APDU) : Except LedgerError ByteArray := do
  unless a.data.size ≤ 255 do throw (.protocolViolation "a command longer than one APDU")
  return ByteArray.mk #[a.cla, a.ins, a.p1, a.p2, a.data.size.toUInt8] ++ a.data

end APDU

/-- A Ledger's reply (`LedgerResponse`): data followed by a two-byte status word. -/
structure Response where
  data : ByteArray
  status : UInt16
  deriving Inhabited

namespace Response

def ok : UInt16 := 0x9000
def interrupted : UInt16 := 0xE000

def parse (bytes : ByteArray) : Except LedgerError Response := do
  unless bytes.size ≥ 2 do throw (.transport "a reply shorter than its status word")
  let n := bytes.size
  return { data := bytes.extract 0 (n - 2), status := (bytes[n - 2]!.toUInt16 <<< 8) ||| bytes[n - 1]!.toUInt16 }

end Response
end Ledger
end Winnow
