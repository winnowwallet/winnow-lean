import Winnow.Ledger.APDU

/-! # Ledger's Bluetooth framing

Port of `LedgerBluetoothFraming` (`Sources/WalletCore/Ledger/LedgerAPDU.swift`, upstream 1cf93fb) and
of the pure parts of the app's `LedgerBluetoothTransport` (`Sources/WinnowApp/LedgerBluetooth.swift`):
the GATT service and characteristic identifiers, the frame size to write with, and the notification
router. The shell offers only generic Bluetooth (write a value, get notified values), so everything a
Ledger needs on top of that is here, pure.

Every frame starts with tag 0x05 and a big-endian sequence number; the first frame also carries the
APDU's big-endian length. Frames are at most the size the device reports in answer to the MTU
request. -/

namespace Winnow.Ledger
namespace BluetoothFraming

def tag : UInt8 := 0x05
/-- Asks the device for its frame size (written as is, not framed). -/
def mtuRequest : ByteArray := ByteArray.mk #[0x08, 0x00, 0x00, 0x00, 0x00]
/-- The frame size to use before the device has answered. -/
def defaultFrameSize : Nat := 20

/-- The frame size in a reply to `mtuRequest` (its sixth byte), or `none` for any other notification. -/
def frameSize? (response : ByteArray) : Option Nat :=
  if response.size ≥ 6 && response[0]! == 0x08 && response[5]! > 5 then some response[5]!.toNat else none

/-- `frames(for:frameSize:)`: one APDU as frames of at most `frameSize` bytes (an empty APDU is one
frame). -/
def frames (apdu : ByteArray) (frameSize : Nat) : Except LedgerError (Array ByteArray) := do
  unless frameSize > 5 && apdu.size ≤ 0xFFFF do throw (.transport "an unusable frame size")
  let mut out : Array ByteArray := #[]
  let mut offset := 0
  let mut sequence : Nat := 0
  -- Each frame after the first carries at least three bytes, so this many rounds always suffice.
  for _ in [0:apdu.size + 1] do
    let mut frame := ByteArray.mk #[tag, (sequence >>> 8).toUInt8, (sequence &&& 0xFF).toUInt8]
    if sequence == 0 then frame := frame ++ ByteArray.mk #[(apdu.size >>> 8).toUInt8, (apdu.size &&& 0xFF).toUInt8]
    let room := frameSize - frame.size
    let take := min room (apdu.size - offset)
    frame := frame ++ apdu.extract offset (offset + take)
    offset := offset + take
    out := out.push frame
    unless sequence < 0xFFFF do throw (.transport "an APDU too long to frame")
    sequence := sequence + 1
    if offset ≥ apdu.size then break
  return out

/-- Reassembles notifications into one reply. -/
structure Reassembler where
  expected : Option Nat := none
  buffer : ByteArray := .empty
  nextSequence : UInt16 := 0
  deriving Inhabited

/-- `receive(_:)`: feeds one notification; the new state, and the whole reply once it is complete
(the state is then fresh again). On an error the caller keeps its previous state, as Swift's
mutating function changes nothing before it throws. -/
def Reassembler.receive (r : Reassembler) (frame : ByteArray) : Except LedgerError (Reassembler × Option ByteArray) := do
  unless frame.size ≥ 3 && frame[0]! == tag do throw (.transport "a frame without the APDU tag")
  let sequence : UInt16 := (frame[1]!.toUInt16 <<< 8) ||| frame[2]!.toUInt16
  unless sequence == r.nextSequence do throw (.transport "a frame out of sequence")
  let mut payload := frame.extract 3 frame.size
  let mut expected := r.expected
  if sequence == 0 then
    unless frame.size ≥ 5 do throw (.transport "a first frame without a length")
    expected := some ((frame[3]!.toNat <<< 8) ||| frame[4]!.toNat)
    payload := frame.extract 5 frame.size
  let some want := expected | throw (.transport "a frame before the first")
  let buffer := r.buffer ++ payload
  let next : Reassembler := { expected, buffer, nextSequence := sequence + 1 }
  if buffer.size < want then return (next, none)
  return ({}, some (buffer.extract 0 want))

end BluetoothFraming

/-! ## The GATT side (`LedgerBluetoothTransport`'s pure parts) -/

namespace Bluetooth

/-- The services Nano X, Stax, Flex and Apex advertise. Each has a notify (…0001…), write (…0002…)
and write-without-response (…0003…) characteristic. -/
def serviceIdentifiers : Array String := #[
  "13D63400-2C97-0004-0000-4C6564676572",
  "13D63400-2C97-6004-0000-4C6564676572",
  "13D63400-2C97-3004-0000-4C6564676572",
  "13D63400-2C97-8004-0000-4C6564676572"]

/-- `characteristic(_:of:)`: the service UUID with `-0000-4C65` replaced by `-<kind>-4C65`, e.g.
kind `"0001"` (notify) or `"0002"` (write with response). -/
def characteristic (kind service : String) : String :=
  service.toUpper.replace "-0000-4C65" s!"-{kind}-4C65"

def notifyCharacteristic (service : String) : String := characteristic "0001" service
def writeCharacteristic (service : String) : String := characteristic "0002" service

/-- The frame size to write with: the device's (from the MTU reply), capped by the largest value
the phone may write with response. -/
def writeFrameSize (deviceFrameSize : Nat) (maximumWriteLength : Option Nat) : Nat :=
  min deviceFrameSize (maximumWriteLength.getD deviceFrameSize)

/-- The steps of a connection; the router only cares about the last two. -/
inductive Step where
  | poweredOn | connected | characteristics | notifying | frameSize | written | reply
  deriving Inhabited, BEq, Repr

/-- `NotificationRouter`: routes one notification to the step in flight — the frame-size reply while
asking for it, reassembled APDU replies while awaiting one, nothing otherwise. -/
structure NotificationRouter where
  reassembler : BluetoothFraming.Reassembler := {}
  deriving Inhabited

/-- `receive(_:during:)`: `none` while the step is still waiting; `some (.ok value)` when it
completes; `some (.error e)` on a framing fault. -/
def NotificationRouter.receive (r : NotificationRouter) (value : ByteArray) (step : Option Step) :
    NotificationRouter × Option (Except LedgerError ByteArray) :=
  match step with
  | some .frameSize => (r, if (BluetoothFraming.frameSize? value).isNone then none else some (.ok value))
  | some .reply =>
    match r.reassembler.receive value with
    | .ok (re, reply) => ({ reassembler := re }, reply.map .ok)
    | .error e => (r, some (.error e))
  | _ => (r, none)

/-- What a Bluetooth manager state means for a connection waiting to start (`readiness(for:)`):
`some (.ok ())` go ahead, `some (.error e)` the step the user can take, `none` keep waiting. The
states are CoreBluetooth's names. -/
def readiness (state : String) : Option (Except LedgerError Unit) :=
  match state with
  | "poweredOn" => some (.ok ())
  | "poweredOff" => some (.error (.transport "Bluetooth is off. Turn it on in Control Center"))
  | "unauthorized" => some (.error (.transport "Bluetooth access is off for Winnow. Turn it on in Settings"))
  | "unsupported" => some (.error (.transport "this device has no Bluetooth Low Energy"))
  | _ => none

end Bluetooth
end Winnow.Ledger
