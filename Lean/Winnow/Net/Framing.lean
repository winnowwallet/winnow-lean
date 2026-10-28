import Winnow.Crypto
import Winnow.Net.Wire

/-! # P2P message framing (`Network/Protocol/Framing.swift`)

Header (24 bytes): magic(4) ‖ command(12, ASCII, zero-padded) ‖ length(4 LE) ‖ checksum(first 4 bytes
of SHA256d(payload)). The deframer is a value: `append` bytes, take complete messages with `nextMessage`. -/

namespace Winnow.Net

inductive FramingError where
  | badMagic
  | badCommand
  | payloadTooLarge (length : UInt32)
  | checksumMismatch (command : String)
  deriving Repr, BEq, Inhabited

def FramingError.name : FramingError → String
  | .badMagic => "badMagic"
  | .badCommand => "badCommand"
  | .payloadTooLarge _ => "payloadTooLarge"
  | .checksumMismatch _ => "checksumMismatch"

structure MessageFramer where
  magic : ByteArray
  buffer : ByteArray := .empty
  deriving Inhabited

namespace MessageFramer

def headerSize : Nat := 24
/-- MAX_PROTOCOL_MESSAGE_LENGTH in Bitcoin Core. -/
def maxPayloadSize : Nat := 4_000_000

def append (f : MessageFramer) (data : ByteArray) : MessageFramer := { f with buffer := f.buffer ++ data }
def bufferedCount (f : MessageFramer) : Nat := f.buffer.size

/-- The command bytes up to the first zero, accepted when non-empty and made only of non-whitespace
ASCII characters (Swift decodes them lossily, so any byte ≥ 0x80 fails; whitespace is U+0009–U+000D
and the space). -/
def commandOf (b : ByteArray) : Option String :=
  let bytes := (b.data.toList.takeWhile (· != 0))
  if bytes.isEmpty || bytes.any (fun c => c ≥ 0x80 || (0x09 ≤ c && c ≤ 0x0D) || c == 0x20) then none
  else some (String.ofList (bytes.map fun c => Char.ofNat c.toNat))

/-- The next complete message, `none` when more bytes are needed. -/
def nextMessage (f : MessageFramer) : Except FramingError (Option (String × ByteArray) × MessageFramer) := do
  let buf := f.buffer
  if buf.size < headerSize then return (none, f)
  if !(buf.extract 0 4 == f.magic) then throw .badMagic
  let some command := commandOf (buf.extract 4 16) | throw .badCommand
  let length := (readLE buf 16 4).toUInt32
  if length.toNat > maxPayloadSize then throw (.payloadTooLarge length)
  let total := headerSize + length.toNat
  if buf.size < total then return (none, f)
  let payload := buf.extract headerSize total
  if !((sha256d payload).extract 0 4 == buf.extract 20 24) then throw (.checksumMismatch command)
  return (some (command, payload), { f with buffer := buf.extract total buf.size })

/-- One framed message (the command is at most 12 bytes; Swift traps otherwise). -/
def frame (command : String) (payload magic : ByteArray) : ByteArray :=
  let c := command.toUTF8
  magic ++ c ++ ByteArray.mk (Array.replicate (12 - c.size) 0) ++ u32LE payload.size.toUInt32 ++
    (sha256d payload).extract 0 4 ++ payload

end MessageFramer
end Winnow.Net
