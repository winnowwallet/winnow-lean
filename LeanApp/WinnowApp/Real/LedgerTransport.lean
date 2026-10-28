import Lean.Data.Json
import Winnow.Ledger
import WinnowApp.Real.Shell

/-! # A Ledger over the shell's Bluetooth: LedgerBluetooth.swift's transport

The shell offers generic Bluetooth LE (framework/lean/ElmShell/Capabilities.lean: `ble.state`,
`ble.connect`, `ble.subscribe`, `ble.write`, `ble.read`, `ble.close`). Everything Ledger-specific
lives here and in `Winnow.Ledger`: the services and characteristics, the frame-size request, the
0x05 framing and reassembly. The steps and their timeouts are Swift's: power on 15 s, connect 45 s,
characteristics 20 s (inside the shell's connect), notifications 90 s (pairing happens here), frame
size 15 s, each write 15 s, the reply 600 s (the person confirms on the Ledger's screen). Failures
carry Swift's texts.

One difference: the shell does not report the peripheral's largest write with response, so frames
are written at the device's own frame size (`writeFrameSize size none`). Swift caps it by that
limit, which is larger than a Ledger's frame size in practice. -/

namespace WinnowApp.Real
open Lean Winnow Winnow.Ledger

/-- One open connection: `exchange` sends an APDU and returns the reassembled reply. -/
structure LedgerSession where
  exchange : ByteArray → IO ByteArray
  close : IO Unit

private def askNow (ask : Ask) (name : String) (args : Json) : IO Json := do
  IO.wait (← ask name args)

private def transportError (reason : String) : IO.Error :=
  IO.userError (LedgerError.transport reason).description

/-- The shell's error codes as Swift's messages. -/
def bleFailure (code : String) : String :=
  match code with
  | "timeout" => "the Ledger did not answer in time"
  | "refused" => "the Ledger refused the connection"
  | "disconnected" => "the Ledger disconnected"
  | "no-service" => "the device offers no Ledger service"
  | "busy" => "another Ledger request is still running"
  | other =>
    match Bluetooth.readiness other with
    | some (.error e) => match e with
      | .transport reason => reason
      | e => e.description
    | _ => "a write to the Ledger failed"

private def check (r : Json) (failure : String) : IO Unit := do
  unless (r.getObjValAs? Bool "ok").toOption.getD false do
    let code := (r.getObjValAs? String "error").toOption.getD ""
    throw (transportError (if code.isEmpty then failure else bleFailure code))

private def readValue (ask : Ask) (id notify : String) (timeout : Nat) : IO ByteArray := do
  let r ← askNow ask "ble.read"
    (Json.mkObj [("id", .str id), ("characteristic", .str notify), ("timeout", toJson timeout)])
  match r.getObjValAs? String "hex" with
  | .ok h => match ofHex? h with
    | some bytes => pure bytes
    | none => throw (transportError "the Ledger sent a malformed frame")
  | .error _ => throw (transportError (bleFailure ((r.getObjValAs? String "error").toOption.getD "timeout")))

private def writeValue (ask : Ask) (id write : String) (bytes : ByteArray) : IO Unit := do
  let r ← askNow ask "ble.write" (Json.mkObj [("id", .str id), ("characteristic", .str write),
    ("hex", .str (hex bytes)), ("response", .bool true), ("timeout", toJson (15 : Nat))])
  check r "a write to the Ledger failed"

/-- The frame-size reply to the MTU request; other notifications before it are not its reply. -/
private partial def readFrameSize (ask : Ask) (id notify : String) (tries : Nat) : IO Nat := do
  let value ← readValue ask id notify 15
  match BluetoothFraming.frameSize? value with
  | some size => pure size
  | none =>
    if tries == 0 then throw (transportError "the Ledger did not answer in time")
    readFrameSize ask id notify (tries - 1)

/-- Reassembles one notified reply (600 s per frame: the person confirms on the device). -/
private partial def collectReply (ask : Ask) (id notify : String) (router : Bluetooth.NotificationRouter) :
    IO ByteArray := do
  let value ← readValue ask id notify 600
  match router.receive value (some .reply) with
  | (_, some (.ok reply)) => pure reply
  | (_, some (.error e)) => throw (IO.userError e.description)
  | (r, none) => collectReply ask id notify r

/-- Waits for a usable Bluetooth state (15 s), as `readiness(for:)` decides. -/
private partial def awaitPoweredOn (ask : Ask) (tries : Nat) : IO Unit := do
  let r ← askNow ask "ble.state" (Json.mkObj [])
  let state := (r.getObjValAs? String "state").toOption.getD "unknown"
  match Bluetooth.readiness state with
  | some (.ok ()) => pure ()
  | some (.error e) => throw (IO.userError e.description)
  | none =>
    if tries == 0 then throw (transportError "the Ledger did not answer in time")
    IO.sleep 250
    awaitPoweredOn ask (tries - 1)

/-- `LedgerBluetoothTransport.open()`: connects to the first Ledger found, subscribes to its notify
characteristic (pairing on first use) and asks its frame size. -/
def openLedger (ask : Ask) : IO LedgerSession := do
  awaitPoweredOn ask 60
  let c ← askNow ask "ble.connect" (Json.mkObj [("services", toJson Bluetooth.serviceIdentifiers),
    ("timeout", toJson (45 : Nat))])
  check c "the Ledger refused the connection"
  let some id := (c.getObjValAs? String "id").toOption
    | throw (transportError "the Ledger refused the connection")
  let some service := (c.getObjValAs? String "service").toOption
    | throw (transportError "the device offers no Ledger service")
  let notify := Bluetooth.notifyCharacteristic service
  let write := Bluetooth.writeCharacteristic service
  let chars := (c.getObjValAs? (Array String) "characteristics").toOption.getD #[]
  let has (u : String) := chars.any (·.toUpper == u.toUpper)
  unless has notify && has write do
    throw (transportError "the Ledger service is missing its characteristics")
  let close : IO Unit := do discard <| askNow ask "ble.close" (Json.mkObj [("id", .str id)])
  try
    check (← askNow ask "ble.subscribe" (Json.mkObj [("id", .str id), ("characteristic", .str notify),
      ("timeout", toJson (90 : Nat))])) "pairing with the Ledger did not complete"
    writeValue ask id write BluetoothFraming.mtuRequest
    let size := Bluetooth.writeFrameSize (← readFrameSize ask id notify 8) none
    let exchange (apdu : ByteArray) : IO ByteArray := do
      let frames ← match BluetoothFraming.frames apdu size with
        | .ok fs => pure fs
        | .error e => throw (IO.userError e.description)
      for f in frames do writeValue ask id write f
      collectReply ask id notify {}
    return { exchange, close }
  catch e =>
    close
    throw e

/-- Runs one Ledger operation on a fresh connection, closing it afterwards (Swift opens a connection
per operation). -/
def withLedger {α} (open_ : IO LedgerSession) (p : Program α) : IO (Except LedgerError α) := do
  let session ← open_
  try
    (Program.runIO session.exchange p).run
  finally
    session.close

/-- Test mode's Ledger: the simulator from `Winnow.Ledger`, one per app run. -/
def simulatedLedger (device : IO.Ref Simulator) : IO LedgerSession :=
  pure { exchange := Simulator.transport device, close := pure () }

end WinnowApp.Real
