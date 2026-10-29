import Lean.Data.Json
import Winnow.Ledger
import WinnowApp.Real.Shell
import ElmLean.Native.Client.Bluetooth

/-! # A Ledger over the shell's Bluetooth: LedgerBluetooth.swift's transport

The shell offers generic Bluetooth LE (`ble.state`, `ble.connect`, `ble.subscribe`, `ble.write`,
`ble.read`, `ble.close`), asked through LeanNative's typed client (`ElmLean.Native.Client.Bluetooth`).
Everything Ledger-specific lives here and in `Winnow.Ledger`: the services and characteristics, the frame-size request, the
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

open ElmLean.Native in
/-- A Bluetooth request through `ask`; a failure as Swift's message (`failure` when the shell's answer
names no error). -/
private def ble (ask : Ask) (r : Client.Request α) (failure : String) : IO α := do
  match ← (callAsk ask r : IO _) with
  | .ok a => pure a
  | .error e => throw (transportError (if e.kind == .malformed then failure else bleFailure e.name))

open ElmLean.Native in
private def readValue (ask : Ask) (id notify : String) (timeout : Nat) : IO ByteArray :=
  ble ask (Client.Bluetooth.read id notify (some timeout)) "the Ledger sent a malformed frame"

open ElmLean.Native in
private def writeValue (ask : Ask) (id write : String) (bytes : ByteArray) : IO Unit :=
  ble ask (Client.Bluetooth.write id write bytes (timeout := some 15)) "a write to the Ledger failed"

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

open ElmLean.Native in
/-- The state's name, as `Bluetooth.readiness` reads it. -/
private def stateName : Client.Bluetooth.State → String
  | .poweredOn => "poweredOn" | .poweredOff => "poweredOff" | .unauthorized => "unauthorized"
  | .unsupported => "unsupported" | .resetting => "resetting" | .unknown => "unknown"

open ElmLean.Native in
/-- Waits for a usable Bluetooth state (15 s), as `readiness(for:)` decides. -/
private partial def awaitPoweredOn (ask : Ask) (tries : Nat) : IO Unit := do
  -- an answer of no known state is not yet a usable one: asked again
  let state := match ← (callAsk ask Client.Bluetooth.state : IO _) with
    | .ok st => stateName st
    | .error _ => "unknown"
  match Bluetooth.readiness state with
  | some (.ok ()) => pure ()
  | some (.error e) => throw (IO.userError e.description)
  | none =>
    if tries == 0 then throw (transportError "the Ledger did not answer in time")
    IO.sleep 250
    awaitPoweredOn ask (tries - 1)

open ElmLean.Native in
/-- `LedgerBluetoothTransport.open()`: connects to the first Ledger found, subscribes to its notify
characteristic (pairing on first use) and asks its frame size. -/
def openLedger (ask : Ask) : IO LedgerSession := do
  awaitPoweredOn ask 60
  let c ← ble ask (Client.Bluetooth.connect Bluetooth.serviceIdentifiers.toList (some 45)) "the Ledger refused the connection"
  let notify := Bluetooth.notifyCharacteristic c.service
  let write := Bluetooth.writeCharacteristic c.service
  let has (u : String) := c.characteristics.any (·.toUpper == u.toUpper)
  unless has notify && has write do
    throw (transportError "the Ledger service is missing its characteristics")
  let close : IO Unit := do discard <| (callAsk ask (Client.Bluetooth.close c.id) : IO _)
  try
    ble ask (Client.Bluetooth.subscribe c.id notify (some 90)) "pairing with the Ledger did not complete"
    writeValue ask c.id write BluetoothFraming.mtuRequest
    let size := Bluetooth.writeFrameSize (← readFrameSize ask c.id notify 8) none
    let exchange (apdu : ByteArray) : IO ByteArray := do
      let frames ← match BluetoothFraming.frames apdu size with
        | .ok fs => pure fs
        | .error e => throw (IO.userError e.description)
      for f in frames do writeValue ask c.id write f
      collectReply ask c.id notify {}
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
