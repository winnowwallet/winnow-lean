import Lean.Data.Json
import Winnow.Ledger
import WinnowApp.Real.LedgerTransport
import TestKit.Check
import TestKit.Fixtures

/-! `ledger-transport-test`: the app's Ledger transport (`WinnowApp.Real.LedgerTransport`) against a
fake Bluetooth peripheral that speaks the shell's `ble.*` capabilities. The peripheral is the Lean
Ledger simulator behind real framing: it answers the frame-size request, reassembles the 0x05 frames
it is written, hands each APDU to the simulator and notifies the framed reply. The transport must give
the same answers as the simulator called directly, at a small frame size (many frames per APDU) and a
real one, and report Swift's messages for each failure. -/

open Lean Winnow Winnow.Keys Winnow.Ledger WinnowApp.Real TestKit

/-- What the fake peripheral does differently, to exercise each failure. -/
inductive Fault where
  | none | poweredOff | refused | missingCharacteristic | silentAfterSubscribe
  deriving BEq

structure Peripheral where
  notifications : Array ByteArray := #[]
  device : BluetoothFraming.Reassembler := {}
  closed : Nat := 0
  apdus : Nat := 0

def fakeAsk (state : IO.Ref Peripheral) (sim : IO.Ref Simulator) (frameSize : Nat) (fault : Fault) : Ask :=
  fun name args => do
    let service := Bluetooth.serviceIdentifiers[0]!
    let notify := Bluetooth.notifyCharacteristic service
    let write := Bluetooth.writeCharacteristic service
    let answer : Json ← match name with
      | "ble.state" => pure (Json.mkObj [("state", .str (if fault == .poweredOff then "poweredOff" else "poweredOn"))])
      | "ble.connect" =>
        if fault == .refused then pure (Json.mkObj [("ok", .bool false), ("error", .str "refused")])
        else
          let chars := if fault == .missingCharacteristic then #[notify] else #[notify, write]
          pure (Json.mkObj [("ok", .bool true), ("id", .str "p1"), ("service", .str service),
            ("characteristics", toJson chars)])
      | "ble.subscribe" => pure (Json.mkObj [("ok", .bool true)])
      | "ble.write" =>
        let bytes := (ofHex? ((args.getObjValAs? String "hex").toOption.getD "")).getD .empty
        if fault == .silentAfterSubscribe then pure (Json.mkObj [("ok", .bool true)])
        else if bytes == BluetoothFraming.mtuRequest then
          let reply := ByteArray.mk #[0x08, 0, 0, 0, 0, frameSize.toUInt8]
          state.modify fun p => { p with notifications := p.notifications.push reply }
          pure (Json.mkObj [("ok", .bool true)])
        else
          let p ← state.get
          match p.device.receive bytes with
          | .error _ => pure (Json.mkObj [("ok", .bool false), ("error", .str "bad-hex")])
          | .ok (device, none) =>
            state.set { p with device }
            pure (Json.mkObj [("ok", .bool true)])
          | .ok (device, some apdu) =>
            let reply ← Simulator.transport sim apdu
            match BluetoothFraming.frames reply frameSize with
            | .ok frames => state.set { p with device, notifications := p.notifications ++ frames, apdus := p.apdus + 1 }
            | .error _ => state.set { p with device }
            pure (Json.mkObj [("ok", .bool true)])
      | "ble.read" =>
        let p ← state.get
        if h : 0 < p.notifications.size then
          state.set { p with notifications := p.notifications.extract 1 p.notifications.size }
          pure (Json.mkObj [("hex", .str (hex p.notifications[0]))])
        else pure (Json.mkObj [("error", .str "timeout")])
      | "ble.close" =>
        state.modify fun p => { p with closed := p.closed + 1 }
        pure (Json.mkObj [("ok", .bool true)])
      | _ => pure (Json.mkObj [("error", .str s!"unknown capability {name}")])
    pure (Task.pure answer)

def main : IO UInt32 := runMain "ledger-transport-test" do
  let device ← master 0xB2
  -- the same answers over Bluetooth as from the simulator directly, at two frame sizes
  let direct ← (Program.runIO (Simulator.transport (← IO.mkRef (Simulator.new device)))
    (Multisig.signerExpression .signet)).run
  let directFp ← (Program.runIO (Simulator.transport (← IO.mkRef (Simulator.new device))) Client.masterFingerprint).run
  for size in [23, 153] do
    let state ← IO.mkRef ({} : Peripheral)
    let sim ← IO.mkRef (Simulator.new device)
    let ask := fakeAsk state sim size .none
    let r ← withLedger (openLedger ask) (Multisig.signerExpression .signet)
    check s!"signer expression over Bluetooth, frame size {size}" (match r, direct with
      | .ok a, .ok b => a == b | _, _ => false)
    let fp ← withLedger (openLedger ask) Client.masterFingerprint
    check s!"fingerprint over Bluetooth, frame size {size}" (match fp, directFp with
      | .ok a, .ok b => a == b && a == device.fingerprint | _, _ => false)
    let p ← state.get
    check s!"closed after each operation, frame size {size}" (p.closed == 2)
    check s!"every APDU answered, frame size {size}" (p.apdus > 0 && p.notifications.isEmpty)
  -- failures carry Swift's messages
  let expectFailure (fault : Fault) (message : String) : IO Unit := do
    let state ← IO.mkRef ({} : Peripheral)
    let sim ← IO.mkRef (Simulator.new device)
    let r ← (try
        let _ ← withLedger (openLedger (fakeAsk state sim 153 fault)) Client.masterFingerprint
        pure none
      catch e => pure (some (toString e)))
    check s!"failure {message}" (match r with
      | some text => (text.splitOn message).length > 1 | none => false)
  expectFailure .poweredOff "Bluetooth is off"
  expectFailure .refused "the Ledger refused the connection"
  expectFailure .missingCharacteristic "the Ledger service is missing its characteristics"
  expectFailure .silentAfterSubscribe "the Ledger did not answer in time"
  -- a failed open closes the connection it made
  let state ← IO.mkRef ({} : Peripheral)
  let sim ← IO.mkRef (Simulator.new device)
  let _ ← (try (some <$> withLedger (openLedger (fakeAsk state sim 153 .silentAfterSubscribe)) Client.masterFingerprint)
    catch _ => pure none)
  check "a failed open closes the connection" ((← state.get).closed == 1)
