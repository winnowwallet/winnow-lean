import WinnowApp.Backend

/-! A UI harness (like Winnow's DEBUG-only E2EMode): `Backend.pending` with a wallet that "opens" and
fixed sample records, so every screen can be reached in the simulator before the Lean wallet is wired
in. Selected only by the `WINNOW_LEAN_SAMPLE=1` launch environment; every operation that would touch a
wallet still fails with "still being ported". The data is made up (signet-style addresses). -/

namespace WinnowApp

def sampleAlice : Person :=
  { id := "p-alice", name := "Alice", payTo := some true, nextPaymentIndex := 3, savedRecipient := some true }
def sampleBob : Person :=
  { id := "p-bob", name := "Bob", payTo := some false, savedRecipient := some true, provenance := some .localFunding }
def sampleCarol : Person :=
  { id := "p-carol", name := "Carol" }

def sampleHistory : List HistoryItem :=
  [ { txid := "c0ffee0000000000000000000000000000000000000000000000000000000003", height := 0,
      received := 0, spent := 12000, fee := some 300 }
  , { txid := "b0b0000000000000000000000000000000000000000000000000000000000002", height := 214010,
      received := 30000, spent := 80000, fee := some 450,
      outputs := some [ { index := 0, address := some "tb1qbobsample000000000000000000000000000", script := "0014b0b", amount := 49550, ownedByWallet := false }
                      , { index := 1, address := some "tb1pchange000000000000000000000000000000000000000000000000", script := "5120c4a", amount := 30000, ownedByWallet := true } ] }
  , { txid := "a11ce00000000000000000000000000000000000000000000000000000000001", height := 213990,
      received := 13_852_000, spent := 0, fee := none,
      outputs := some [ { index := 0, address := some "tb1preceive00000000000000000000000000000000000000000000000", script := "5120ab1", amount := 13_852_000, ownedByWallet := true } ],
      fundingAddresses := ["tb1qalicefunding0000000000000000000000000"] } ]

/-- The Nano X `WINNOW_LEAN_SAMPLE_LEDGER=1` has advertising nearby. -/
def sampleNearbyLedger : NearbyLedger := { id := "sample-nano-x", name := "Nano X 7C4E", rssi := some (-58) }

/-- The sample's wallet holds 0.138 BTC: above `hardwareWalletThresholdSats`, so the home suggests a Ledger. -/
def Backend.sample : Backend :=
  { Backend.pending with
    openWallet := fun _ _ => pure (.opened "sample-wallet")
    snapshot := pure ({ balance := 13_790_000, utxoCount := 2, history := sampleHistory, feeBumpable := [sampleHistory[0]!.txid],
                        peerCount := 0, tipHeight := 214020, nextScanHeight := 214021, feeFloorMilli := some 1000 }, .peerDiscoveryFailed)
    records := pure { people := [sampleAlice, sampleBob, sampleCarol],
                      senderByTxid := [(sampleHistory[2]!.txid, "p-alice")],
                      recipientByScript := [("0014b0b", "p-bob")],
                      receiveLabels := [("tb1preceive00000000000000000000000000000000000000000000000", "Alice · invoice 12")] } }

end WinnowApp
