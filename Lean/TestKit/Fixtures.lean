import Winnow.Keys
import Winnow.Wallet.Descriptor
import Winnow.Wallet.MultisigAccount
import Winnow.Wallet.Wallet
import TestKit.Check

/-! # The keys the tests share

Upstream's `Tests/Support/TestKeys.swift`: HD masters from BIP39 over 16 repeated bytes (0xA1, 0xB2, 0xC3 the
usual three signers), their Taproot account keys at m/86'/1'/0' and those as descriptor key expressions; the
zero BIP340 auxiliary randomness and the outside destination the multisig and Ledger tests spend to; how a test
shows a multisig or wallet failure. -/

namespace TestKit
open Winnow Winnow.Keys

initialize masterCache : IO.Ref (Array (UInt8 × HDKey)) ← IO.mkRef #[]

/-- `TestKeys.master(entropyByte:)`. A BIP39 seed takes 2048 PBKDF2 rounds, so each master is made once. -/
def master {n} [MonadLiftT IO n] (entropyByte : UInt8) : n HDKey := liftM (m := IO) do
  if let some (_, m) := (← masterCache.get).find? (·.1 == entropyByte) then return m
  let words ← needE "mnemonic" (fun _ => "bip39") (BIP39.mnemonic (ByteArray.mk (Array.replicate 16 entropyByte)))
  let m ← needE "master" (·.name) (HDKey.ofSeed (BIP39.seed words))
  masterCache.modify (·.push (entropyByte, m))
  return m

/-- The three signers: 0xA1, 0xB2, 0xC3. -/
def masters {n} [MonadLiftT IO n] : n (Array HDKey) := liftM (m := IO) (#[0xA1, 0xB2, 0xC3].mapM master)

/-- The master's Taproot account key, m/86'/1'/0'. -/
def accountKey {n} [MonadLiftT IO n] (m : HDKey) : n HDKey := needE "account key" (·.name) (m.derived "m/86'/1'/0'")

/-- `[fingerprint/86'/1'/0']tpub…` -/
def bareKeyExpression {n} [MonadLiftT IO n] (m : HDKey) : n String := liftM (m := IO) do
  return s!"[{Descriptor.hex8 m.fingerprint}/86'/1'/0']{(← accountKey m).neutered.serialized .testnet}"

/-- `[fingerprint/86'/1'/0']tpub…/<0;1>/*`, a signer of a multisig account. -/
def keyExpression {n} [MonadLiftT IO n] (m : HDKey) : n String :=
  liftM (m := IO) do return (← bareKeyExpression m) ++ "/<0;1>/*"

/-- BIP340 auxiliary randomness: zero. -/
def aux0 : ByteArray := ByteArray.mk (Array.replicate 32 0)

/-- A P2TR output to a key no test holds. -/
def destination : ByteArray := ByteArray.mk (#[0x51, 0x20] ++ Array.replicate 32 0x77)

instance : Describe MultisigFailure where
  name e := e.name
  describe e := s!"{e.name}{match e with | .account a => " (" ++ a.description ++ ")" | _ => ""}"

instance : Describe WalletFailure := ⟨(·.name), (·.name)⟩

end TestKit
