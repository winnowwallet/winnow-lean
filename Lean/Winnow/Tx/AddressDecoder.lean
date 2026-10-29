import Winnow.Crypto

/-! # AddressDecoder: standard addresses ↔ scriptPubKeys

Port of `Sources/WalletCore/Transactions/AddressDecoder.swift`: bech32/bech32m segwit (BIP173/350, incl.
P2TR) and Base58Check P2PKH/P2SH, with the network enforced.

`BitcoinNetwork` lives in `Network/Protocol/NetworkParams.swift` (another area); the Tx area carries its
own copy as `Winnow.Tx.BitcoinNetwork` until that one is ported. -/

namespace Winnow.Tx

inductive BitcoinNetwork where
  | mainnet | signet | regtest
  deriving Repr, BEq, Inhabited, DecidableEq

def BitcoinNetwork.allCases : List BitcoinNetwork := [.mainnet, .signet, .regtest]

def BitcoinNetwork.ofString? : String → Option BitcoinNetwork
  | "mainnet" => some .mainnet | "signet" => some .signet | "regtest" => some .regtest | _ => none

end Winnow.Tx

namespace Winnow
open Tx (BitcoinNetwork)

inductive AddressError where
  | invalidAddress (address : String)
  | wrongNetwork (address : String)
  | unsupportedWitnessVersion (version : Nat)
  | unsupportedWitnessProgram (version length : Nat)
  deriving Repr, BEq, Inhabited

def AddressError.name : AddressError → String
  | .invalidAddress _ => "invalidAddress" | .wrongNetwork _ => "wrongNetwork"
  | .unsupportedWitnessVersion _ => "unsupportedWitnessVersion"
  | .unsupportedWitnessProgram .. => "unsupportedWitnessProgram"

namespace AddressDecoder

/-- bech32 HRP per network (signet uses the testnet constants, BIP325). -/
def hrp : BitcoinNetwork → String
  | .mainnet => "bc" | .signet => "tb" | .regtest => "bcrt"

def asciiLower (s : String) : String := s.map fun c => if 'A' ≤ c ∧ c ≤ 'Z' then Char.ofNat (c.toNat + 32) else c

/-- Segwit: OP_n ‹program›; v0 bech32 with 20/32 bytes, v1 bech32m with 32 bytes; other versions refused. -/
def segwitScriptPubKey (address : String) (network : BitcoinNetwork) : Except AddressError ByteArray := do
  match SegwitAddress.decode address (some (hrp network)) with
  | .error _ => throw (.invalidAddress address)
  | .ok (version, program) =>
    if version == 1 && program.size != 32 then throw (.unsupportedWitnessProgram version program.size)
    if version ≥ 2 then throw (.unsupportedWitnessVersion version)
    return ByteArray.mk #[if version == 0 then 0x00 else (0x50 + version).toUInt8, program.size.toUInt8] ++ program

/-- Base58Check: 0x00/0x6F P2PKH, 0x05/0xC4 P2SH. -/
def base58ScriptPubKey (address : String) (network : BitcoinNetwork) : Except AddressError ByteArray := do
  match Base58Check.decode address with
  | .error _ => throw (.invalidAddress address)
  | .ok payload =>
    if payload.size != 21 then throw (.invalidAddress address)
    let hash := payload.extract 1 21
    let p2pkh : UInt8 := if network == .mainnet then 0x00 else 0x6F
    let p2sh : UInt8 := if network == .mainnet then 0x05 else 0xC4
    if payload[0]! == p2pkh then return ByteArray.mk #[0x76, 0xA9, 0x14] ++ hash ++ ByteArray.mk #[0x88, 0xAC]
    else if payload[0]! == p2sh then return ByteArray.mk #[0xA9, 0x14] ++ hash ++ ByteArray.mk #[0x87]
    else throw (.wrongNetwork address)

/-- Decodes an address to its output scriptPubKey, enforcing the network. -/
def scriptPubKey (address : String) (network : BitcoinNetwork) : Except AddressError ByteArray := do
  let lowered := asciiLower address
  if BitcoinNetwork.allCases.any fun n => lowered.startsWith (hrp n ++ "1") then
    unless lowered.startsWith (hrp network ++ "1") do throw (.wrongNetwork address)
    segwitScriptPubKey address network
  else base58ScriptPubKey address network

/-- Whether a scriptPubKey is P2TR (OP_1 ‹32 bytes›). -/
def isP2TR (spk : ByteArray) : Bool := spk.size == 34 && spk[0]! == 0x51 && spk[1]! == 0x20

/-- The standard address for a payment output, if Winnow can pay it. -/
def address (script : ByteArray) (network : BitcoinNetwork) : Option String :=
  let n := script.size
  if n == 25 && script[0]! == 0x76 && script[1]! == 0xa9 && script[2]! == 0x14 && script[23]! == 0x88 &&
      script[24]! == 0xac then
    some (Base58Check.encode (ByteArray.mk #[if network == .mainnet then 0x00 else 0x6f] ++ script.extract 3 23))
  else if n == 23 && script[0]! == 0xa9 && script[1]! == 0x14 && script[22]! == 0x87 then
    some (Base58Check.encode (ByteArray.mk #[if network == .mainnet then 0x05 else 0xc4] ++ script.extract 2 22))
  else if n ≥ 4 && script[1]!.toNat == n - 2 && (script[0]! == 0 || script[0]! == 0x51) then
    match SegwitAddress.encode (hrp network) (if script[0]! == 0 then 0 else 1) (script.extract 2 n) with
    | .ok addr =>
      match scriptPubKey addr network with
      | .ok s => if s == script then some addr else none
      | .error _ => none
    | .error _ => none
  else none

end AddressDecoder
end Winnow
