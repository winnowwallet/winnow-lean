import Winnow.Crypto
import Winnow.Net.Wire

/-! # Network parameters (`Network/Protocol/NetworkParams.swift`, `PeerEndpoint` of PeerConnection.swift)

Values from Bitcoin Core's chainparams.cpp (v28.0) as Winnow ships them; hashes in internal byte order. -/

namespace Winnow.Net

inductive BitcoinNetwork where
  | mainnet | signet | regtest
  deriving BEq, Inhabited, Repr, DecidableEq

def BitcoinNetwork.rawValue : BitcoinNetwork → String
  | .mainnet => "mainnet" | .signet => "signet" | .regtest => "regtest"

def BitcoinNetwork.ofRaw? : String → Option BitcoinNetwork
  | "mainnet" => some .mainnet | "signet" => some .signet | "regtest" => some .regtest | _ => none

/-- A peer's host/port. -/
structure PeerEndpoint where
  host : String
  port : UInt16
  deriving BEq, Inhabited, Repr, Hashable

def PeerEndpoint.description (e : PeerEndpoint) : String := s!"{e.host}:{e.port}"

/-- A trusted start for header sync: an 80-byte header and the big-endian chainwork through it. -/
structure Checkpoint where
  height : UInt32
  header : ByteArray
  chainwork : ByteArray
  deriving Inhabited

instance : BEq Checkpoint := ⟨fun a b => a.height == b.height && a.header == b.header && a.chainwork == b.chainwork⟩

structure NetworkParams where
  network : BitcoinNetwork
  magic : ByteArray
  defaultPort : UInt16
  genesisTime : UInt32
  genesisBits : UInt32
  genesisNonce : UInt32
  genesisMerkleRoot : ByteArray
  genesisHash : ByteArray
  powLimit : ByteArray
  dnsSeeds : Array String
  checkpoint : Option Checkpoint := none
  powTargetTimespan : UInt32 := 14 * 24 * 60 * 60
  powTargetSpacing : UInt32 := 600
  noRetargeting : Bool := false
  deriving Inhabited

namespace NetworkParams

def difficultyAdjustmentInterval (p : NetworkParams) : UInt32 := p.powTargetTimespan / p.powTargetSpacing

/-- The checks of Swift's `init` preconditions (a violation traps there). -/
def valid (p : NetworkParams) : Bool :=
  p.powTargetTimespan ≥ 4 && p.powTargetTimespan ≤ 0xFFFFFFFF / 4 &&
  p.powTargetSpacing > 0 && p.powTargetTimespan % p.powTargetSpacing == 0 &&
  (match p.checkpoint with | some c => c.header.size == 80 && c.chainwork.size == 32 | none => true)

/-- The default BIP325 signet challenge (2-of-2 multisig script). -/
def signetChallenge : ByteArray := ofHex!
  "512103ad5e0edad18cb1f0fc0d28a3d4f1f3e445640337489abb10404f2d1e086be430210359ef5021964fe22d6f8e05b2463c9540ce96883fe3b278760f048f5189f2e6c452ae"

/-- BIP325 magic: the first 4 bytes of SHA256d(compactSize(len) ‖ challenge). -/
def signetMagic (challenge : ByteArray) : ByteArray := (sha256d (varBytes challenge)).extract 0 4

/-- Mainnet genesis merkle root (display 4a5e1e4b…deda33b), internal order. -/
def mainnetGenesisMerkleRoot : ByteArray := ofDisplayHex! "4a5e1e4baab89f3a32518a88c31bc87f618f76673e2cc77ab2127b7afdeda33b"

def mainnet : NetworkParams := {
  network := .mainnet
  magic := ofHex! "f9beb4d9"
  defaultPort := 8333
  genesisTime := 1_231_006_505
  genesisBits := 0x1D00FFFF
  genesisNonce := 2_083_236_893
  genesisMerkleRoot := mainnetGenesisMerkleRoot
  genesisHash := ofDisplayHex! "000000000019d6689c085ae165831e934ff763ae46a2a6c172b3f1b60a8ce26f"
  powLimit := ofDisplayHex! "00000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffff"
  dnsSeeds := #["seed.bitcoin.sipa.be", "dnsseed.bluematt.me", "dnsseed.bitcoin.dashjr-list-of-p2p-nodes.us",
    "seed.bitcoin.jonasschnelli.ch", "seed.btc.petertodd.net", "seed.bitcoin.sprovoost.nl", "dnsseed.emzy.de",
    "seed.bitcoin.wiz.biz", "seed.mainnet.achownodes.xyz"]
  -- Block 959,616 (a difficulty-period boundary, 476 × 2016), derived from a genesis sync.
  checkpoint := some {
    height := 959_616
    header := ofHex! ("0000a03d32cf5172fa1b0614ac95b2bd9e965e644866cfc3f71701000000000000000000"
      ++ "723f3173aa33f0644ab1294973f345eb428455c7d0fd7f50bc4252c1c7300d3f" ++ "da3d656ad43a02170a17b1ae")
    chainwork := ofHex! "00000000000000000000000000000000000000013a74dc6d1ab305ff3e4295d7" }
}

def regtest : NetworkParams := {
  network := .regtest
  magic := ofHex! "fabfb5da"
  defaultPort := 18_444
  genesisTime := 1_296_688_602
  genesisBits := 0x207FFFFF
  genesisNonce := 2
  genesisMerkleRoot := mainnetGenesisMerkleRoot
  genesisHash := ofDisplayHex! "0f9188f13cb7b2c71f2a335e3a4fc328bf5beb436012afca590b1a11466e2206"
  powLimit := ofDisplayHex! "7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff"
  dnsSeeds := #[]
  noRetargeting := true
}

def signet : NetworkParams := {
  network := .signet
  magic := ofHex! "0a03cf40"
  defaultPort := 38333
  genesisTime := 1_598_918_400
  genesisBits := 0x1E0377AE
  genesisNonce := 52_613_770
  genesisMerkleRoot := mainnetGenesisMerkleRoot
  genesisHash := ofDisplayHex! "00000008819873e925422c1ff0f99f7cc9bbb232af63a077a480a3633bee1ef6"
  powLimit := ofDisplayHex! "00000377ae000000000000000000000000000000000000000000000000000000"
  dnsSeeds := #["seed.signet.bitcoin.sprovoost.nl", "seed.signet.achownodes.xyz"]
}

def params (n : BitcoinNetwork) : NetworkParams :=
  match n with
  | .mainnet => mainnet
  | .signet => signet
  | .regtest => regtest

/-- A custom BIP325 signet: the default signet's consensus fields under the challenge's magic.
(Swift traps on an empty challenge; `none` here.) -/
def customSignet (challenge : ByteArray) (defaultPort : UInt16 := 38_333) : Option NetworkParams :=
  if challenge.size == 0 then none
  else some { network := .signet, magic := signetMagic challenge, defaultPort,
              genesisTime := signet.genesisTime, genesisBits := signet.genesisBits,
              genesisNonce := signet.genesisNonce, genesisMerkleRoot := signet.genesisMerkleRoot,
              genesisHash := signet.genesisHash, powLimit := signet.powLimit, dnsSeeds := #[] }

def isCustomSignet (p : NetworkParams) : Bool := p.network == .signet && !(p.magic == signet.magic)
def allowsPrivateSeedAddresses (p : NetworkParams) : Bool := p.isCustomSignet

end NetworkParams
end Winnow.Net
