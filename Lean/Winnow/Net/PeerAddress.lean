import Winnow.Net.Wire

/-! # Peer addresses (`Network/Protocol/PeerAddress.swift`): `CAddress` = services, 16-byte IP, port -/

namespace Winnow.Net

structure PeerAddress where
  /-- Present in `addr` records, absent in `version` messages. -/
  time : Option UInt32 := none
  services : UInt64
  /-- 16-byte IPv6 address; IPv4 peers use ::ffff:a.b.c.d. -/
  ip : ByteArray
  port : UInt16
  deriving Inhabited

namespace PeerAddress

instance : BEq PeerAddress := ⟨fun a b => a.time == b.time && a.services == b.services && a.ip == b.ip && a.port == b.port⟩

def ofIPv4 (time : Option UInt32) (services : UInt64) (a b c d : UInt8) (port : UInt16) : PeerAddress :=
  { time, services, ip := ByteArray.mk (Array.replicate 10 0 ++ #[0xFF, 0xFF, a, b, c, d]), port }

def unspecified : PeerAddress := { services := 0, ip := ByteArray.mk (Array.replicate 16 0), port := 0 }

/-- With or without the leading timestamp (`addr` vs `version`); the port is big-endian on the wire. -/
def serialized (a : PeerAddress) (includeTime : Bool) : ByteArray :=
  (if includeTime then u32LE (a.time.getD 0) else .empty) ++ u64LE a.services ++ a.ip ++
    ByteArray.mk #[(a.port >>> 8).toUInt8, a.port.toUInt8]

def read (includeTime : Bool) : Wire PeerAddress := do
  let time ← if includeTime then some <$> Wire.u32 else pure none
  let services ← Wire.u64
  let ip ← Wire.bytes 16
  let portLE ← Wire.u16
  return { time, services, ip, port := (portLE <<< 8) ||| (portLE >>> 8) }

def isIPv4Mapped (a : PeerAddress) : Bool :=
  (List.range 10).all (a.ip.get! · == 0) && a.ip.get! 10 == 0xFF && a.ip.get! 11 == 0xFF

private def hexGroup (g : Nat) : String := String.ofList (Nat.toDigits 16 g)

/-- Dotted quad for IPv4-mapped addresses, RFC 5952 canonical IPv6 otherwise (lowercase, the first
longest run of two or more zero groups collapsed). -/
def host (a : PeerAddress) : String := Id.run do
  let ip := a.ip
  if a.isIPv4Mapped then
    return s!"{ip.get! 12}.{ip.get! 13}.{ip.get! 14}.{ip.get! 15}"
  let groups := (List.range 8).map fun i => (ip.get! (2 * i)).toNat * 256 + (ip.get! (2 * i + 1)).toNat
  let gs := groups.toArray
  let mut best : Option (Nat × Nat) := none -- [lo, hi)
  let mut index := 0
  while index < 8 do
    if gs[index]! != 0 then index := index + 1
    else
      let mut stop := index
      while stop < 8 && gs[stop]! == 0 do stop := stop + 1
      let len := stop - index
      let bestLen := match best with | some (lo, hi) => hi - lo | none => 0
      if len ≥ 2 && len > bestLen then best := some (index, stop)
      index := stop
  match best with
  | none => return ":".intercalate (groups.map hexGroup)
  | some (lo, hi) =>
    return ":".intercalate ((groups.take lo).map hexGroup) ++ "::" ++ ":".intercalate ((groups.drop hi).map hexGroup)

/-- "host:port", IPv6 bracketed. -/
def endpointDescription (a : PeerAddress) : String :=
  if a.isIPv4Mapped then s!"{a.host}:{a.port}" else s!"[{a.host}]:{a.port}"

end PeerAddress
end Winnow.Net
