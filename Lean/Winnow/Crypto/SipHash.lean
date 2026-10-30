import Winnow.Bytes

/-! # SipHash-2-4 (BIP158 uses it to hash filter elements) -/

namespace Winnow

@[inline] private def rotl64 (x : UInt64) (b : UInt64) : UInt64 := (x <<< b) ||| (x >>> (64 - b))

def sipHash (k0 k1 : UInt64) (data : ByteArray) : UInt64 := Id.run do
  let mut v0 : UInt64 := 0x736f6d6570736575 ^^^ k0
  let mut v1 : UInt64 := 0x646f72616e646f6d ^^^ k1
  let mut v2 : UInt64 := 0x6c7967656e657261 ^^^ k0
  let mut v3 : UInt64 := 0x7465646279746573 ^^^ k1
  let n := data.size
  let mut off := 0
  let mut last : UInt64 := (n.toUInt64 &&& 0xff) <<< 56
  let mut done := false
  while !done do
    let m : UInt64 :=
      if off + 8 ≤ n then readLE data off 8
      else Id.run do
        let mut l := last
        for i in [off:n] do l := l ||| ((data.get! i).toUInt64 <<< (8 * (i - off)).toUInt64)
        return l
    if off + 8 > n then done := true
    v3 := v3 ^^^ m
    for _ in [0:2] do
      v0 := v0 + v1; v1 := rotl64 v1 13; v1 := v1 ^^^ v0; v0 := rotl64 v0 32
      v2 := v2 + v3; v3 := rotl64 v3 16; v3 := v3 ^^^ v2
      v0 := v0 + v3; v3 := rotl64 v3 21; v3 := v3 ^^^ v0
      v2 := v2 + v1; v1 := rotl64 v1 17; v1 := v1 ^^^ v2; v2 := rotl64 v2 32
    v0 := v0 ^^^ m
    off := off + 8
  v2 := v2 ^^^ 0xff
  for _ in [0:4] do
    v0 := v0 + v1; v1 := rotl64 v1 13; v1 := v1 ^^^ v0; v0 := rotl64 v0 32
    v2 := v2 + v3; v3 := rotl64 v3 16; v3 := v3 ^^^ v2
    v0 := v0 + v3; v3 := rotl64 v3 21; v3 := v3 ^^^ v0
    v2 := v2 + v1; v1 := rotl64 v1 17; v1 := v1 ^^^ v2; v2 := rotl64 v2 32
  return v0 ^^^ v1 ^^^ v2 ^^^ v3

end Winnow
