/-! # UTF8: Swift's lossy UTF-8 decoding

`String(decoding: bytes, as: UTF8.self)` in one place, with no imports, so that the wire reader (Tx) and
the key and records files (Keys, the app) share it without pulling in Keys/Unicode's tables.

Exercised by `crypto-test`'s `utf8` section against Swift's own output (`Vectors/swift-utf8-decoding.json`,
written by `scripts/swift-utf8-vectors`), and through its callers: `records-test` (sealed records),
`io-test` (version messages' user agents) and the keys oracle's `walletSecret.parse`. -/

namespace Winnow.Text

/-- `String(decoding: bytes, as: UTF8.self)`: ill-formed sequences become U+FFFD, one per maximal subpart
(Unicode §3.9, "U+FFFD Substitution of Maximal Subparts"): a lead byte that cannot start a sequence (80–C1,
F5–FF) is one subpart; otherwise the lead and every continuation byte that still fits its sequence is one,
so a truncated sequence is one U+FFFD and the byte that broke it starts afresh. -/
def decodeUTF8Lossy (b : ByteArray) : String := Id.run do
  let n := b.size
  let cont (i : Nat) (lo hi : UInt8) : Bool := i < n && lo ≤ b[i]! && b[i]! ≤ hi
  let mut out := ""
  let mut i := 0
  while i < n do
    let b0 := b[i]!
    if b0 < 0x80 then
      out := out.push (Char.ofNat b0.toNat); i := i + 1
    else
      -- (sequence length, allowed range of the second byte): the second byte's range is what refuses
      -- overlongs (E0 80–9F, F0 80–8F), surrogates (ED A0–BF) and code points past U+10FFFF (F4 90–BF)
      let spec : Option (Nat × UInt8 × UInt8) :=
        if 0xC2 ≤ b0 && b0 ≤ 0xDF then some (2, 0x80, 0xBF)
        else if b0 == 0xE0 then some (3, 0xA0, 0xBF)
        else if b0 == 0xED then some (3, 0x80, 0x9F)
        else if 0xE1 ≤ b0 && b0 ≤ 0xEF then some (3, 0x80, 0xBF)
        else if b0 == 0xF0 then some (4, 0x90, 0xBF)
        else if b0 == 0xF4 then some (4, 0x80, 0x8F)
        else if 0xF1 ≤ b0 && b0 ≤ 0xF3 then some (4, 0x80, 0xBF)
        else none
      match spec with
      | none => out := out.push '�'; i := i + 1
      | some (len, lo, hi) =>
        -- how many bytes of the sequence are well-formed so far
        let mut good := 1
        if cont (i + 1) lo hi then
          good := 2
          if len ≥ 3 && cont (i + 2) 0x80 0xBF then
            good := 3
            if len ≥ 4 && cont (i + 3) 0x80 0xBF then good := 4
        if good == len then
          let mask : Nat := if len == 2 then 0x1F else if len == 3 then 0x0F else 0x07
          let mut cp := b0.toNat &&& mask
          for k in [1:len] do cp := cp * 64 + (b[i + k]!.toNat &&& 0x3F)
          out := out.push (Char.ofNat cp)
          i := i + len
        else
          out := out.push '�'; i := i + good
  return out

end Winnow.Text
