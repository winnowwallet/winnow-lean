import Std.Data.HashMap
import Winnow.Keys.UnicodeData
import Winnow.Wallet.Characters

/-! # The Unicode that Foundation does for WalletCore's keys

* NFD / NFKD (`decomposedStringWithCanonicalMapping` / `…WithCompatibilityMapping`): BIP39 normalizes
  sentences and passphrases NFKD; Swift `String` equality and dictionary keys are canonical equivalence,
  i.e. NFD equality.
* Splitting on a `Character` (`split(separator:)`), over Swift's own `Character`s (`Winnow.Characters`).
* `String(decoding:as: UTF8.self)`: invalid UTF-8 becomes U+FFFD per maximal subpart.
* `CharacterSet.whitespacesAndNewlines`. -/

namespace Winnow.Keys.Unicode

private def hexNat (s : String) : Nat :=
  s.foldl (fun acc c =>
    let d := if '0' ≤ c ∧ c ≤ '9' then c.toNat - '0'.toNat
      else if 'a' ≤ c ∧ c ≤ 'f' then c.toNat - 'a'.toNat + 10 else 0
    acc * 16 + d) 0

/-- Code point ↦ (compatibility?, one level of decomposition). -/
def decompTable : Std.HashMap Nat (Bool × Array Nat) := Id.run do
  let mut m : Std.HashMap Nat (Bool × Array Nat) := {}
  for e in UnicodeData.decompositions.splitOn ";" do
    let (compat, parts) :=
      if (e.splitOn "~").length == 2 then (true, e.splitOn "~") else (false, e.splitOn "=")
    match parts with
    | [k, v] => m := m.insert (hexNat k) (compat, ((v.splitOn " ").map hexNat).toArray)
    | _ => pure ()
  return m

def cccTable : Std.HashMap Nat Nat := Id.run do
  let mut m : Std.HashMap Nat Nat := {}
  for e in UnicodeData.combiningClasses.splitOn ";" do
    match e.splitOn ":" with
    | [k, v] => m := m.insert (hexNat k) v.toNat!
    | _ => pure ()
  return m

def ccc (c : Nat) : Nat := cccTable.getD c 0

def hangulSBase : Nat := 0xAC00
def hangulCount : Nat := 11172

partial def decomposeScalar (compat : Bool) (c : Nat) (acc : Array Nat) : Array Nat :=
  if hangulSBase ≤ c ∧ c < hangulSBase + hangulCount then
    let s := c - hangulSBase
    let l := 0x1100 + s / 588
    let v := 0x1161 + (s % 588) / 28
    let t := s % 28
    let acc := acc.push l |>.push v
    if t == 0 then acc else acc.push (0x11A7 + t)
  else
    match decompTable[c]? with
    | some (isCompat, parts) =>
      if isCompat && !compat then acc.push c
      else parts.foldl (fun a p => decomposeScalar compat p a) acc
    | none => acc.push c

/-- Canonical ordering: a stable sort of every run of non-starters by combining class. -/
def canonicalOrder (cs : Array Nat) : Array Nat := Id.run do
  let mut out := cs
  -- insertion sort inside runs (runs are short)
  for i in [1:out.size] do
    let mut j := i
    while j > 0 do
      let a := out[j - 1]!
      let b := out[j]!
      let ca := ccc a
      let cb := ccc b
      if cb != 0 && ca > cb then
        out := (out.set! (j - 1) b).set! j a
        j := j - 1
      else break
  return out

/-- Decomposition, then canonical ordering as Foundation applies it: runs are delimited by the *source*
scalars of combining class 0. This differs from UAX #15 only for U+0F73, U+0F75 and U+0F81 (class 0, but
decomposing into non-starters): Foundation does not reorder marks across them (measured, macOS 27). -/
def decompose (compat : Bool) (s : String) : String := Id.run do
  let mut out : Array Nat := #[]
  let mut run : Array Nat := #[]
  for ch in s.toList do
    let d := decomposeScalar compat ch.toNat #[]
    if ccc ch.toNat == 0 then
      out := out ++ canonicalOrder run
      run := d
    else run := run ++ d
  out := out ++ canonicalOrder run
  return String.ofList (out.toList.map Char.ofNat)

def nfd (s : String) : String := decompose false s
def nfkd (s : String) : String := decompose true s

/-- Split on a separator the way Swift splits a `String` on a `Character` (keeping empty pieces): the text is
cut into Swift `Character`s (`Winnow.Characters`, measured from Swift) and a piece ends at each `Character`
that is exactly the separator, so a separator that joins a neighbour (a combining mark after it, a Prepend
before it, `"\r\n"` for `'\n'`) does not separate. -/
def splitCharacters (s : String) (sep : Char) : List String := Id.run do
  let target := String.singleton sep
  let mut pieces : Array String := #[]
  let mut cur := ""
  for c in Characters.characters s do
    if c == target then
      pieces := pieces.push cur
      cur := ""
    else cur := cur ++ c
  return (pieces.push cur).toList

/-- `String(decoding: bytes, as: UTF8.self)`: each maximal ill-formed subpart becomes U+FFFD. -/
def decodeUTF8Lossy (b : ByteArray) : String := Id.run do
  let mut out : Array Char := #[]
  let mut i := 0
  let n := b.size
  let cont (x : UInt8) : Bool := 0x80 ≤ x && x ≤ 0xBF
  while i < n do
    let x := b[i]!
    if x < 0x80 then
      out := out.push (Char.ofNat x.toNat); i := i + 1
    else
      -- expected length and the allowed range of the second byte
      let (len, lo, hi) : Nat × UInt8 × UInt8 :=
        if 0xC2 ≤ x && x ≤ 0xDF then (2, 0x80, 0xBF)
        else if x == 0xE0 then (3, 0xA0, 0xBF)
        else if (0xE1 ≤ x && x ≤ 0xEC) || x == 0xEE || x == 0xEF then (3, 0x80, 0xBF)
        else if x == 0xED then (3, 0x80, 0x9F)
        else if x == 0xF0 then (4, 0x90, 0xBF)
        else if 0xF1 ≤ x && x ≤ 0xF3 then (4, 0x80, 0xBF)
        else if x == 0xF4 then (4, 0x80, 0x8F)
        else (0, 0, 0)
      if len == 0 then
        out := out.push '�'; i := i + 1
      else
        -- count how many bytes of the sequence are well-formed
        let mut k := 1
        let mut ok := true
        while ok && k < len do
          if i + k < n then
            let y := b[i + k]!
            let good := if k == 1 then lo ≤ y && y ≤ hi else cont y
            if good then k := k + 1 else ok := false
          else ok := false
        if k == len then
          let mut v : Nat := x.toNat &&& (if len == 2 then 0x1F else if len == 3 then 0x0F else 0x07)
          for j in [1:len] do v := v * 64 + (b[i + j]!.toNat &&& 0x3F)
          out := out.push (Char.ofNat v)
          i := i + len
        else
          out := out.push '�'; i := i + k
  return String.ofList out.toList

/-- `CharacterSet.whitespacesAndNewlines` (as measured: it includes U+200B). -/
def isWhitespaceOrNewline (c : Char) : Bool :=
  let n := c.toNat
  (0x09 ≤ n ∧ n ≤ 0x0D) || n == 0x20 || n == 0x85 || n == 0xA0 || n == 0x1680 ||
  (0x2000 ≤ n ∧ n ≤ 0x200B) || n == 0x2028 || n == 0x2029 || n == 0x202F || n == 0x205F || n == 0x3000

/-- `trimmingCharacters(in: .whitespacesAndNewlines)`. -/
def trimWhitespace (s : String) : String :=
  String.ofList ((s.toList.dropWhile isWhitespaceOrNewline).reverse.dropWhile isWhitespaceOrNewline).reverse

end Winnow.Keys.Unicode

namespace Winnow.Keys

/-- WalletCore's `Data(hex:)`: trims whitespace and newlines, then pairs of characters, each parsed as
Swift's `UInt8(_, radix: 16)` (which takes a sign: `+f` is 15, `-0` is 0). -/
def dataOfHex? (s : String) : Option ByteArray := Id.run do
  let cs := (Unicode.trimWhitespace s).toList.toArray
  if cs.isEmpty || cs.size % 2 != 0 then return none
  let digit (c : Char) : Option Nat :=
    if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat)
    else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
    else if 'A' ≤ c ∧ c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
    else none
  let mut out := ByteArray.empty
  for i in [0:cs.size / 2] do
    let a := cs[2 * i]!
    let b := cs[2 * i + 1]!
    let v : Option Nat := match a, digit a, digit b with
      | _, some x, some y => some (16 * x + y)
      | '+', none, some y => some y
      | '-', none, some 0 => some 0
      | _, _, _ => none
    match v with
    | some x => out := out.push x.toUInt8
    | none => return none
  return some out

end Winnow.Keys
