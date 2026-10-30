import Winnow.Crypto
import Winnow.Keys.BIP39Wordlist
import Winnow.Keys.Unicode

/-! # BIP39 mnemonics (port of `Keys/BIP39.swift`) -/

namespace Winnow.Keys

inductive BIP39Error where
  | invalidEntropyLength | invalidWordCount
  | wordNotInWordlist (word : String)
  | invalidChecksum
  deriving Repr, DecidableEq

def BIP39Error.name : BIP39Error → String
  | .invalidEntropyLength => "invalidEntropyLength" | .invalidWordCount => "invalidWordCount"
  | .wordNotInWordlist _ => "wordNotInWordlist" | .invalidChecksum => "invalidChecksum"

namespace BIP39

def wordlist : Array String := BIP39Wordlist.english

/-- The index of a word; the list is sorted, so a binary search. -/
def indexOf? (w : String) : Option Nat := Id.run do
  let mut lo := 0
  let mut hi := wordlist.size
  while lo < hi do
    let mid := (lo + hi) / 2
    let m := wordlist[mid]!
    if w == m then return some mid
    else if w < m then hi := mid else lo := mid + 1
  return none

def bitsOf (b : ByteArray) : Array Bool := Id.run do
  let mut out := #[]
  for x in b.toList do
    for i in [0:8] do out := out.push ((x >>> (7 - i).toUInt8) &&& 1 == 1)
  return out

/-- Entropy (16-32 bytes, multiple of 4) → mnemonic sentence. -/
def mnemonic (entropy : ByteArray) : Except BIP39Error String := do
  if entropy.size < 16 || entropy.size > 32 || entropy.size % 4 != 0 then throw .invalidEntropyLength
  let csLen := entropy.size * 8 / 32
  let bits := bitsOf entropy ++ (bitsOf ((sha256 entropy).extract 0 1)).extract 0 csLen
  let words := (List.range (bits.size / 11)).map fun w =>
    let idx := (List.range 11).foldl (fun acc j => acc * 2 + (if bits[w * 11 + j]! then 1 else 0)) 0
    wordlist[idx]!
  return " ".intercalate words

/-- Validates a mnemonic sentence against the wordlist and its checksum. Separators after NFKD are
exactly one space (each empty piece is a word that is not in the list). -/
def validate (mnemonic : String) : Except BIP39Error Unit := do
  let words := Unicode.splitCharacters (Unicode.nfkd mnemonic) ' '
  if ![12, 15, 18, 21, 24].contains words.length then throw .invalidWordCount
  let mut bits : Array Bool := #[]
  for w in words do
    match indexOf? w with
    | none => throw (.wordNotInWordlist w)
    | some idx => for j in [0:11] do bits := bits.push ((idx >>> (10 - j)) % 2 == 1)
  let csLen := words.length / 3
  let entLen := (bits.size - csLen) / 8
  let mut entropy := ByteArray.mk (Array.replicate entLen 0)
  for i in [0:entLen * 8] do
    if bits[i]! then entropy := entropy.set! (i / 8) (entropy[i / 8]! ||| (1 <<< (7 - (i % 8)).toUInt8))
  let checksum := (bits.extract (bits.size - csLen) bits.size).foldl (fun acc b => acc * 2 + (if b then 1 else 0)) 0
  let expected := (sha256 entropy)[0]!.toNat >>> (8 - csLen)
  if checksum != expected then throw .invalidChecksum

/-- Mnemonic → 64-byte seed via PBKDF2-HMAC-SHA512, salt "mnemonic"+passphrase, 2048 rounds; both
normalized NFKD. -/
def seed (mnemonic : String) (passphrase : String := "") : ByteArray :=
  pbkdf2HmacSha512 (Unicode.nfkd mnemonic).toUTF8 (Unicode.nfkd ("mnemonic" ++ passphrase)).toUTF8 2048 64

end BIP39
end Winnow.Keys
