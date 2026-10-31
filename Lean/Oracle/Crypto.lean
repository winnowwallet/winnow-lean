import Oracle.Base
import Winnow.Crypto

/-! Oracle ops for the base layer: hashes and encodings. -/

namespace Oracle
open Lean Winnow

def cryptoOps : List (String × Handler) := [
  ("sha256", fun j => return ok (hexJ (sha256 (← bytes j "data")))),
  ("sha256d", fun j => return ok (hexJ (sha256d (← bytes j "data")))),
  ("sha512", fun j => return ok (hexJ (sha512 (← bytes j "data")))),
  ("hmacSha256", fun j => return ok (hexJ (hmacSha256 (← bytes j "key") (← bytes j "data")))),
  ("hmacSha512", fun j => return ok (hexJ (hmacSha512 (← bytes j "key") (← bytes j "data")))),
  ("pbkdf2", fun j => return ok (hexJ (pbkdf2HmacSha512 (← bytes j "password") (← bytes j "salt") (← nat j "rounds") (← nat j "keyLength")))),
  ("ripemd160", fun j => return ok (hexJ (ripemd160 (← bytes j "data")))),
  ("hash160", fun j => return ok (hexJ (hash160 (← bytes j "data")))),
  ("siphash", fun j => return ok (Json.str (toString (sipHash (← u64 j "k0") (← u64 j "k1") (← bytes j "data")).toNat))),
  ("tagged", fun j => return ok (hexJ (taggedHash (← str j "tag") (← bytes j "data")))),
  ("base58.encode", fun j => return ok (Json.str (Base58.encode (← bytes j "data")))),
  ("base58.decode", fun j => do
    match Base58.decode (← str j "text") with
    | .ok b => return ok (hexJ b)
    | .error e => return err e.name),
  ("base58check.encode", fun j => return ok (Json.str (Base58Check.encode (← bytes j "data")))),
  ("base58check.decode", fun j => do
    match Base58Check.decode (← str j "text") with
    | .ok b => return ok (hexJ b)
    | .error e => return err e.name),
  ("segwit.encode", fun j => do
    match SegwitAddress.encode (← str j "hrp") (← nat j "version") (← bytes j "program") with
    | .ok s => return ok (Json.str s)
    | .error e => return err e.name),
  ("segwit.decode", fun j => do
    match SegwitAddress.decode (← str j "text") with
    | .ok (v, p) => return ok (Json.mkObj [("version", toJson v), ("program", hexJ p)])
    | .error e => return err e.name),
  ("bech32.decode", fun j => do
    match Bech32.decode (← str j "text") with
    | .ok (hrp, data, enc) =>
      return ok (Json.mkObj [("hrp", Json.str hrp), ("data", toJson (data.map (·.toNat))),
                             ("encoding", Json.str (if enc == .bech32 then "bech32" else "bech32m"))])
    | .error e => return err e.name)
]

end Oracle
