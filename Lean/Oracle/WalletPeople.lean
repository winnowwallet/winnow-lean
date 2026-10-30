import Oracle.WalletScenario

/-! People and import-bundle ops (Lean side of `LeanOracle/Wallet/People.swift`). The vault, vault-setup,
signer, shared-savings, approval and payment-label ops and `vault.flow` went with vaults (upstream
1cf93fb); the archived Swift harness still sends them, so its generators need the same trim. -/

namespace Oracle.WalletPeople
open Lean Winnow Keys

def netJ (j : Json) : Except String Tx.BitcoinNetwork := do
  match Tx.BitcoinNetwork.ofString? ((str j "network").toOption.getD "signet") with
  | some n => pure n
  | none => throw "network"

def errJ (e : String) : Json := err e
def optS (o : Option String) : Json := optJ Json.str o

/-! ## Pure ops -/

def payToJ (p : PersonPayTo) (network : Tx.BitcoinNetwork) (count : UInt32) : Json :=
  let r {α} (x : PM α) (f : α → Json) : Json := match x with | .ok a => f a | .error e => Json.str s!"error:{e}"
  Json.mkObj [("json", Json.str (SwiftJSON.write p.toJV)), ("fresh", Json.bool p.derivesFreshAddresses), ("text", Json.str p.text),
    ("a0", r (p.addressAt 0 network) Json.str), ("a5", r (p.addressAt 5 network) Json.str),
    ("scripts", r (p.scripts count network) fun xs => Json.arr (xs.map hexJ)), ("identity", r (p.identity network) hexJ)]

def importJ (i : PersonImport) (network : Tx.BitcoinNetwork) : Json :=
  Json.mkObj [("name", optS i.name), ("payTo", optJ (fun p => payToJ p network 2) i.payTo),
    ("source", Json.str i.source.name)]

def reportBundleJ (b : ImportBundle) : Json :=
  Json.mkObj [("serialized", Json.str b.serialized),
    ("claimed", match b.claimedUTXOs with
      | .ok us => Json.arr (us.map fun u => Json.str (SwiftJSON.write u.toJV))
      | .error e => Json.str s!"error:{e.name}")]

def ops : List (String × Handler) := [
  ("people.describe", fun j => do
    let n := (Tx.BitcoinNetwork.ofString? ((str j "network").toOption.getD "signet")).getD .signet
    let sArg := (str j "s").toOption.getD ""
    let iArg : Int := (j.getObjValAs? Int "i").toOption.getD 0
    let text ← match ← str j "type", ← str j "case" with
      | "payTo", c => match ([PersonPayToError.malformed, .privateKey, .singleAddressKey, .notSingleKey, .wrongNetwork n,
            .unsupportedDerivation].find? (·.name == c)) with
        | some e => pure e.description
        | none => throw "case"
      | "card", "notACard" => pure PersonCardError.notACard.description
      | "card", "unsupportedVersion" => pure (PersonCardError.unsupportedVersion iArg).description
      | "card", "wrongNetwork" => pure (PersonCardError.wrongNetwork sArg n).description
      | "paste", "empty" => pure PersonPasteError.empty.description
      | "paste", "unrecognised" => pure PersonPasteError.unrecognised.description
      | _, _ => throw "case"
    return ok (Json.str text)),
  ("people.payTo", fun j => do
    let n ← netJ j
    let text ← str j "text"
    let r := if (str j "kind").toOption == some "address" then PersonPayTo.ofAddress text n
      else (PersonPayTo.ofDescriptor text n).mapError (·.name)
    return match r with
      | .ok p => ok (payToJ p n ((nat j "count").toOption.getD 3).toUInt32) | .error e => errJ e),
  ("people.payToJSON", fun j => do
    return match SwiftJSON.decodeText (← str j "json") PersonPayTo.ofJV with
      | .ok p => ok (Json.str (SwiftJSON.write p.toJV)) | .error e => errJ e),
  ("people.displayName", fun j => do return ok (optS (DisplayName.normalized (← str j "text")))),
  ("people.cardMake", fun j => do
    let n ← netJ j
    let c := PersonCard.make n (← str j "name") (str j "payTo").toOption
    return ok (Json.arr #[Json.str c.serialized])),
  ("people.cardDecode", fun j => do
    return match PersonCard.decode (← str j "text") with
      | .ok c => ok (Json.str c.serialized) | .error e => errJ e.name),
  ("people.paste", fun j => do
    let n ← netJ j
    return match PersonPaste.parse (← str j "text") n with
      | .ok i => ok (importJ i n) | .error e => errJ e),
  ("bundle.decode", fun j => do
    return match ImportBundle.decode (← str j "json") with
      | .ok b => ok (reportBundleJ b) | .error e => errJ e.name),
  ("bundle.excerpt", fun j => do return ok (Json.str (ImportBundle.excerpt (← str j "text"))))
]

def ioOps : List (String × (Json → IO Json)) := []

end Oracle.WalletPeople
