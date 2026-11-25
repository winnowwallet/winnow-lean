import WinnowApp.Real.RecordsBackend
import WinnowApp.Real
import WinnowApp.View
import WinnowApp.E2E
import WinnowApp.Project
import WinnowApp.Main
import LeanNative.Erase
import LeanNative.Json
import TestKit.Check
import TestKit.Regtest
import FoundationVectors
import AppTestNames

/-! `records-test`: a scripted run of every records operation against a temporary directory, with the
in-memory key store and two wallets made by `Wallet.create` (two phones: A and B).

Covers people (add, rename, label, attach, remove), every kind of paste, receive and sender labels, store
tamper detection (on the sealed people file), a wrong-network store, a first write that fails, and
reopening everything from disk; the People store's payment index and pay-to checks; and the screens the
journeys open but never use (Home's payment screen, People, Settings, Receive, the recovery phrase and the
backup file with the Back up page and Restore from a file, and `Model.fail` for every failure a
screen can get), driven as a person uses them through the app's own `perform`; background tasks launched and
expired through `perform` (`backgroundTaskCommands`), and test mode's one seed variable. Exits 1 on any
failure. (The shared-savings and MuSig2 scenarios went with vaults, upstream 1cf93fb; cards and records
written with a `signerKey` still read.) -/

open Winnow WinnowApp WinnowApp.RecordsReal TestKit
open TestKit.Regtest (waitUntil)
open Tx (BitcoinNetwork)

instance : Describe RecordsError := ⟨(·.name), fun e => s!"{e.name}: {e.description}"⟩

/-- Runs `x`, a check that it succeeds; the value, or `none`. -/
def succeeds {α} (name : String) (x : RM α) : IO (Option α) := do
  match ← x.run with
  | .ok a => check name true; return some a
  | .error e => check name false s!"{e.name}: {e.description}"; return none

/-- `succeeds`, and the script stops when it does not. -/
def obtain {α} (name : String) (x : RM α) : IO α := do
  match ← succeeds name x with
  | some a => return a
  | none => throw (IO.userError s!"cannot continue after {name}")

def network : BitcoinNetwork := .regtest

def wm {α} (x : WM α) : RM α := liftWallet network x

def coinbaseInput : Transaction.Input :=
  { previousOutput := ⟨ByteArray.mk (Array.replicate 32 0), 0xFFFF_FFFF⟩, scriptSig := ByteArray.mk #[0x01], sequence := 0xFFFF_FFFF }

def fakeMatch (height : UInt32) (txs : Array Transaction) : Net.BlockMatch :=
  let header : Net.BlockHeader := {
    version := 2, previousHash := ByteArray.mk (Array.replicate 32 0),
    merkleRoot := ByteArray.mk (Array.replicate 32 0xAA), time := 1_700_000_000 + height, bits := 0x207F_FFFF, nonce := 0,
    hash := .empty }
  { height := height, blockHash := .empty, block := { header := header, transactions := txs } }

structure Phone where
  name : String
  dir : System.FilePath
  secrets : IO.Ref Keys.InMemorySecrets
  wallet : Wallet
  store : RecordsStore

def Phone.keyStore (p : Phone) : Keys.KeyStore IO := inMemoryKeyStore p.secrets
def Phone.keys (p : Phone) : StoreKeyVault := StoreKeyVault.ofKeyStore p.keyStore

def newPhone (root : System.FilePath) (name : String) : IO Phone := do
  let dir := root / name / "regtest"
  IO.FS.createDirAll dir
  let secrets ← IO.mkRef ({} : Keys.InMemorySecrets)
  let ks := inMemoryKeyStore secrets
  let wallet ← match ← (Wallet.create network ks (some (dir / "wallet.json"))).run with
    | .ok w => pure w
    | .error e => throw (IO.userError s!"Wallet.create: {e.name}")
  let store ← RecordsStore.open network (some dir) (StoreKeyVault.ofKeyStore ks)
  return { name, dir, secrets, wallet, store }

def Phone.reopen (p : Phone) : IO Phone := do
  return { p with store := ← RecordsStore.open network (some p.dir) p.keys }

def Phone.records (p : Phone) : IO Records := RecordsReal.records p.store (some p.wallet)

def mutateByte (b : ByteArray) (i : Nat) : ByteArray := b.set! i (b[i]! ^^^ 0x01)

/-! ## The script -/

def peopleAndPastes (a b : Phone) : IO Unit := do
  -- cards and own keys
  let cardB ← obtain "ownCard B" (do return (← ownPersonCard b.wallet "Bob").serialized)
  let keyB ← obtain "ownKeyExpression B" (ownKeyExpression b.wallet false)
  let keyBm ← obtain "ownKeyExpression B multipath" (ownKeyExpression b.wallet true)
  check "own key expression shape" (keyB.startsWith "[" && (keyB.splitOn "/86'/1'/0']tpub").length == 2 && keyBm == keyB ++ "/<0;1>/*") keyB
  -- pastes of each kind
  let pCard ← obtain "paste card" (parsePaste network cardB)
  check "paste card reads name and fresh pay-to" (pCard.name == some "Bob" && pCard.payTo == some true)
  let pKey ← obtain "paste key expression" (parsePaste network keyB)
  check "paste bare key: fresh pay-to" (pKey.payTo == some true && pKey.name.isNone)
  let pKeyM ← obtain "paste multipath key" (parsePaste network keyBm)
  check "paste multipath key" (pKeyM.payTo == some true)
  let pDesc ← obtain "paste descriptor" (parsePaste network s!"tr({keyBm})")
  check "paste descriptor: pay-to" (pDesc.payTo == some true)
  let addrB ← obtain "B address" (wm (b.wallet.address .receive 7))
  let pAddr ← obtain "paste address" (parsePaste network addrB)
  check "paste address: one address" (pAddr.payTo == some false)
  refused "paste empty" (kind := "empty") (parsePaste network "   ")
  refused "paste garbage" (kind := "unrecognised") (parsePaste network "hello world")
  refused "paste mainnet address on regtest" (kind := "wrongNetwork") (parsePaste network "bc1qar0srrr7xfkvy5l643lydnw9re59gtzzwf5mdq")
  let otherNet ← obtain "card for another network" (do
    let c := PersonCard.make .mainnet "Eve" none
    return c.serialized)
  refused "paste card of another network" (kind := "wrongNetwork") (parsePaste network otherNet)
  -- a card from a Winnow that also shared a signer key still reads; the key is ignored
  let oldCard := s!"\{\"name\":\"Bob\",\"network\":\"regtest\",\"payTo\":\"tr({keyBm})\",\"signerKey\":\"{keyBm}\",\"version\":1,\"winnow\":\"person-card\"}"
  let pOld ← obtain "paste a card that carries a signer key" (parsePaste network oldCard)
  check "the old card reads as a pay-to card" (pOld.name == some "Bob" && pOld.payTo == some true)
  check "a stored person's signerKey is ignored, and never written back"
    (match SwiftJSON.decodeText s!"\{\"id\":\"p\",\"name\":\"Old\",\"nextPaymentIndex\":0,\"signerKey\":\"{keyBm}\"}" PersonRecord.ofJV with
     | .ok r => r.payTo.isNone && SwiftJSON.write r.toJV == "{\"id\":\"p\",\"name\":\"Old\",\"nextPaymentIndex\":0}"
     | .error _ => false)
  -- add / rename / duplicates
  let r ← obtain "add Bob from card" (addPerson a.store (some a.wallet) "Bob" (some cardB) none none none)
  let some bob := r.people.find? (·.name == "Bob") | check "Bob saved" false; return
  check "Bob is paid at fresh addresses" (bob.payTo == some true)
  check "recipientByScript covers Bob's first scripts" ((r.recipientByScript.filter (·.2 == bob.id)).length == 20)
  refused "duplicate card refused" (kind := "duplicate") (addPerson a.store (some a.wallet) "Bobby" (some cardB) none none none)
  refused "a name over two lines is refused" (kind := "invalidState") (addPerson a.store (some a.wallet) "Bo\nb" (some addrB) none none none)
  let r ← obtain "rename Bob" (updateRecipient a.store (some a.wallet) bob.id (some "Robert") true)
  check "renamed" ((r.people.find? (·.id == bob.id)).map (·.name) == some "Robert")
  let r ← obtain "add Carol from an address" (addPerson a.store (some a.wallet) "Carol" (some addrB) none none none)
  let some carol := r.people.find? (·.name == "Carol") | check "Carol saved" false; return
  check "Carol pays one address" (carol.payTo == some false)
  -- sender labels
  let txid := hex (ByteArray.mk (Array.replicate 32 0x5a))
  let r ← obtain "add Dave as the sender of a payment" (addPerson a.store (some a.wallet) "Dave" none none none (some txid))
  let some dave := r.people.find? (·.name == "Dave") | check "Dave saved" false; return
  check "Dave is name-only and labels the payment" (dave.payTo.isNone && r.senderByTxid == [(txid, dave.id)])
  refused "label with an unknown person" (kind := "unknownPerson") (labelSender a.store (some a.wallet) txid "nobody")
  refused "label with an invalid txid" (kind := "invalidState") (labelSender a.store (some a.wallet) "abcd" dave.id)
  refused "a sender with an invalid txid" (kind := "invalidState") (addPerson a.store (some a.wallet) "Eve" none none none (some "abcd"))
  let r ← RM.toIO (RM.io (RecordsReal.records a.store (some a.wallet)))
  check "the person is saved even when the label is refused (as AppModel's two steps)" (r.people.any (·.name == "Eve"))
  let some eve := r.people.find? (·.name == "Eve") | check "Eve saved" false; return
  let aR ← a.reopen
  check "and disk agrees with memory" ((← RecordsReal.records aR.store (some a.wallet)).people.any (·.name == "Eve"))
  discard <| obtain "remove Eve" (removePerson a.store (some a.wallet) eve.id)
  let addrB2 ← obtain "B address 8" (wm (b.wallet.address .receive 8))
  let r ← obtain "attach a funding address to Dave" (attachDestination a.store (some a.wallet) dave.id addrB2 .localFunding (some txid))
  check "Dave now has an unverified funding destination"
    (((r.people.find? (·.id == dave.id)).map fun p => p.payTo == some false && p.provenance == some .localFunding) == some true)
  refused "a second destination is refused" (kind := "invalidState") (attachDestination a.store (some a.wallet) dave.id addrB .supplied none)
  let r ← obtain "remove the sender label" (removeSenderLabel a.store (some a.wallet) txid)
  check "label removed" r.senderByTxid.isEmpty
  discard <| obtain "label again" (labelSender a.store (some a.wallet) txid dave.id)
  let r ← obtain "remove Dave" (removePerson a.store (some a.wallet) dave.id)
  check "removing a person prunes their labels" (r.senderByTxid.isEmpty && !(r.people.any (·.id == dave.id)))
  let r ← obtain "remove Carol" (removePerson a.store (some a.wallet) carol.id)
  check "Carol removed" (!(r.people.any (·.id == carol.id)))
  refused "remove twice" (kind := "unknownPerson") (removePerson a.store (some a.wallet) carol.id)
  -- hide and re-save a recipient keeps the record
  let r ← obtain "hide Robert" (updateRecipient a.store (some a.wallet) bob.id none false)
  check "hidden" (((r.people.find? (·.id == bob.id)).map (·.isSavedRecipient)) == some false)
  let r ← obtain "re-saving the hidden card restores it" (addPerson a.store (some a.wallet) "Bob" (some cardB) none none none)
  check "same record, saved again, renamed" (((r.people.find? (·.id == bob.id)).map fun p => p.isSavedRecipient && p.name == "Bob") == some true)
  -- B knows A too
  let cardA ← obtain "ownCard A" (do return (← ownPersonCard a.wallet "Alice").serialized)
  discard <| obtain "B adds Alice" (addPerson b.store (some b.wallet) "Alice" (some cardA) none none none)

/-- A card per person (issue #94): A makes a card for one person, B is that person and pays it. -/
def personCards (a b : Phone) : IO Unit := do
  let contains (haystack needle : String) : Bool := (haystack.splitOn needle).length > 1
  let (cardText, r) ← obtain "a card for Dana" (personCard a.store a.wallet none " Dana " "Alice")
  let some dana := r.people.find? (·.name == "Dana") | check "card: Dana is a contact" false; return
  check "card: the person is saved by name, with no destination, and has a card"
    (dana.payTo.isNone && dana.hasCard && !dana.isSavedRecipient)
  let issued ← a.wallet.cards
  check "card: the wallet issued one card" (issued.size == 1)
  let some code := (← (a.wallet.card 0).run).toOption | check "card: issued" false; return
  let codeText := code.encoded.toOption.getD ""
  -- the wallet's own two keys, as its file records them and as a card of 0.9.12 carried them beside a tweak
  let keysText := (← a.wallet.state).silentPaymentAddress.getD ""
  let some own := (SilentPaymentAddress.parse keysText).toOption | check "card: the wallet records its keys" false; return
  let tweakHex := (issued[0]?.map fun c => hex c.tweak).getD ""
  check "card: a version 3 person card under my name, with Dana's code and nothing else to pay with"
    (match PersonCard.decode cardText with
     | .ok c => c.version == 3 && c.name == "Alice" && c.network == "regtest" && c.payTo == some codeText &&
         c.tweak.isNone && codeText.startsWith "twinnowcard1p"
     | .error _ => false) cardText
  check "card: the card carries neither the account key, nor the wallet's two keys, nor the tweak"
    (!contains cardText "tpub" && !contains cardText "tr(" && !contains cardText "tweak" && !contains cardText tweakHex &&
     code.sharedSecret != own.scanKey && code.spendKey != own.spendKey && !contains cardText (keysText.drop 14).toString)
  let (again, _) ← obtain "Dana's card again" (personCard a.store a.wallet none "Dana" "Alice")
  check "card: asked again, it is the same card and no new one is issued" (again == cardText && (← a.wallet.cards).size == 1)
  check "card: whether a person has one" ((← hasPersonCard a.store none "Dana") && (← hasPersonCard a.store none " Dana ") &&
    (← hasPersonCard a.store (some dana.id) "") && !(← hasPersonCard a.store none "Nobody") &&
    !(← hasPersonCard a.store none "") && !(← hasPersonCard a.store (some "no such id") "Dana"))
  let (erinText, r) ← obtain "a card for Erin" (personCard a.store a.wallet none "Erin" "Alice")
  check "card: another person gets another card" (erinText != cardText && (← a.wallet.cards).size == 2 &&
    (r.people.filter (·.hasCard)).length == 2)
  -- two people of one name: by name the first is meant, by ID the one that was chosen
  let twin ← obtain "a second Dana" (do
    let (ps, record) ← (← RM.io a.store.read).people.add a.keys writeAtomically "twin" "Dana" none
    a.store.modify fun st => pure ({ st with people := ps }, record))
  let (byName, _) ← obtain "Dana by name" (personCard a.store a.wallet none "Dana" "Alice")
  let (byID, r) ← obtain "the second Dana by ID" (personCard a.store a.wallet (some twin.id) "Dana" "Alice")
  check "card: by name the first Dana's card, by ID the second Dana's own"
    (byName == cardText && byID != cardText && (← a.wallet.cards).size == 3 &&
     (r.people.filter fun p => p.name == "Dana" && p.hasCard).length == 2)
  refused "card: a person that is not saved has no card" (kind := "unknownPerson") (personCard a.store a.wallet (some "no such id") "Dana" "Alice")
  discard <| obtain "the second Dana goes" (removePerson a.store (some a.wallet) twin.id)
  refused "card: a name over two lines makes no card" (kind := "invalidState") (personCard a.store a.wallet none "Da\nna" "Alice")
  check "card: and issues none" ((← a.wallet.cards).size == 3)
  -- the person pastes it
  let read ← obtain "B reads the card" (parsePaste network cardText)
  check "card: read as Alice, a fresh address each payment" (read.name == some "Alice" && read.payTo == some true)
  -- the code on its own is the whole of what a card pays with: the same person, without the name
  let lone ← obtain "B reads the code alone" (parsePaste network codeText)
  check "card: the code pasted alone is read as a card, without a name" (lone.name.isNone && lone.payTo == some true)
  check "card: in capitals too" ((← (parsePaste network codeText.toUpper).run).toOption.map (·.payTo) == some (some true))
  -- the wallet's two keys out of a 0.9.12 card are not: before they had a prefix of their own they read as an
  -- ordinary silent payment address, and a payment made to it that way is one A's wallet never finds
  refused "card: the two keys of a 0.9.12 card alone, without the tweak, are not read as anything to pay" (kind := "cardAddressAlone")
    (parsePaste network keysText)
  -- B already has an Alice (her shared card): names are not unique, so this one is found by its own
  let rb ← obtain "B saves Alice" (addPerson b.store (some b.wallet) "Alice, her card for me" (some cardText) none none none)
  let some alice := rb.people.find? (·.name == "Alice, her card for me") | check "card: Alice saved on B" false; return
  check "card: B's first scripts for Alice are the card's" (
    let expected := (List.range 20).filterMap fun i => (Keys.SilentPaymentPairing.codeScript code i.toUInt32).toOption.map hex
    (rb.recipientByScript.filter (·.2 == alice.id)).map (·.1) == expected && expected.length == 20)
  let (address0, index0) ← obtain "B's next payment" (nextPaymentAddress b.store alice.id)
  let script0 := (Keys.SilentPaymentPairing.codeScript code 0).toOption.getD .empty
  check "card: B pays payment 0 of the card, an address A's wallet watches"
    (index0 == 0 && some address0 == AddressDecoder.address script0 network &&
     ((← (a.wallet.watchScripts).run).toOption.getD #[]).contains script0) address0
  -- for a payer that does not read cards, an exchange say: the same card's next unpaid address, as an address
  let plain ← obtain "an address for Dana" (personAddress a.store a.wallet none " Dana ")
  check "address: Dana's ordinary address is what her card's first payment goes to" (plain == address0 && plain.startsWith "bcrt1p")
  check "address: by her ID too, and the same until it is paid"
    ((← (personAddress a.store a.wallet (some dana.id) "").run).toOption == some plain)
  check "address: Erin's is another" ((← (personAddress a.store a.wallet none "Erin").run).toOption.any (· != plain))
  refused "address: nobody by that name" (kind := "unknownPerson") (personAddress a.store a.wallet none "Nobody")
  refused "address: nobody by that ID" (kind := "unknownPerson") (personAddress a.store a.wallet (some "no such id") "Dana")
  refused "address: a person without a card has none" (kind := "unknownCard") (personAddress a.store a.wallet none "Bob")
  check "address: asking for one issues no card" ((← a.wallet.cards).size == 3)
  discard <| advancePersonPaymentIndex b.store (some b.wallet) alice.id index0
  let (address1, index1) ← obtain "B's payment after that" (nextPaymentAddress b.store alice.id)
  check "card: the next payment is the next index, another address" (index1 == 1 && address1 != address0)
  refused "card: the same card for a second person is refused" (kind := "duplicate")
    (addPerson b.store (some b.wallet) "Alicia" (some cardText) none none none)
  refused "card: the code alone for a second person is refused too" (kind := "duplicate")
    (addPerson b.store (some b.wallet) "Alicia" (some codeText) none none none)
  let withCode (payTo : String) : String := (PersonCard.make network "Alice" (some payTo)).serialized
  let mainnetCode := ({ code with hrp := Keys.SilentPaymentPairing.hrp true } : CardCode).encoded.toOption.getD ""
  let otherNetwork (text : String) : IO Bool := do
    match ← (parsePaste network text).run with
    | .error e => return e.description == "That code is for a different Bitcoin network. This wallet is on regtest."
    | .ok _ => return false
  check "card: a card whose code is for another network says so, and so does that code alone"
    (mainnetCode.startsWith "winnowcard1p" && (← otherNetwork (withCode mainnetCode)) && (← otherNetwork mainnetCode))
  let notValid (text : String) : IO Bool := do
    match ← (parsePaste network text).run with
    | .error e => return e.description == "That card's code is not valid. Ask for the card again."
    | .ok _ => return false
  check "card: a code that is damaged says so, in a card or alone"
    ((← notValid (codeText ++ "q")) && (← notValid (withCode (codeText ++ "q"))))
  check "card: a card with the wallet's two keys and no tweak is not a card"
    (match ← (parsePaste network (withCode keysText)).run with
     | .error e => e.description == "That isn't a Winnow card."
     | .ok _ => false)
  -- a card of 0.9.12: the wallet's two keys and a tweak. It is still read, as the code that pays what it paid
  let withPayTo (payTo tweak : String) : String := (PersonCard.make network "Alice" (some payTo) (tweak := some tweak)).serialized
  let oldCard := withPayTo keysText tweakHex
  let oldCode := ((Keys.SilentPaymentPairing.codeOf { address := own, tweak := (issued[0]?.map (·.tweak)).getD .empty }).toOption.bind
    (·.encoded.toOption)).getD ""
  check "card: a 0.9.12 card is version 2, and is read"
    (contains oldCard "\"version\":2" && (← (parsePaste network oldCard).run).toOption.map (·.payTo) == some (some true))
  check "card: it is kept as a code with the wallet's own spend key, which pays what the card paid"
    (oldCode.startsWith "twinnowcard1p" && oldCode != codeText &&
     (PersonPayTo.ofCard keysText tweakHex network).toOption == some (.card oldCode) &&
     (List.range 5).all fun i => (PersonPayTo.cardScript oldCode i.toUInt32 network).toOption ==
       (Keys.SilentPaymentPairing.scriptPubKey { address := own, tweak := (issued[0]?.map (·.tweak)).getD .empty } i.toUInt32).toOption)
  check "card: a code with a tweak beside it is refused" ((← (parsePaste network (withPayTo codeText tweakHex)).run).toOption.isNone)
  let mainnetAddress := ({ own with hrp := Keys.SilentPaymentPairing.hrp true } : SilentPaymentAddress).encoded.toOption.getD ""
  check "card: a 0.9.12 card whose keys are for another network says so" (← otherNetwork (withPayTo mainnetAddress tweakHex))
  -- the same keys written as a silent payment address: not what a card carries, and refused as that
  let plainAddress := ({ own with hrp := "tsp" } : SilentPaymentAddress).encoded.toOption.getD ""
  let plain ← (parsePaste network (withPayTo plainAddress tweakHex)).run
  check "card: a card that carries a plain silent payment address says so" (plainAddress.startsWith "tsp1" && (match plain with
    | .error e => e.description == "That card carries a plain silent payment address, which a card for one person does not use. Ask for a new card."
    | .ok _ => false))
  -- a person saved by 0.9.12 holds the two keys and the tweak, and for a day before that the keys were written
  -- tsp1…: the same person either way, read into the code that pays the same addresses
  let saved (keys : String) : Option PersonPayTo :=
    (PersonPayTo.ofJV (.obj #[("kind", .str "card"), ("tweak", .str tweakHex), ("value", .str keys)])).toOption
  check "card: a person 0.9.12 saved is read into the code" (saved keysText == some (.card oldCode))
  check "card: a person saved with the keys written as a silent payment address is read into the same code"
    (saved plainAddress == some (.card oldCode))
  check "card: a saved code reads back as it was, and is written without a tweak"
    ((PersonPayTo.ofJV (PersonPayTo.card codeText).toJV).toOption == some (.card codeText) &&
     !contains (SwiftJSON.write (PersonPayTo.card codeText).toJV) "tweak")
  check "card: a saved card whose keys are not keys is left for validation to refuse"
    (saved "tsp1qqnotanaddress" == some (.card "tsp1qqnotanaddress") &&
     (PersonPayTo.ofCardCode "tsp1qqnotanaddress" network).toOption.isNone)
  let alone ← (parsePaste network keysText).run
  check "card: the card's address pasted on its own says to paste the whole card" (match alone with
    | .error e => e.description == "That is the address from inside a Winnow card. On its own it cannot be paid: paste the whole card."
    | .ok _ => false)
  check "card: neither the code nor the wallet's two keys are taken for a silent payment code"
    ([codeText, keysText].all fun t => (PersonPayTo.ofSilentPayment t network).toOption.isNone && !SilentPaymentAddress.looksLikeCode t)
  let badTweak ← (parsePaste network (withPayTo keysText "00")).run
  check "card: a card whose tweak is not one says so" (match badTweak with
    | .error e => e.description == "That card's tweak is not valid. Ask for the card again."
    | .ok _ => false)
  refused "card: a zero tweak is refused" (kind := "invalidTweak")
    (parsePaste network (withPayTo keysText (String.ofList (List.replicate 64 '0'))))
  refused "card: a tweak with an ordinary address is refused" (parsePaste network (withPayTo address0 tweakHex))
  check "card: a tweak with nothing to pay is not a card"
    ((← (parsePaste network "{\"name\":\"Alice\",\"network\":\"regtest\",\"tweak\":\"00\",\"version\":2,\"winnow\":\"person-card\"}").run).toOption.isNone)
  -- a payment to a card is named as its person's
  let txid := String.ofList (List.replicate 64 'a')
  labelCardPayment a.store 0 txid
  check "card: a payment to Dana's card is labelled Dana's" ((lookup (← a.records).senderByTxid txid) == some dana.id)
  labelCardPayment a.store 0 txid
  check "card: labelled once" (((← a.records).senderByTxid.filter (·.1 == txid)).length == 1)
  let some erin := (← a.records).people.find? (·.name == "Erin") | check "card: Erin" false; return
  let other := String.ofList (List.replicate 64 'b')
  discard <| obtain "label by hand" (labelSender a.store (some a.wallet) other erin.id)
  labelCardPayment a.store 0 other
  check "card: a label already given is kept" ((lookup (← a.records).senderByTxid other) == some erin.id)
  labelCardPayment a.store 9 (String.ofList (List.replicate 64 'c'))
  check "card: a card nobody is linked to labels nothing" ((← a.records).senderByTxid.length == 2)
  -- the file
  let reopened ← a.reopen
  check "card: the links are in the people file" (((← reopened.records).people.filter (·.hasCard)).map (·.name) == ["Dana", "Erin"])
  let st ← a.store.read
  let people := st.people.records
  check "card: two people linked to one card is an invalid file"
    ((← (PeopleStore.validate (people.map fun (p : PersonRecord) => if p.name == "Erin" then { p with issuedCard := some 0 } else p)
      st.people.senderByTxid network).run).toOption.isNone)
  check "card: a person with no card writes no link"
    (!contains (SwiftJSON.write ({ id := "p", name := "Plain" } : PersonRecord).toJV) "issuedCard")
  -- an iCloud copy brings the links back to a phone that has the contacts without them
  let backup ← obtain "backup" st.people.backup
  let unlinked : PeopleStore := { st.people with records := people.map fun (p : PersonRecord) => { p with issuedCard := none } }
  let merged : PeopleStore.Backup ← obtain "restore plan" (unlinked.planRestore backup)
  check "card: a restore gives the contacts their cards back"
    ((merged.people.filter (·.issuedCard.isSome)).map (fun (p : PersonRecord) => (p.name, p.issuedCard)) == #[("Dana", some 0), ("Erin", some 1)])
  let taken : PeopleStore := { st.people with records := people.map fun (p : PersonRecord) =>
    if p.name == "Erin" then { p with issuedCard := some 0 }
    else if p.name == "Dana" then { p with id := "another", name := "Dan", issuedCard := none } else p }
  let merged : PeopleStore.Backup ← obtain "restore plan, a card already linked here" (taken.planRestore backup)
  check "card: a restore never links one card to two people"
    ((merged.people.filter (·.issuedCard == some 0)).map (fun (p : PersonRecord) => p.name) == #["Erin"] &&
     merged.people.any (fun (p : PersonRecord) => p.name == "Dana"))

def receiveLabels (a b : Phone) : IO Unit := do
  let addr ← obtain "A receive address" (wm (a.wallet.address .receive 0))
  let foreign ← obtain "B receive address" (wm (b.wallet.address .receive 0))
  let r ← obtain "set a receive label" (setReceiveLabel a.store a.wallet addr "Invoice 12")
  check "label shown by address" (r.receiveLabels == [(addr, "Invoice 12")])
  refused "a label for someone else's address is refused" (kind := "noWallet")
    (setReceiveLabel a.store a.wallet foreign "x")
  refused "a two-line label is refused" (kind := "invalidLabel") (setReceiveLabel a.store a.wallet addr "a\nb")
  let addr1 ← obtain "A receive address 1" (wm (a.wallet.address .receive 1))
  discard <| obtain "second label" (setReceiveLabel a.store a.wallet addr1 "  Rent  ")
  let r ← obtain "empty text removes a label" (setReceiveLabel a.store a.wallet addr "")
  check "one label left, trimmed" (r.receiveLabels == [(addr1, "Rent")])
  let file ← IO.FS.readFile (a.dir / "receive-labels.json")
  let script ← obtain "script of address 1" (RM.lift (fun e => namedError e.name network) (AddressDecoder.scriptPubKey addr1 network))
  check "labels file in the Swift shape"
    (file == s!"\{\"labels\":\{\"{hex script}\":\"Rent\"},\"network\":\"regtest\",\"version\":1,\"walletID\":\"{a.wallet.id}\"}") file

def lookupSenderTest (b : Phone) : IO Unit := do
  let txid := hex (ByteArray.mk (Array.replicate 32 0x11))
  let funder ← obtain "B address 9" (wm (b.wallet.address .receive 9))
  let answer := s!"\{\"txid\":\"{txid}\",\"vin\":[\{\"prevout\":\{\"scriptpubkey_address\":\"{funder}\"}},\{\"prevout\":null},\{\"prevout\":\{\"scriptpubkey_address\":\"{funder}\"}}]}"
  let urls ← IO.mkRef ([] : List String)
  let get : String → Nat → IO ByteArray := fun url _ => do urls.modify (url :: ·); return answer.toUTF8
  let addrs ← obtain "lookupSender" (lookupSender get network txid "https://example.org/api/")
  check "distinct funding addresses, in input order" (addrs == [funder])
  check "GET {base}/tx/{txid}" ((← urls.get) == [s!"https://example.org/api/tx/{txid}"])
  let other : String → Nat → IO ByteArray := fun _ _ => return "{\"txid\":\"00\",\"vin\":[]}".toUTF8
  refused "a different transaction is refused" (kind := "unavailable") (lookupSender other network txid "https://example.org/api")
  let bad : String → Nat → IO ByteArray := fun _ _ => return "[]".toUTF8
  refused "a wrong shape is refused" (kind := "unavailable") (lookupSender bad network txid "https://example.org/api")
  refused "an invalid txid is refused" (kind := "unavailable") (lookupSender get network "abc" "https://example.org/api")

def tamper (root : System.FilePath) (a : Phone) : IO Unit := do
  -- tampered people.json: a notice, and every mutation refused
  let peoplePath := a.dir / "people.json"
  let good ← IO.FS.readBinFile peoplePath
  check "people.json is sealed" (SealedStoreFile.isSealed good)
  IO.FS.writeBinFile peoplePath (mutateByte good (good.size - 3))
  let a2 ← a.reopen
  let r ← a2.records
  check "tampered people: unverified notice, no people"
    (r.peopleStorageNotice == some PeopleStore.unverifiedStorageMessage && r.people.isEmpty)
  refused "a damaged people store refuses mutations" (kind := "damaged")
    (addPerson a2.store (some a.wallet) "Zed" none none none (some (hex (ByteArray.mk (Array.replicate 32 1)))))
  IO.FS.writeBinFile peoplePath good
  -- unsealed file while a key exists
  match SealedStoreFile.open good "people" network ((← (a.keys.key "people.regtest").run).toOption.join.getD .empty) with
  | .ok payload =>
    IO.FS.writeBinFile peoplePath payload
    let a3 ← a.reopen
    check "an unsealed file once a key exists reads as unverified"
      ((← a3.records).peopleStorageNotice == some PeopleStore.unverifiedStorageMessage)
    -- a valid seal around invalid content is damage, not substitution
    let key := ((← (a.keys.key "people.regtest").run).toOption.join).getD .empty
    IO.FS.writeBinFile peoplePath (SealedStoreFile.sealed "{\"people\":[{\"id\":\"x\"}]}".toUTF8 "people" network key)
    let a4 ← a.reopen
    check "valid seal, invalid records: the damaged message"
      ((← a4.records).peopleStorageNotice == some PeopleStore.damagedStorageMessage)
  | .error e => check "own people file opens" false e.name
  IO.FS.writeBinFile peoplePath good
  let unverified (st : RecordsStore) : IO Bool := do
    return (← RecordsReal.records st none).peopleStorageNotice == some PeopleStore.unverifiedStorageMessage
  let peopleKey := ((← (a.keys.key "people.regtest").run).toOption.join).getD .empty
  -- a file sealed for another store name (the seal binds the store)
  match SealedStoreFile.open good "people" network peopleKey with
  | .ok payload =>
    IO.FS.writeBinFile peoplePath (SealedStoreFile.sealed payload "vaults" network peopleKey)
    check "a file sealed for another store is refused" (← unverified (← a.reopen).store)
  | .error e => check "own people file opens" false e.name
  IO.FS.writeBinFile peoplePath good
  -- wrong network, same device: a regtest file under signet, where signet has a key
  let sigDir := root / "A-signet"
  IO.FS.createDirAll sigDir
  let sig ← RecordsStore.open .signet (some sigDir) a.keys
  discard <| obtain "signet store's first write establishes its key"
    (addPerson sig none "Sam" none none none (some (hex (ByteArray.mk (Array.replicate 32 2)))))
  IO.FS.writeBinFile (sigDir / "people.json") good
  check "a regtest people file under signet fails verification" (← unverified (← RecordsStore.open .signet (some sigDir) a.keys))
  -- wrong network, fresh device: sealed file, no key at all
  let fresh ← IO.mkRef ({} : Std.HashMap String ByteArray)
  let freshDir := root / "fresh"
  IO.FS.createDirAll freshDir
  IO.FS.writeBinFile (freshDir / "people.json") good
  check "a sealed file without its key is refused (keyMissing)"
    (← unverified (← RecordsStore.open network (some freshDir) (StoreKeyVault.inMemory fresh)))
  -- a file from before sealing is adopted and sealed
  let legacyDir := root / "legacy"
  IO.FS.createDirAll legacyDir
  let legacyKeys ← IO.mkRef ({} : Std.HashMap String ByteArray)
  match SealedStoreFile.open good "people" network peopleKey with
  | .ok payload =>
    IO.FS.writeBinFile (legacyDir / "people.json") payload
    let ls ← RecordsStore.open network (some legacyDir) (StoreKeyVault.inMemory legacyKeys)
    let r ← RecordsReal.records ls none
    check "an unsealed legacy file loads" r.peopleStorageNotice.isNone
    check "and is sealed now" (SealedStoreFile.isSealed (← IO.FS.readBinFile (legacyDir / "people.json")))
    check "with its people" (!r.people.isEmpty)
  | .error e => check "own people file opens" false e.name
  -- a first write that fails discards the new key
  let failKeys ← IO.mkRef ({} : Std.HashMap String ByteArray)
  let failDir := root / "fail"
  IO.FS.createDirAll failDir
  let fs ← RecordsStore.open network (some failDir) (StoreKeyVault.inMemory failKeys)
    (writeData := fun _ _ => throw (IO.userError "disk full"))
  refused "a failed first write fails" (kind := "ioError")
    (addPerson fs none "Nia" none none none (some (hex (ByteArray.mk (Array.replicate 32 3)))))
  check "and leaves no key behind" (!(← failKeys.get).contains "people.regtest")
  check "and no person" (← records fs none).people.isEmpty
  -- a damaged label file: a notice, sets refused
  let labelsPath := a.dir / "receive-labels.json"
  let lgood ← IO.FS.readBinFile labelsPath
  IO.FS.writeBinFile labelsPath "{\"version\":2}".toUTF8
  let a5 ← a.reopen
  let r ← a5.records
  check "damaged labels: notice" (r.receiveLabelStorageNotice == some (RecordsError.labels .damaged).description && r.receiveLabels.isEmpty)
  let addr ← obtain "address" (wm (a.wallet.address .receive 2))
  refused "a damaged label store refuses sets" (kind := "damaged") (setReceiveLabel a5.store a.wallet addr "x")
  IO.FS.writeBinFile labelsPath lgood

def reopenFromDisk (a : Phone) (before : Records) : IO Unit := do
  let a2 ← a.reopen
  let r ← a2.records
  check "reopen: the same people" (r.people == before.people) s!"{reprStr r.people}"
  check "reopen: the same labels" (r.receiveLabels == before.receiveLabels && r.senderByTxid == before.senderByTxid)
  check "reopen: no notices" (r.peopleStorageNotice.isNone && r.receiveLabelStorageNotice.isNone)
  -- the people file is exactly what the Swift encoder writes for these records
  let st ← a2.store.read
  let file ← IO.FS.readBinFile (a.dir / "people.json")
  let key := ((← (a.keys.key "people.regtest").run).toOption.join).getD .empty
  check "people.json: seal over the sorted-key envelope"
    (file == SealedStoreFile.sealed (PeopleStore.encode st.people.records st.people.senderByTxid) "people" network key)

/-- Upstream d2ca878's `BackgroundSyncTests`: the home waits out dropped peers but shows other errors at
once, and only link failures count as transient. -/
def syncErrorBookkeeping : IO Unit := do
  let dropped := (Winnow.IO.NetError.peer (.disconnected "closed")).description
  check "simple sync error: none without an error" (simpleSyncError none none 0 == none)
  check "simple sync error: one dropped peer stays quiet" (simpleSyncError (some dropped) (some dropped) 1 == none)
  check "simple sync error: two dropped peers stay quiet" (simpleSyncError (some dropped) (some dropped) 2 == none)
  check "simple sync error: a third is said in plain words" (simpleSyncError (some dropped) (some dropped) 3 ==
    some "Winnow keeps losing its connection to Bitcoin peers. It will keep trying.")
  let mismatch := (Winnow.IO.NetError.filters (.filterHeaderMismatch 7)).description
  check "simple sync error: another failure shows as is" (simpleSyncError (some mismatch) (some dropped) 1 == some mismatch)
  check "simple sync error: a lone failure shows as is" (simpleSyncError (some mismatch) none 0 == some mismatch)
  check "transient: a dropped peer" (isTransientSyncError (.peer (.disconnected "closed")))
  check "transient: a timeout" (isTransientSyncError (.peer .timeout))
  check "transient: peers cooling down" (isTransientSyncError (.filters (.peersCoolingDown 2)))
  check "transient: no peers" (isTransientSyncError (.filters .noPeers))
  check "not transient: a protocol violation" (!isTransientSyncError (.peer (.protocolViolation "bad")))
  check "not transient: a checkpoint mismatch" (!isTransientSyncError (.filters (.checkpointMismatch "split")))
  check "not transient: a corrupt file" (!isTransientSyncError (.other "The file couldn’t be opened because it isn’t in the correct format."))

/-! ## Peer gateways (upstream d2ca878 `PeerGatewayModelTests`) -/

def contains (haystack needle : String) : Bool := (haystack.splitOn needle).length > 1

open Winnow.IO in
def discoveredTor : PeerGatewayConfiguration := { networks := [.tor], torProxy := some { host := "100.75.175.127", port := 9050 } }

/-- A backend core over nothing (no peer, no HTTPS): routing is all these tests drive. -/
def gatewayEnv (discover : Option (IO Winnow.IO.PeerGatewayConfiguration)) : IO Real.Env := do
  let ks := Winnow.inMemoryKeyStore (← IO.mkRef {})
  let env ← Real.Env.new { keyStore := ks, fetch := fun _ => throw (.other "offline"), discoverGateways := discover }
  return env

def relaunch (s : Settings) : Settings :=
  match Lean.Json.parse (Lean.toJson s).compress >>= Lean.fromJson? with
  | .ok s' => s'
  | .error _ => {}

open Winnow.IO in
def peerGatewayModel : IO Unit := do
  -- testAutomaticDefaultAndManualOverridePersistAcrossModes
  let m : Model := { stage := .ready }
  check "gateways: Automatic by default" (m.settings.peerGatewaySettings.mode == "automatic" && (relaunch {}).peerGatewaySettings == {})
  let m := m.loadGatewayDraft
  let config : PeerGatewayConfiguration := { networks := [.i2p], i2pProxy := some { host := "gateway", port := 4447 } }
  let m := (stepSettings (.setGatewayMode 2) m).1
  let m := (stepSettings (.setGatewayNetwork .clearnet false) m).1
  let m := (stepSettings (.setGatewayNetwork .i2p true) m).1
  let m := (stepSettings (.setI2PAddress "gateway:4447") m).1
  let (m, cs) := stepSettings .applyGateways m
  check "gateways: Apply saves the manual gateways" (m.settings.peerGatewaySettings == { mode := "manual", manual := config })
    (reprStr m.settings.peerGatewaySettings)
  check "gateways: Apply saves and reconnects" (cs.length == 2 && cs.any (· matches .reconnect ..) && cs.any (· matches .saveSettings _))
  -- leaving the peers screen and coming back keeps the saved override
  let m := (stepHome .pop { m with routes := [.settings, .network .peers] }).1
  let relaunched := relaunch m.settings
  check "gateways: the manual override survives leaving the screen and a relaunch" (relaunched.peerGatewaySettings == { mode := "manual", manual := config })
  let http ← RoutedHTTPClient.ofGateways (fun _ => throw (.other "offline")) relaunched.peerGatewaySettings.initialActive
  check "gateways: I2P alone makes no HTTP request" (!http.enabled)
  let m := (stepHome (.openNetwork .peers) m).1
  let m := (stepSettings (.setGatewayNetwork .i2p false) m).1
  let (bad, badCmds) := stepSettings .applyGateways m
  check "gateways: an invalid edit does not overwrite the settings"
    (bad.settings.peerGatewaySettings.manual == config && badCmds.isEmpty &&
     bad.settingsDraft.gatewayError == some PeerGatewayConfiguration.Invalid.configuration.description)
  let (typo, _) := stepSettings .applyGateways (stepSettings (.setI2PAddress "gateway") (stepSettings (.setGatewayNetwork .i2p true) m).1).1
  check "gateways: an incomplete address is refused" (typo.settingsDraft.gatewayError == some PeerGatewayConfiguration.Invalid.address.description &&
    typo.settings.peerGatewaySettings.manual == config)
  let (direct, _) := stepSettings .applyGateways (stepSettings (.setGatewayMode 1) m).1
  check "gateways: Direct only persists" ((relaunch direct.settings).peerGatewaySettings.mode == "direct")
  check "gateways: Direct only keeps the manual gateways for later" ((relaunch direct.settings).peerGatewaySettings.manual == config)
  -- testRoutingBannerSaysWhetherPeersSeeTheIPAddress
  let tor : Winnow.Net.PeerEndpoint := { host := "100.75.175.127", port := 9050 }
  let i2p : Winnow.Net.PeerEndpoint := { host := "100.74.30.8", port := 4447 }
  let state (mode : String) (c : PeerGatewayConfiguration) (discovering := false) := PeerRoutingState.current mode c discovering
  check "banner: Tor and I2P" (state "automatic" { networks := [.tor, .i2p], torProxy := some tor, i2pProxy := some i2p } == .overlay true true)
  check "banner: Tor" (state "automatic" { networks := [.tor], torProxy := some tor } == .overlay true false)
  check "banner: Automatic found nothing" (state "automatic" {} == .direct true)
  check "banner: Direct only" (state "direct" {} == .direct false)
  check "banner: mixed" (state "manual" { networks := [.clearnet, .i2p], i2pProxy := some i2p } == .mixed)
  check "banner: checking" (state "automatic" {} true == .checking)
  check "banner: offline" (state "manual" { networks := [] } == .offline)
  check "banner: the private line" ((PeerRoutingState.overlay true true).message == "Private: peers reached through Tor and I2P")
  check "banner: a fallback says the IP is seen" (contains (PeerRoutingState.direct true).message "can see your IP address")
  check "banner: mixed says the IP is seen" (contains PeerRoutingState.mixed.message "can see your IP address")
  let banner := (LeanNative.Html.toWire (.list (homeSections { m with settings := { network := .mainnet } }) : H)).toJson.compress
  check "banner: the home shows it on mainnet, in a few words" (contains banner "peerRoutingBanner" && contains banner "Peers see your IP" &&
    !contains banner "No Tor or I2P gateway found")
  let signet := (LeanNative.Html.toWire (.list (homeSections { m with settings := { network := .signet } }) : H)).toJson.compress
  check "banner: not on signet" (!contains signet "peerRoutingBanner")
  -- testCandidateCountFollowsRoutedNetworks
  let entry : CensusEntry := { host := "8.8.8.8", port := 8333, userAgent := "/Satoshi:30/", startHeight := 900_000 }
  let nets := #[("clearnet", #[entry, entry]), ("tor", #[entry]), ("i2p", #[entry, entry, entry])]
  let catalog : CensusCatalog := { date := "2026-09-28", tip := 900_000, networks := nets }
  check "candidates: clearnet" (Real.candidateCount catalog == "2 candidates")
  check "candidates: I2P" (Real.candidateCount catalog [.i2p] == "3 candidates")
  check "candidates: Tor" (Real.candidateCount catalog [.tor] == "1 candidate")
  check "candidates: all three" (Real.candidateCount catalog [.clearnet, .tor, .i2p] == "6 candidates")
  -- testCorruptSavedSettingsStayOffline
  let corrupt : Settings := match Lean.Json.parse "{\"peerGatewaySettings\":\"broken\"}" >>= Lean.fromJson? with
    | .ok s => s | .error _ => {}
  check "corrupt settings: read as offline" (corrupt.peerGatewaySettings == PeerGatewaySettings.unreadable)
  let env ← gatewayEnv (some (pure discoveredTor))
  env.modify (·.withSettings corrupt)
  Real.preparePeerGateways env
  let c ← env.get
  check "corrupt settings: networking stays offline" (!c.activeGateways.isValid && !c.http.enabled)
  -- testDiscoveredAddressesAreNotPersisted
  let env ← gatewayEnv (some (pure discoveredTor))
  let saved : Settings := {}
  env.modify (·.withSettings saved)
  Real.preparePeerGateways env
  let c ← env.get
  check "discovery: the gateways found are in use" (c.activeGateways == discoveredTor && c.http.proxy == discoveredTor.torProxy)
  check "discovery: nothing is persisted" (!contains (Lean.toJson saved).compress "100.75.175.127")
  let fresh ← gatewayEnv none
  check "discovery: a relaunch starts from clearnet" ((← fresh.get).activeGateways == {})
  -- testDiscoveryIsSharedUntilTheNetworkingGenerationEnds
  let asked ← IO.mkRef 0
  let gate ← IO.mkRef (← IO.Promise.new : IO.Promise PeerGatewayConfiguration)
  let discover : IO PeerGatewayConfiguration := do
    asked.modify (· + 1)
    let p ← gate.get
    return (← IO.wait p.result?).getD {}
  let env ← gatewayEnv (some discover)
  env.modify (·.withSettings {})
  let first ← IO.asTask (Real.preparePeerGateways env)
  while (← asked.get) == 0 do IO.sleep 5
  let second ← IO.asTask (Real.preparePeerGateways env)
  IO.sleep 50
  check "discovery: Checking while it runs" (← env.get).discoveringGateways
  (← gate.get).resolve discoveredTor
  discard <| IO.wait first
  discard <| IO.wait second
  Real.preparePeerGateways env
  check "discovery: one discovery for every caller of a generation" ((← asked.get) == 1 && (← env.get).activeGateways == discoveredTor)
  check "discovery: done" (!(← env.get).discoveringGateways)
  gate.set (← IO.Promise.new)
  Real.stopNetworking env
  let next ← IO.asTask (Real.preparePeerGateways env)
  while (← asked.get) < 2 do IO.sleep 5
  (← gate.get).resolve {}
  discard <| IO.wait next
  check "discovery: the next generation asks again" ((← asked.get) == 2 && (← env.get).activeGateways == {})
  -- testBackgroundAndManualChangeDiscardStaleDiscovery
  for changeMode in [false, true] do
    let gate ← IO.Promise.new
    let started ← IO.mkRef false
    let env ← gatewayEnv (some do started.set true; return (← IO.wait gate.result?).getD {})
    env.modify (·.withSettings {})
    let task ← IO.asTask (Real.preparePeerGateways env)
    while !(← started.get) do IO.sleep 5
    if changeMode then Real.reconnect env { peerGatewaySettings := { mode := "direct" } }
    else Real.stopNetworking env
    gate.resolve discoveredTor
    discard <| IO.wait task
    let c ← env.get
    check s!"stale discovery is dropped ({if changeMode then "mode change" else "background"})"
      (c.activeGateways == {} && !c.discoveringGateways)
  -- AppModel.backgroundRoutingAllowed (BackgroundSyncTests)
  let torGw : Winnow.Net.PeerEndpoint := { host := "100.64.0.1", port := 9050 }
  let i2pGw : Winnow.Net.PeerEndpoint := { host := "100.64.0.2", port := 4447 }
  let overlay : PeerGatewayConfiguration := { networks := [.tor, .i2p], torProxy := some torGw, i2pProxy := some i2pGw }
  check "background: no direct connection after the foreground used gateways" (!backgroundRoutingAllowed "automatic" {} true)
  check "background: through the gateways found" (backgroundRoutingAllowed "automatic" overlay true)
  check "background: direct when the foreground was direct too" (backgroundRoutingAllowed "automatic" {} false)
  check "background: Direct only as chosen" (backgroundRoutingAllowed "direct" {} true)
  check "background: Manual as chosen" (backgroundRoutingAllowed "manual" overlay true)

/-- The home keeps a warning to one short line and explains it in an alert, which leads to the Settings page
with the details (and, for the network, Retry). -/
def homeWarnings : IO Unit := do
  IO.println "home warnings"
  let wire (hs : List H) := (LeanNative.Html.toWire (.list hs : H)).toJson.compress
  let base : Model := { stage := .ready, settings := { network := .mainnet } }
  let err := "No peer answered within 30 s (3 tried)"
  let off : Model := { base with phase := .peerDiscoveryFailed, status := { base.status with lastSyncError := some err } }
  let home := wire (homeSections off)
  check "warnings: offline is one short line" (contains home "homeNetworkWarning" && contains home "Offline")
  -- a row of the balance card, not in its cell, so the shell draws it as tinted words with no box
  let rowIds (s : H) : List String := match s with
    | .section _ _ cs => cs.filterMap fun c => match c with | .identified i _ => some i | _ => none
    | _ => []
  check "warnings: each is a row of the balance card, not in its cell" ((rowIds (balanceSection off)).contains "homeNetworkWarning" &&
    (rowIds (balanceSection base)).contains "peerRoutingBanner" && !contains (wire [balanceSection off]) "syncSummaryText")
  check "warnings: no Retry on the home" (!contains home "retryPeersButton")
  check "warnings: no error text on the home" (!contains home err && !contains home "check your connection")
  let (asked, cmds) := stepHome (.explainWarning .network) off
  check "warnings: a tap explains" (asked.confirm == some (.homeWarning .network) && cmds.isEmpty)
  let alert := wire (confirms asked)
  check "warnings: the alert says what happened and the error" (contains alert "Couldn't reach the Bitcoin network" && contains alert err)
  check "warnings: the alert leads to Settings" (contains alert "warningSettingsButton" && contains alert "Network settings")
  let (sync, _) := stepHome (.warningSettings .network) asked
  check "warnings: Network settings opens Settings, then Sync" (sync.routes == [.settings, .network .sync] && sync.confirm.isNone)
  let page := wire (syncSections sync)
  check "warnings: Sync has Retry and the error" (contains page "retryPeersButton" && contains page "syncLastError" && contains page err)
  check "warnings: Sync's last error is a row that stays" (contains (wire (syncSections base)) "syncLastError")
  let mismatch := "Peer sent a filter header that does not match"
  let failing : Model := { base with phase := .synced, status := { base.status with lastSyncError := some mismatch } }
  let home := wire (homeSections failing)
  check "warnings: a failing sync is a short line too" (contains home "homeNetworkWarning" && contains home "Sync problem" && !contains home mismatch)
  check "warnings: its alert shows the error" (contains (wire (confirms (stepHome (.explainWarning .network) failing).1)) mismatch)
  let dropped := "The connection to the peer was lost"
  let quietStatus : Status := { base.status with lastSyncError := some dropped, transientSyncError := some dropped, transientSyncFailures := 1 }
  let quiet : Model := { base with phase := .synced, status := quietStatus }
  check "warnings: a dropped peer stays quiet" (!contains (wire (homeSections quiet)) "homeNetworkWarning")
  let home := wire (homeSections base)
  check "warnings: routing is a short line" (contains home "peerRoutingBanner" && contains home "Peers see your IP")
  let (routing, _) := stepHome (.explainWarning .routing) base
  let alert := wire (confirms routing)
  check "warnings: routing's alert has the whole message" (contains alert "Peers can see your IP address" &&
    contains alert "No Tor or I2P gateway found" && contains alert "Peers and routing")
  let (peers, _) := stepHome (.warningSettings .routing) routing
  check "warnings: Peers and routing opens Settings, then Peers" (peers.routes == [.settings, .network .peers] && peers.confirm.isNone)

/-- Sync bookkeeping as the screens show it (upstream 66c6a48): the home waits out dropped peers, Settings →
Network → Sync shows every error and says when the chain was last checked. -/
def syncBookkeepingScreens : IO Unit := do
  let dropped := (Winnow.IO.NetError.peer (.disconnected "closed")).description
  let status (n : Nat) : Status := { lastSyncError := some dropped, transientSyncError := some dropped, transientSyncFailures := n }
  let home (n : Nat) := (LeanNative.Html.toWire (.list (homeSections { stage := .ready, status := status n }) : H)).toJson.compress
  let sync (n : Nat) := (LeanNative.Html.toWire (.list (syncSections { stage := .ready, status := status n }) : H)).toJson.compress
  check "home: a dropped peer stays quiet" (!contains (home 1) "closed")
  check "home: the third is a short warning" (contains (home 3) "homeNetworkWarning" && contains (home 3) "Sync problem")
  let explained := (LeanNative.Html.toWire (.list (confirms (stepHome (.explainWarning .network) { stage := .ready, status := status 3 }).1) : H)).toJson.compress
  check "home: tapped, it says so in plain words" (contains explained "Winnow keeps losing its connection to Bitcoin peers.")
  check "Sync screen: every error shows" (contains (sync 1) dropped)
  check "Sync screen: never fully checked" (contains (sync 0) "Chain not fully checked yet")
  let st : Status := { lastCheckedAgo := some (relativeAgo 300) }
  let mm : Model := { stage := .ready, status := st, backgroundRefreshAvailable := false }
  let checked := (LeanNative.Html.toWire (.list (syncSections mm) : H)).toJson.compress
  check "Sync screen: last checked" (contains checked "Chain last checked 5 min ago")
  check "Sync screen: Background App Refresh off" (contains checked "Background App Refresh is off, so Winnow checks the chain only while open.")
  -- Header tip, always-visible Filter scan, Copy sync diagnostics, and Recent peer issues
  let diagModel : Model :=
    { stage := .ready, appVersion := some "0.9.31 (38)",
      phase := .headers 945100 945102,
      status := { syncing := true, tipHeight := 945100, nextScanHeight := 944000, peerCount := 3,
                  lastCheckedAgo := some "5 min", lastSyncError := some "timeout" },
      settingsDraft :=
        { peers := [{ endpoint := "1.2.3.4:8333", userAgent := "/Satoshi:28.0.0/", startHeight := 945102, feeFilter := some 1000, network := .clearnet }],
          peerIssues := [("5.6.7.8:8333", "claimed height 945102 at handshake but delivered no headers past 945100 on 2 passes")] } }
  let diagWire := (LeanNative.Html.toWire (.list (syncSections diagModel) : H)).toJson.compress
  check "Sync screen: shows Header tip and Filter scan even while checking headers"
    (contains diagWire Ids.syncHeaderTip && contains diagWire "945,100 / 945,102" &&
     contains diagWire "block 944,000 of 945,100" && contains diagWire Ids.copySyncDiagnosticsButton)
  let diagText := syncDiagnosticsText diagModel
  check "Sync diagnostics: includes telemetry, peers, and peer issues without wallet secrets"
    (contains diagText "Winnow 0.9.31 (38) (Mainnet)" &&
     contains diagText "Header tip: 945,100 / 945,102" &&
     contains diagText "Filter scan: block 944,000 of 945,100" &&
     contains diagText "1.2.3.4:8333" &&
     contains diagText "5.6.7.8:8333" &&
     !contains diagText "walletID")
  let (_, openSyncCmds) := stepHome (.openNetwork .sync) { stage := .ready }
  check "Sync screen: opening Sync loads connected peers and recent issues for diagnostics"
    (openSyncCmds.any (· matches .connectedPeers _))
  let peersWire := (LeanNative.Html.toWire (.list (peersSections diagModel) : H)).toJson.compress
  check "Peers screen: shows Recent peer issues section when issues exist"
    (contains peersWire Ids.peerIssuesSection && contains peersWire "5.6.7.8:8333" && contains peersWire "on 2 passes")
  check "relative: under a minute" (relativeAgo 59 == "under a minute")
  check "relative: hours and minutes" (relativeAgo (2 * 3600 + 3 * 60) == "2 hr, 3 min")
  check "relative: days" (relativeAgo (3 * 86400 + 4 * 3600) == "3 days, 4 hr" && relativeAgo 86400 == "1 day")

/-! ## Background checks (upstream d2ca878 `BackgroundSyncTests`) -/

/-- Sleeps `ms` unless the task is cancelled first (`Task.sleep` throwing `CancellationError`). -/
def cancellableSleep (ms : Nat) : IO Unit := do
  let deadline := (← IO.monoMsNow) + ms
  while (← IO.monoMsNow) < deadline do
    if ← IO.checkCanceled then return
    IO.sleep 5

def backgroundRuns : IO Unit := do
  -- testCompletionOccursOnceAndCancelsDeadline
  let completions ← IO.mkRef (#[] : Array Bool)
  let cancellations ← IO.mkRef 0
  let run ← Real.BackgroundSyncRun.new 20 (pure true) (cancellations.modify (· + 1)) fun ok => completions.modify (·.push ok)
  run.start; run.start
  discard <| waitUntil 1000 (every := 5) do return !(← completions.get).isEmpty
  run.expire
  IO.sleep 40
  check "background run: completes once, successfully" ((← completions.get) == #[true] && (← cancellations.get) == 0)
  -- testExpirationDrainsWorkAndCannotReportSuccess
  let completions ← IO.mkRef (#[] : Array Bool)
  let cancellations ← IO.mkRef 0
  let started ← IO.mkRef false
  let drained ← IO.mkRef false
  let drainedAtCompletion ← IO.mkRef false
  let run ← Real.BackgroundSyncRun.new 10_000 (do started.set true; cancellableSleep 10_000; drained.set true; return true)
    (cancellations.modify (· + 1)) fun ok => do drainedAtCompletion.set (← drained.get); completions.modify (·.push ok)
  run.start
  discard <| waitUntil 1000 (every := 5) started.get
  run.expire; run.expire
  discard <| waitUntil 1000 (every := 5) do return !(← completions.get).isEmpty
  IO.sleep 20
  check "background run: an expired run drains, then fails once" ((← completions.get) == #[false] && (← drainedAtCompletion.get))
  check "background run: one cancellation" ((← cancellations.get) == 1)
  -- testDeadlineCancelsHungWork
  let completions ← IO.mkRef (#[] : Array Bool)
  let run ← Real.BackgroundSyncRun.new 10 (do cancellableSleep 10_000; return true) (pure ()) fun ok => completions.modify (·.push ok)
  run.start
  check "background run: the deadline cancels hung work" (← waitUntil 1000 (every := 5) do return (← completions.get) == #[false])
  -- testBackgroundAndForegroundCannotOwnNetworkingTogether
  let env ← gatewayEnv none
  env.modify fun c => { c with active := true }
  check "background: refused while the scene is active" (!(← Real.runBackgroundSync env {}) && !(← env.get).backgroundRunning)
  -- testColdBackgroundRunOpensTheWalletScansAndTearsDown (a custom signet, an unreachable peer)
  let vars := [("WINNOW_E2E", "1"), ("WINNOW_E2E_RUN", "background"), ("WINNOW_E2E_ENTROPY", "000102030405060708090a0b0c0d0e0f"),
               ("WINNOW_E2E_PEER", "127.0.0.1:1"), ("WINNOW_E2E_CHALLENGE", "51")]
  match WinnowApp.E2E.resolve (fun k => vars.lookup k) with
  | .active mode =>
    let root ← IO.FS.createTempDir
    let dir := (root / "signet").toString
    IO.FS.createDirAll dir
    let ks := Winnow.inMemoryKeyStore (← IO.mkRef {})
    discard <| (Wallet.create .signet ks (some (System.FilePath.mk dir / "wallet.json")) mode.entropy).run
    let env ← Real.Env.new { keyStore := ks, fetch := fun _ => throw (.other "offline"), networkParams := mode.networkParams, peerCount := 1 }
    let booted ← Real.openWallet env .signet dir
    check "cold background run: boot opens the wallet without networking" ((booted matches .opened _) && (← env.get).stack.isNone)
    let settings : Settings := { network := .signet, signet := { manualPeers := ["127.0.0.1:1"] } }
    let complete ← Real.runBackgroundSync env settings
    let c ← env.get
    check "cold background run: an unreachable peer cannot finish a check" (!complete)
    check "cold background run: no networking left running" (c.stack.isNone && !c.backgroundRunning && !c.active)
    check "cold background run: never fully checked" c.lastCompleteCheck.isNone
    Real.startNetworking env settings
    check "cold background run: the foreground still starts normally" ((← env.get).stack.bind (·.filters)).isSome
    Real.stopNetworking env
    -- the loops see the stop at their next slice, and a pass still running saves the wallet into `root`
    check "cold background run: no loop thread outlives the stop"
      (← waitUntil 5_000 (every := 5) do return (← env.get).liveLoops == 0)
    IO.FS.removeDirAll root
  | _ => check "cold background run: test mode resolves" false
  -- testBackgroundIdentifiersAreDeclaredInBuiltApplication: the Info.plist the app's manifest generates
  let info := WinnowApp.manifest.infoPlist
  let strs (k : String) : List String := match info.getObjValAs? (Array String) k with
    | .ok a => a.toList
    | .error _ => []
  check "background: the identifiers are permitted in Info.plist"
    (strs "BGTaskSchedulerPermittedIdentifiers" ==
      [Real.backgroundRefreshID, Real.backgroundProcessingID, Real.backgroundContinuedWildcard])
  -- Apple requires BGContinuedProcessingTask wildcard identifiers to start with `<CFBundleIdentifier>.`
  let wildcards := (strs "BGTaskSchedulerPermittedIdentifiers").filter (·.endsWith ".*")
  check "background: continued wildcards start with the app's bundleId"
    (!wildcards.isEmpty && wildcards.all (·.startsWith (WinnowApp.manifest.bundleId ++ ".")))
  check "backgroundContinuedID formats per network and serial"
    (Real.backgroundContinuedID .mainnet 1 == Real.backgroundContinuedPrefix ++ "mainnet-1" &&
     Real.backgroundContinuedID .signet 2 == Real.backgroundContinuedPrefix ++ "signet-2" &&
     Real.backgroundContinuedID .regtest 3 == Real.backgroundContinuedPrefix ++ "regtest-3")
  -- BackgroundSyncRun.wait on completed and expired runs, plus scanInBackground/runBackgroundSync guards
  let doneRun ← Real.BackgroundSyncRun.new 5_000 (pure true) (pure ()) (fun _ => pure ())
  doneRun.start
  doneRun.wait
  let expRun ← Real.BackgroundSyncRun.new 10_000 (cancellableSleep 5_000 *> pure true) (pure ()) (fun _ => pure ())
  expRun.start
  expRun.expire
  expRun.wait
  let envIdle ← gatewayEnv none
  check "scanInBackground returns false without wallet/dir" (!(← Real.scanInBackground envIdle))
  envIdle.modify fun c => { c with backgroundRunning := true }
  check "runBackgroundSync refuses when another background check is running" (!(← Real.runBackgroundSync envIdle {}))
  -- RecordsError.isDamaged & writeAtomically direct tests
  check "RecordsError.isDamaged classifies store damage vs other errors"
    ((RecordsError.people .damaged).isDamaged &&
     (RecordsError.labels .damaged).isDamaged &&
     (RecordsError.multisig .damaged).isDamaged &&
     (RecordsError.signers .damaged).isDamaged &&
     !(RecordsError.seal .malformed).isDamaged &&
     !(RecordsError.app .noWallet).isDamaged)
  let atomDir ← IO.FS.createTempDir
  let atomPath := atomDir / "atomic-test.bin"
  let payload := ByteArray.mk #[1, 2, 3, 4]
  RecordsReal.writeAtomically payload atomPath
  RecordsReal.writeAtomically (ByteArray.mk #[5, 6]) atomPath
  check "writeAtomically creates and overwrites target cleanly"
    ((← IO.FS.readBinFile atomPath) == ByteArray.mk #[5, 6])
  IO.FS.removeDirAll atomDir
  -- Phase 3: Real.sameSummary, Real.bumpFee, Real.watchAddress, Real.watchRelay early/offline paths
  let pBase : Preview :=
    { destination := "tb1qbase", amount := 10_000, fee := 200, feeRateMilli := 1_500,
      inputCount := 1, change := some 5_000, locktimeLagsTip := false }
  check "Real.sameSummary detects equality and each differing field"
    (Real.sameSummary pBase pBase &&
     !Real.sameSummary pBase { pBase with destination := "tb1qother" } &&
     !Real.sameSummary pBase { pBase with amount := 10_001 } &&
     !Real.sameSummary pBase { pBase with fee := 201 } &&
     !Real.sameSummary pBase { pBase with feeRateMilli := 2_000 } &&
     !Real.sameSummary pBase { pBase with inputCount := 2 } &&
     !Real.sameSummary pBase { pBase with change := none } &&
     Real.sameSummary pBase { pBase with locktimeLagsTip := true })
  let fakeBump : WinnowApp.FeeBumpPreview := { feeRateMilli := 2_000, fee := 300, change := some 4_900 }
  let envNoStack ← gatewayEnv none
  let bumpNoWallet ← (Real.bumpFee envNoStack "00" fakeBump).toBaseIO
  check "Real.bumpFee fails without open wallet" (bumpNoWallet matches .error _)
  Real.watchAddress envNoStack "tb1qbase" (fun _ _ => pure ())
  Real.watchRelay envNoStack "00" (fun _ => pure ())
  check "background: fetch and processing modes" (strs "UIBackgroundModes" == ["fetch", "processing"])
  check "background: the manifest passes LeanNative's capability checks" WinnowApp.manifest.problems.isEmpty
  -- the Model: a cold launch's task waits for boot, boot without a scene starts no networking
  let (m, cs) := onHost (.bgtask Real.backgroundRefreshID "refresh" (some 3)) ({} : Model)
  check "Model: a task launched during boot waits for the wallet" (m.pendingBackgroundTasks == [(Real.backgroundRefreshID, "refresh", some 3)] &&
    cs.any (· matches .scheduleBackgroundTasks) && !cs.any (· matches .runBackgroundTask ..))
  let (m, cs) := onHost (.booted 0 (.opened "w")) m
  check "Model: boot runs it, without foreground networking" (cs.any (· matches .runBackgroundTask ..) &&
    !cs.any (· matches .startNetworking ..) && m.pendingBackgroundTasks.isEmpty)
  let (m, cs) := onHost (.scene true) m
  check "Model: the scene becoming active starts networking" (cs.any (· matches .startNetworking ..) && m.active)
  let (_, cs) := onHost (.scene false) m
  check "Model: backgrounding asks for the next checks" (cs.any (· matches .scheduleBackgroundTasks) && cs.any (· matches .stopNetworking))
  let (_, cs) := onHost (.bgtaskExpired Real.backgroundRefreshID "refresh" (some 3)) m
  check "Model: an expired task is cancelled" (cs.any (· matches .expireBackgroundTask _ (some 3)))
  -- #92's findings 6 and 14: the wallet opens, or is deleted, whether or not the scene left the front meanwhile
  let (away, _) := onHost (.scene false) ({} : Model)
  let (opened, _) := onHost (.booted 0 (.opened "w")) away
  check "Model: a wallet that opened while the app was away is open" (opened.stage == .ready && opened.walletID == some "w")
    s!"{repr opened.stage}"
  let (back, cs) := onHost (.scene true) opened
  check "Model: and coming back starts its networking" (back.stage == .ready && cs.any (· matches .startNetworking ..))
  let (switched, _) := (away.switchNetwork (if away.settings.network == .mainnet then .signet else .mainnet))
  let (stale, _) := onHost (.booted 0 (.opened "w")) switched
  check "Model: another network's wallet opening is still dropped" (stale.stage == .loading && stale.walletID.isNone)
  let (failed, _) := onHost (.failed 0 (.wallet .openWallet) false "The wallet's folder could not be made.") away
  check "Model: a wallet that could not be opened says so, with Retry"
    (failed.stage == .storageDamaged "The wallet's folder could not be made." && contains (LeanNative.Html.toWire (view failed)).toJson.compress "Retry")
  let ready : Model := { stage := .ready, active := true, walletID := some "w" }
  let (leaving, _) := onHost (.scene false) ready
  let (deleted, cs) := onHost (.deleted 0) leaving
  check "Model: a wallet deleted while the app was away is gone, and what is kept now is asked for"
    (deleted.stage == .loading && deleted.walletID.isNone && cs.any (· matches .openWallet _ _ false))
  let (none', _) := onHost (.booted deleted.generation .missing) deleted
  check "Model: with no wallet left, onboarding" (none'.stage == .onboarding && none'.walletID.isNone)
  let (kept, _) := onHost (.walletPlace deleted.generation "1" [{ id := "x", slot := "1", active := true }]) deleted
  let (other, _) := onHost (.booted deleted.generation (.opened "x")) kept
  check "Model: with another wallet kept, that one opens" (other.stage == .ready && other.walletID == some "x" && other.slot == "1")
  -- #92's finding 15: an amount there cannot be is refused, not wrapped into another one
  check "amount: every satoshi there is, is an amount"
    ((← (Real.satsOf Real.maximumMoney).toBaseIO).toOption == some (Int64.ofNat Real.maximumMoney))
  check "amount: one more is refused" (match ← (Real.satsOf (Real.maximumMoney + 1)).toBaseIO with
    | .error e => toString e == Real.amountTooLargeText | .ok _ => false)
  check "amount: 2⁶⁴ + 10,000 is refused, where it once read as 10,000" (match ← (Real.satsOf (2 ^ 64 + 10_000)).toBaseIO with
    | .error _ => true | .ok _ => false)
  check "system events: a launched task" ((system (Lean.Json.mkObj [("bgtask", Lean.Json.mkObj [("id", "x"), ("kind", "processing")])])) matches some (.bgtask "x" "processing" none))
  check "system events: an expired task" ((system (Lean.Json.mkObj [("bgtaskExpired", Lean.Json.mkObj [("id", "x"), ("kind", "refresh")])])) matches some (.bgtaskExpired "x" "refresh" none))
  check "system events: a launch's tag" ((system (Lean.Json.mkObj [("bgtask", Lean.Json.mkObj [("id", "x"), ("kind", "processing"), ("tag", Lean.toJson (7 : Nat))])])) matches some (.bgtask "x" "processing" (some 7)))
  check "system events: an expiry's tag" ((system (Lean.Json.mkObj [("bgtaskExpired", Lean.Json.mkObj [("id", "x"), ("kind", "refresh"), ("tag", Lean.toJson (7 : Nat))])])) matches some (.bgtaskExpired "x" "refresh" (some 7)))

/-! ## The screens, as a person uses them (#35, #44, #45, #48, #64)

Each flow sends the Model what a tap sends (`step`), runs the commands through the app's own `perform`
against a backend (the real one over a wallet opened from disk with no network, or a stub that records what
reaches it), hands every answer back through `onHost`, and reads the screen as the shell receives it. The
journeys open these screens; these flows use their controls. -/

/-- The shell's side of `perform`: the answers it posts, collected; `auth` and the other capabilities say yes,
`clipboard.get` answers `clipboard`; the fire-and-forget capabilities (`clipboard.set`, `open`) asked for,
with their arguments, in `caps`. -/
structure Shell where
  posted : IO.Ref (Array Host)
  clipboard : IO.Ref String
  caps : IO.Ref (Array (String × Lean.Json))
  /-- What was asked of the shell and waited for (`ask`), with its arguments. -/
  asks : IO.Ref (Array (String × Lean.Json))
  /-- What `auth` answers; yes unless a case says otherwise. -/
  auth : IO.Ref Lean.Json

def Shell.new : IO Shell := do
  return { posted := ← IO.mkRef #[], clipboard := ← IO.mkRef "", caps := ← IO.mkRef #[], asks := ← IO.mkRef #[],
           auth := ← IO.mkRef (Lean.Json.mkObj [("ok", Lean.Json.bool true)]) }

def Shell.fx (s : Shell) : LeanNative.Native.Effects Host where
  post h := s.posted.modify (·.push h)
  cap name args _ := s.caps.modify (·.push (name, args))
  ask name args := do
    s.asks.modify (·.push (name, args))
    if name == "clipboard.get" then return Task.pure (Lean.Json.mkObj [("text", Lean.Json.str (← s.clipboard.get))])
    if name == "auth" then return Task.pure (← s.auth.get)
    return Task.pure (Lean.Json.mkObj [("ok", Lean.Json.bool true)])

/-- How many answers `perform` posts for the commands these flows run; none for the ones they leave out
(networking, the mempool window, timers, the clipboard's copy, the journal). -/
def answersTo : Cmd → Option Nat
  | .refresh .. => some 3
  | .saveSettings .. | .removeExport .. => some 0
  | .records .. | .receiveAddress .. | .setReceiveLabel .. | .personCard .. | .parsePaste .. | .addPerson .. | .editPerson ..
  | .updateRecipient .. | .labelSender .. | .removeSenderLabel .. | .catalogStatus .. | .connectedPeers ..
  | .resetPeers .. | .reconnect .. | .loadPaymentDetails .. | .exportBundle .. | .revealPhrase ..
  | .deleteWallet .. | .paste .. | .importWallet .. => some 1
  | _ => none

/-- Runs `cs` through `perform`, each answer back through `onHost` and whatever that asks for in turn; the
model after, and the commands left out, in order. -/
partial def Shell.run (s : Shell) (m : Model) (cs : List Cmd) : IO (Model × List Cmd) := do
  let mut m := m
  let mut left : List Cmd := []
  for c in cs do
    match answersTo c with
    | none => left := left ++ [c]
    | some n =>
      let before := (← s.posted.get).size
      WinnowApp.perform c s.fx
      unless ← waitUntil 10_000 (every := 2) (do return (← s.posted.get).size ≥ before + n) do
        throw (IO.userError "a command posted no answer within 10 s")
      for h in (← s.posted.get).extract before (before + n) do
        let (m', cs') := onHost h m
        let (m', rest) ← s.run m' cs'
        m := m'
        left := left ++ rest
  return (m, left)

/-- A tap: `step`, then its commands as `run` runs them. -/
def Shell.tap (s : Shell) (msg : Msg) (m : Model) : IO (Model × List Cmd) := do
  let (m, cs) := step msg m
  s.run m cs

/-- The whole tree as the shell receives it. -/
def rendered (m : Model) : String := (LeanNative.Html.toWire (view m)).toJson.compress
def renderedH (h : H) : String := (LeanNative.Html.toWire h).toJson.compress

/-- A ready regtest phone on the real backend: `Wallet.create` in its own directory, opened by
`Backend.realWithMultisig` with no network (no peer, no HTTPS). -/
def screenPhone (root : System.FilePath) (name : String) (entropy : UInt8) : IO (Backend × String) := do
  let dir := root / name / "regtest"
  IO.FS.createDirAll dir
  let ks := inMemoryKeyStore (← IO.mkRef {})
  match ← (Wallet.create network ks (some (dir / "wallet.json")) (entropy := some (ByteArray.mk (Array.replicate 16 entropy)))).run with
  | .ok _ => pure ()
  | .error e => throw (IO.userError s!"Wallet.create: {e.name}")
  let (backend, _, _) ← Backend.realWithMultisig { keyStore := ks, fetch := fun _ => throw (.other "offline") }
  match ← backend.openWallet .regtest dir.toString with
  | .opened id => return (backend, id)
  | _ => throw (IO.userError s!"{name}: the wallet did not open")

/-- The model of a ready phone on regtest, in the foreground. -/
def readyModel (walletID : String) : Model :=
  { stage := .ready, active := true, walletID := some walletID,
    settings := { network := .regtest } }

/-! ### Model.fail (#48) -/

/-- Every busy flag a failure can clear, by name, as one model has them all set. -/
def busyFlags : List (String × (Model → Bool)) :=
  [ ("onboarding.busy", (·.onboarding.busy)), ("onboarding.restoring", (·.onboarding.restoring))
  , ("receive.changing", (·.receive.changing)), ("labelEditor.saving", (·.labelEditor.saving))
  , ("send.reviewing", (·.send.reviewing)), ("send.sending", (·.send.sending))
  , ("spendingInFlight", (·.spendingInFlight)), ("settingsDraft.resettingPeers", (·.settingsDraft.resettingPeers))
  , ("payment.loading", (·.payment.loading)), ("feeBump.bumping", (·.feeBump.bumping))
  , ("exportState.busy", (·.exportState.busy)), ("reveal.revealing", (·.reveal.revealing))
  , ("person.saving", (·.person.saving)), ("person.inferring", (·.person.inferring))
  , ("multisigAdd.saving", (·.multisigAdd.saving)), ("multisigBuild.creating", (·.multisigBuild.creating))
  , ("ledgerPair.pairing", (·.ledgerPair.pairing)), ("signerKeys.saving", (·.signerKeys.saving))
  , ("collect.busy", (·.collect.busy)), ("shareCard.making", (·.shareCard.making)) ]

/-- A phone with every screen in the middle of something: each busy flag set, the export holding a file, a
card being made, the collection step at epoch 4. -/
def busyModel : Model :=
  { readyModel "w" with
    onboarding := { busy := true, restoring := true }
    receive := { address := "bcrt1q", changing := true }
    labelEditor := { address := "bcrt1q", draft := "Rent", saving := true }
    send := { reviewing := true, sending := true, resolvedRateMilli := some 2_000 }
    spendingInFlight := true
    settingsDraft := { resettingPeers := true }
    payment := { loading := true }
    feeBump := { txid := "tt", bumping := true }
    exportState := { busy := true, file := some "/tmp/winnow-export-x/w.json" }
    reveal := { revealing := true }
    person := { saving := true, inferring := true }
    shareCard := { making := true }
    multisigAdd := { saving := true }
    multisigBuild := { creating := true }
    ledgerPair := { pairing := true }
    signerKeys := { saving := true }
    collect := { busy := true, epoch := 4 } }

/-- `Model.fail` for each target it handles: where the message lands, and the busy flags it clears; every
other flag stays set (a failure touches only the screen that asked). -/
def failTable : List (FailTarget × Bool × (Model → Bool) × List String) :=
  let boom := some "boom"
  [ (.wallet .create, false, (·.onboarding.error == boom), ["onboarding.busy"])
  , (.wallet .importWallet, false, (·.onboarding.error == boom), ["onboarding.busy"])
  , (.wallet .create, true, (·.onboarding.error.isNone), ["onboarding.busy"])
  , (.wallet .importWallet, true, (·.onboarding.error.isNone), ["onboarding.busy"])
  , (.wallet .cloudRestore, false, (·.onboarding.restoreError == boom), ["onboarding.restoring"])
  , (.wallet .cloudRestore, true, (·.onboarding.restoreError.isNone), ["onboarding.restoring"])
  , (.wallet .delete, false, (·.confirm == some (.deleteFailed "boom")), [])
  , (.wallet .openWallet, false, (·.status.lastSyncError == boom), [])
  , (.wallet .unlock, false, (·.status.lastSyncError == boom), [])
  , (.wallet .unlock, true, (·.status.lastSyncError.isNone), [])
  , (.wallet .sync, false, (·.status.lastSyncError == boom), [])
  , (.payment .receive, false, (·.receive.error == boom), ["receive.changing"])
  , (.payment .label, false, (·.labelEditor.error == boom), ["labelEditor.saving"])
  , (.payment .send, false, (·.send.error == boom), ["send.reviewing", "send.sending", "spendingInFlight"])
  -- a declined Face ID before a payment: the prompt's text shows, and Send is free again
  , (.payment .send, true, (·.send.error == boom), ["send.reviewing", "send.sending", "spendingInFlight"])
  , (.payment .rate, false, (·.send.resolvedRateMilli.isNone), [])
  , (.payment .payment, false, (·.payment.error == boom), ["payment.loading"])
  , (.payment .feeBump, false, (·.feeBump.error == boom), ["feeBump.bumping", "spendingInFlight"])
  , (.payment .feeBump, true, (·.feeBump.error == boom), ["feeBump.bumping", "spendingInFlight"])
  , (.settings .peers, false, (·.settingsDraft.error == boom), ["settingsDraft.resettingPeers"])
  , (.settings .catalog, false, (·.settingsDraft.catalog.isNone), [])
  , (.settings .exportBundle, false, fun m => m.exportState.error == boom && m.exportState.file.isNone, ["exportState.busy"])
  , (.settings .exportBundle, true, (·.exportState.error.isNone), ["exportState.busy"])
  , (.settings .reveal, false, (·.reveal.error == boom), ["reveal.revealing"])
  , (.settings .reveal, true, (·.reveal.error.isNone), ["reveal.revealing"])
  , (.people .personCard, false, (·.shareCard.error == boom), ["shareCard.making"])
  -- a declined Face ID before a card is made: nothing is said, and the button is free again
  , (.people .personCard, true, (·.shareCard.error.isNone), ["shareCard.making"])
  , (.people .person, false, (·.person.error == boom), ["person.saving", "person.inferring"])
  , (.people .recipients, false, (·.recipientsError == boom), [])
  , (.multisig .overview, false, (·.status.lastSyncError.isNone), [])
  , (.multisig .add, false, (·.multisigAdd.error == boom), ["multisigAdd.saving"])
  , (.multisig .build, false, (·.multisigBuild.error == boom), ["multisigBuild.creating"])
  , (.multisig .account, false, (·.multisigAccountError == boom), [])
  , (.multisig .spend, false, (·.payment.error == boom), [])
  , (.multisig .ledgerPair, false, (·.ledgerPair.error == boom), ["ledgerPair.pairing"])
  , (.multisig .signerKeys, false, (·.signerKeys.error == boom), ["signerKeys.saving"])
  , (.multisig .signer, false, (·.signerDetail.error == boom), [])
  , (.multisig (.collect 4), false, (·.collect.error == boom), ["collect.busy", "spendingInFlight"])
  , (.multisig (.collect 4), true, (·.collect.error.isNone), ["collect.busy", "spendingInFlight"])
  -- an earlier collection run's failure: dropped, though the spend it held is free again
  , (.multisig (.collect 3), false, (·.collect.error.isNone), ["spendingInFlight"]) ]

/-- #48: each failure reaches the screen that asked and clears that screen's busy flags, through `onHost`
as `perform` posts it; the screens then show it. -/
def failuresReachTheirScreens : IO Unit := do
  for (name, flag) in busyFlags do
    check s!"fail: the busy model has {name} set" (flag busyModel)
  for (target, cancelled, landed, clears) in failTable do
    let label := s!"{reprStr target}{if cancelled then ".cancelled" else ""}"
    let (m, cs) := onHost (.failed busyModel.generation target cancelled "boom") busyModel
    check s!"fail {label}: the message lands on its screen" (landed m && cs.isEmpty)
    for (name, flag) in busyFlags do
      if clears.contains name then check s!"fail {label}: clears {name}" (!flag m)
      else check s!"fail {label}: leaves {name}" (flag m)
  -- a cancelled restore leaves an earlier message alone
  let restoring := { busyModel with onboarding := { busyModel.onboarding with restoreError := some "earlier" } }
  check "fail cloudRestore.cancelled: keeps what the restore said"
    ((restoring.fail (.wallet .cloudRestore) true "x").onboarding.restoreError == some "earlier")
  -- the collection step only while the scene is active
  let away := (busyModel.fail (.multisig (.collect 4)) false "boom")
  check "fail collect: the active scene's run shows" (away.collect.error == some "boom")
  let background := { busyModel with active := false }.fail (.multisig (.collect 4)) false "boom"
  check "fail collect: not while in the background" (background.collect.busy && background.collect.error.isNone && !background.spendingInFlight)
  -- another wallet's failure is dropped (a network switch since)
  let (switched, _) := busyModel.switchNetwork .mainnet
  let (other, _) := onHost (.failed busyModel.generation (.payment .send) false "boom") { switched with send := { sending := true } }
  check "fail: another wallet's failure is dropped" (other.send.sending && other.send.error.isNone)
  -- the screens show it: Send's review, the fee bump, Pair a Ledger, the label editor
  let sending := { readyModel "w" with send := { sending := true, preview := none }, spendingInFlight := true }.present .send
  let (m, _) := onHost (.failed 0 (.payment .send) false Real.AppError.sendReviewChanged.text) sending
  check "fail send: Send shows why, and can be used again" (contains (rendered m) Real.AppError.sendReviewChanged.text && !m.send.sending)
  let replacedRow : HistoryItem := { txid := "tt", height := 0, received := 0, spent := 1000, fee := some 100, replacedBy := some "rr" }
  let sent := { (readyModel "w") with send := { sentTxid := some "tt" } }.present .send
  check "a sent payment waits for its confirmation" (contains (rendered sent) "Waiting for confirmation")
  let gone := { sent with status := { sent.status with history := [replacedRow] } }
  check "Send stops waiting once the payment is replaced" (contains (rendered gone) "Replaced" && !contains (rendered gone) "Waiting for confirmation")
  let opened := { sent with expanded := ["send.details"] }
  check "a new payment starts with its details closed" (!(stepSend .newPayment opened).1.isExpanded "send.details")
  check "so does Send opened again" (!(opened.closeSheet .send).1.isExpanded "send.details")
  let review : WinnowApp.FeeBumpPreview := { feeRateMilli := 5_000, fee := 700, change := some 9_300 }
  let bump : FeeBump := { txid := "tt", bumping := true, targetText := "5", reviewed := some ("5", review) }
  let bumping := { readyModel "w" with feeBump := bump }.present .feeBump
  check "fail feeBump: the sheet says Signing while it runs" (contains (rendered bumping) "Signing & broadcasting")
  let (m, _) := onHost (.failed 0 (.payment .feeBump) false "The replacement was refused") bumping
  check "fail feeBump: the sheet shows it and offers Sign & replace again"
    (contains (rendered m) "The replacement was refused" && contains (rendered m) "Sign & replace" && !m.spendingInFlight)
  let pairing := { readyModel "w" with routes := [.ledgerPair], ledgerPair := { name := "Nano X", pairing := true } }
  let (m, _) := onHost (.failed 0 (.multisig .ledgerPair) false "No Ledger answered") pairing
  check "fail ledgerPair: Pair a Ledger shows it, Pair again" (contains (rendered m) "No Ledger answered" && contains (rendered m) "\"Pair\"")
  let syncErr := (onHost (.failed 0 (.wallet .sync) false "the sync line") (readyModel "w")).1
  check "fail: a sync failure is a sync problem on the home" (contains (rendered syncErr) "Sync problem")
  check "fail: and shows on the Sync screen" (contains (LeanNative.Html.toWire (.list (syncSections syncErr) : H)).toJson.compress "the sync line")

/-! ### Settings (#44) -/

/-- A backend that answers the Settings screen and records what reached it. -/
def recordingBackend (calls : IO.Ref (Array String)) (failReset : IO.Ref Bool) : Backend :=
  let note (s : String) : IO Unit := calls.modify (·.push s)
  { Backend.pending with
    reconnect := fun s => note s!"reconnect {s.scoped.manualPeers} genesis={s.verifyFromGenesis}"
    snapshot := do note "snapshot"; return ({}, .synced)
    records := do note "records"; return {}
    multisigOverview := do note "multisigOverview"; return {}
    catalogStatus := do note "catalogStatus"; return "Observed 2026-09-28: 412 candidates."
    connectedPeers := do
      note "connectedPeers"
      return [{ endpoint := "203.0.113.7:8333", userAgent := "/Satoshi:30.0/", startHeight := 900_000, feeFilter := some 1_000 }]
    resetPeers := do
      note "resetPeers"
      if ← failReset.get then throw (IO.userError "The peer store could not be cleared.")
    updateSettings := fun s => note s!"updateSettings {s.scoped.manualPeers} {reprStr s.scoped.explorer} {s.scoped.esploraURL} genesis={s.verifyFromGenesis}"
    exportBundle := fun withPhrase => do note s!"exportBundle {withPhrase}"; return "{\"version\":1}"
    revealMnemonic := do note "revealMnemonic"; return ["abandon", "ability", "able"]
    deleteWallet := note "deleteWallet" }

/-- #44: Settings' controls, each through `perform` to the backend, each change saved (the command, the
settings file and the backend's copy) and shown. -/
def settingsScreen (root : System.FilePath) : IO Unit := do
  let calls ← IO.mkRef (#[] : Array String)
  let failReset ← IO.mkRef false
  backendRef.set (recordingBackend calls failReset)
  rootDir.set (root / "settings").toString
  IO.FS.createDirAll (root / "settings")
  tmpDir.set (root / "tmp").toString
  IO.FS.createDirAll (root / "tmp")
  let sh ← Shell.new
  let called (s : String) : IO Bool := do return (← calls.get).contains s
  let savedFile : IO Settings := do
    match Lean.Json.parse (← IO.FS.readFile (root / "settings" / "settings.json")) >>= Lean.fromJson? with
    | .ok s => return s
    | .error _ => return {}
  let saved (f : Settings → Bool) : IO Bool := waitUntil 5_000 (every := 5) do
    try return f (← savedFile) catch _ => return false
  let tap (msg : SettingsMsg) (m : Model) := sh.tap (.settings msg) m
  -- Settings → Network → Peers and routing: the census line and the connected peers load as it appears
  let m := readyModel "w"
  let (m, _) ← sh.tap (.home .openSettings) m
  let (m, _) ← sh.tap (.home (.openNetwork .peers)) m
  check "settings: the peers page asks for the peers and the census line" ((← called "connectedPeers") && (← called "catalogStatus"))
  check "settings: both shown" (contains (rendered m) "Observed 2026-09-28: 412 candidates." && contains (rendered m) "203.0.113.7:8333" &&
    contains (rendered m) "floor 1000 sat/kvB")
  -- a manual peer: added, saved and shown; the same one again changes nothing; nonsense is refused
  let (m, _) ← tap (.setManualPeer " 127.0.0.1:18444 ") m
  let (m, left) ← tap .addManualPeer m
  check "manual peer: added to this network's settings" (m.settings.manualPeers == ["127.0.0.1:18444"] && m.settingsDraft.manualPeer.isEmpty && left.isEmpty)
  check "manual peer: saved to settings.json" (← saved (·.regtest.manualPeers == ["127.0.0.1:18444"]))
  check "manual peer: the backend has it" (← waitUntil 2_000 (every := 5) (called "updateSettings [127.0.0.1:18444] WinnowApp.Explorer.blockstream  genesis=false"))
  check "manual peer: shown with Remove" (contains (rendered m) "127.0.0.1:18444" && contains (rendered m) "Remove")
  check "manual peer: only this network's" (m.settings.mainnet.manualPeers.isEmpty && m.settings.signet.manualPeers.isEmpty)
  let (again, cs) := stepSettings .addManualPeer (stepSettings (.setManualPeer "127.0.0.1:18444") m).1
  check "manual peer: the same one again is not saved twice" (cs.isEmpty && again.settings.manualPeers.length == 1)
  let (bad, cs) := stepSettings .addManualPeer (stepSettings (.setManualPeer "no port here") m).1
  check "manual peer: nonsense is refused on the screen" (cs.isEmpty && contains (rendered bad) "use host:port.")
  let (m, _) ← tap (.setManualPeer "peer.example:8333") m
  let (m, _) ← tap .addManualPeer m
  check "manual peer: a second one" (m.settings.manualPeers == ["127.0.0.1:18444", "peer.example:8333"])
  let (m, _) ← tap (.removeManualPeer 0) m
  check "manual peer: removed" (m.settings.manualPeers == ["peer.example:8333"] && !contains (rendered m) "127.0.0.1:18444")
  check "manual peer: the removal is saved" (← saved (·.regtest.manualPeers == ["peer.example:8333"])) (← IO.FS.readFile (root / "settings" / "settings.json"))
  -- Reconnect: the backend rebuilds networking with the settings as saved
  let (m, _) ← tap .reconnect m
  check "Reconnect peers: reaches the backend with the saved peers" (← called "reconnect [peer.example:8333] genesis=false")
  -- Verify from genesis: saved, journaled, and networking rebuilt with it
  let (m', cs) := stepSettings (.setVerifyFromGenesis true) m
  check "Verify from genesis: saves, journals and reconnects"
    (cs.any (· matches .saveSettings _) && cs.any (· matches .journal "setting.verifyFromGenesis" _) && cs.any (· matches .reconnect ..))
  let (m, _) ← sh.run m' cs
  check "Verify from genesis: the backend reconnects from block 0" (← called "reconnect [peer.example:8333] genesis=true")
  check "Verify from genesis: saved" (← saved (·.verifyFromGenesis))
  let onPage (page : NetworkPage) (m : Model) := rendered { m with routes := [.settings, .network page] }
  check "Verify from genesis: the toggle is on, with its note" (contains (onPage .verification m) "Turning this off later keeps the chain you already verified.")
  check "Verify from genesis: the same value again does nothing" (stepSettings (.setVerifyFromGenesis true) m).2.isEmpty
  -- the explorer: a preset, then a custom Esplora URL
  let (m, _) ← tap (.setExplorer 1) m
  check "explorer: mempool.space saved" (m.settings.scoped.explorer == .mempool)
  check "explorer: no URL field for a preset" (!contains (onPage .explorer m) "Esplora-compatible website URL")
  let (m, _) ← tap (.setExplorer 2) m
  check "explorer: Custom shows the URL field" (contains (onPage .explorer m) "Esplora-compatible website URL")
  let (m, _) ← tap (.setEsploraURL "  https://esplora.example/api  ") m
  check "explorer: the custom URL is saved trimmed" (m.settings.scoped.esploraURL == "https://esplora.example/api" && m.settings.scoped.explorer == .custom)
  check "explorer: saved to settings.json" (← saved fun s => s.regtest.explorer == .custom && s.regtest.esploraURL == "https://esplora.example/api")
  check "explorer: the backend has it"
    (← waitUntil 2_000 (every := 5) (called "updateSettings [peer.example:8333] WinnowApp.Explorer.custom https://esplora.example/api genesis=true"))
  check "explorer: Selected shows it" (contains (onPage .explorer m) "Selected: https://esplora.example/api")
  check "explorer: a relaunch keeps it" ((relaunch m.settings).esploraBaseURL == "https://esplora.example/api")
  check "explorer: an index past the list does nothing" (stepSettings (.setExplorer 7) m).2.isEmpty
  -- what the explorer trades away, and the design papers
  let (side, _) := stepSettings .openReadSide m
  check "read side: the sheet" (side.topSheet == some .readSide && contains (renderedH (readSideSheet [])) "read-side.html" &&
    contains (rendered side) "The Read Side")
  let (closed, _) := step .closeSheet side
  check "read side: closes" closed.sheets.isEmpty
  let (papers, _) := stepSettings .openPapers m
  let list := renderedH (papersSheet papers [])
  check "papers: the four" (contains list "A phone wallet" && contains list "The read side" && contains list "The write side" && contains list "Import")
  let (paper, _) := stepSettings (.openPaper 2) papers
  check "papers: one opens as its page" (contains (renderedH (papersSheet paper [])) "write-side.html" && contains (rendered paper) "write-side.html")
  let (back, _) := stepSettings .closePaper paper
  check "papers: back to the list" (back.paper.isNone && contains (renderedH (papersSheet back [])) "A phone wallet")
  let (done, _) := step .closeSheet paper
  check "papers: closing forgets the page" (done.sheets.isEmpty && done.paper.isNone)
  -- Refresh and Reset peers
  calls.set #[]
  let (m, _) ← tap .refreshPeers m
  check "Refresh: asks the backend for the peers" (← called "connectedPeers")
  let (asking, _) ← tap .askResetPeers m
  check "Reset peers: asks first" (asking.confirm == some .resetPeers && contains (rendered asking) "Reset and shuffle peers?")
  let (resetting, cs) := stepSettings .resetPeers asking
  check "Reset peers: Resetting… while it runs" (resetting.settingsDraft.resettingPeers && contains (rendered resetting) "Resetting" &&
    resetting.confirm.isNone && cs.any (· matches .resetPeers _))
  let (m, _) ← sh.run resetting cs
  check "Reset peers: the backend resets, then the peers and the wallet are read again"
    ((← called "resetPeers") && (← called "connectedPeers") && (← called "snapshot") && !m.settingsDraft.resettingPeers)
  check "Reset peers: the button is back" (contains (rendered m) "Reset and shuffle peers" && !contains (rendered m) "Resetting")
  failReset.set true
  let (failed, _) ← sh.run (stepSettings .resetPeers m).1 (stepSettings .resetPeers m).2
  check "Reset peers: a failure shows and frees the button"
    (!failed.settingsDraft.resettingPeers && contains (rendered failed) "The peer store could not be cleared.")
  -- Check gateways and reconnect: not while a discovery runs
  check "Check gateways: reconnects" ((stepSettings .checkGateways m).2.any (· matches .reconnect ..))
  check "Check gateways: not while discovering" (stepSettings .checkGateways { m with status := { discoveringGateways := true } }).2.isEmpty
  -- the backup file and the recovery phrase reach the backend too (performSettings' other commands)
  let (exp, _) := stepBackup .openExport m
  let (exp, cs) := stepBackup .createExport exp
  let (exp, _) ← sh.run exp cs
  check "export: the backend's bundle, staged as a file" ((← called "exportBundle false") && exp.exportState.file.isSome && !exp.exportState.busy)
  let file := exp.exportState.file.getD ""
  check "export: the file holds the bundle" ((← IO.FS.readFile file) == "{\"version\":1}")
  let (gone, cs) := step .closeSheet exp
  let (_, _) ← sh.run gone cs
  check "export: closing the sheet removes the staged file" (← waitUntil 2_000 (every := 5) do return !(← System.FilePath.pathExists file))
  let (rev, _) ← sh.tap (.backup .reveal) m
  check "reveal: the words, after device authentication" ((← called "revealMnemonic") && rev.reveal.words == ["abandon", "ability", "able"] &&
    rev.topSheet == some .revealPhrase)
  -- Delete wallet: asks, then the backend deletes and onboarding comes back
  let (asking, _) ← tap .askDelete m
  check "delete: asks first" (asking.confirm == some .deleteWallet && contains (rendered asking) "Delete this wallet?")
  let (deleted, _) ← tap .deleteWallet asking
  check "delete: the backend deletes, and the wallet is no longer shown" ((← called "deleteWallet") && deleted.stage != .ready && deleted.walletID.isNone)
    s!"{repr deleted.stage}"
  backendRef.set Backend.pending

/-! ### Receive (#45) -/

/-- #45: Receive's controls on the real backend: New address, a label saved, renamed and removed, and the
share card with a display name. -/
def receiveScreen (sh : Shell) (backend : Backend) (walletID : String) : IO Unit := do
  let m := readyModel walletID
  let (m, left) ← sh.tap .openReceive m
  let first := m.receive.address
  check "receive: the first address" (first.startsWith "bcrt1p" && m.topSheet == some .receive) first
  check "receive: the mempool window opens on it" (left.any fun | .watchAddress _ a => a == first | _ => false)
  check "receive: one page, the address at once and nothing asked first"
    (!m.receive.editingLabel && contains (rendered m) first && contains (rendered m) "Label this address" &&
     !contains (rendered m) "Who is this address for?" && contains (rendered m) "From one person")
  check "receive: no button to a second sheet for a card" (!contains (rendered m) "Make a card")
  let (asking, _) ← sh.tap (.receive .editLabel) m
  check "label: asked for only when wanted, and Cancel goes back to the address"
    (asking.receive.editingLabel && contains (rendered asking) "Who is this address for?" && contains (rendered asking) "Cancel" &&
     !contains (rendered asking) "Skip for now" &&
     (let back := (stepReceive .finishLabel asking).1; !back.receive.editingLabel && contains (rendered back) first))
  -- New address
  let (m, left) ← sh.tap (.receive .freshAddress) m
  let second := m.receive.address
  check "New address: differs from the first" (second.startsWith "bcrt1p" && second != first) second
  check "New address: the mempool window moves to it"
    (left.any (· matches .stopWatchingAddress) && left.any fun | .watchAddress _ a => a == second | _ => false)
  check "New address: shown at once too" (!m.receive.editingLabel && !m.receive.changing && m.labelEditor.address == second &&
    contains (rendered m) second)
  -- label it
  let (m, _) ← sh.tap (.receive .editLabel) m
  let (m, _) ← sh.tap (.receive (.setLabelDraft "  Alice, invoice 12 ")) m
  let (m, _) ← sh.tap (.receive .saveLabel) m
  check "label: saved for the new address only, trimmed"
    (lookup m.records.receiveLabels second == some "Alice, invoice 12" && (lookup m.records.receiveLabels first).isNone)
  check "label: back to the address, the label above it"
    (!m.receive.editingLabel && contains (rendered m) "Alice, invoice 12" && contains (rendered m) "Edit label")
  -- rename it
  let (m, _) ← sh.tap (.receive .editLabel) m
  check "rename: the editor holds the label" (m.labelEditor.draft == "Alice, invoice 12" && contains (rendered m) "Save label" &&
    contains (rendered m) "Remove label")
  let (twoLines, _) := stepReceive (.setLabelDraft "Alice\ninvoice") m
  check "rename: two lines are refused on the screen"
    ((stepReceive .saveLabel twoLines).2.isEmpty && contains (rendered twoLines) "Use a single-line label of at most 120 characters.")
  let (m, _) ← sh.tap (.receive (.setLabelDraft "Alice, invoice 13")) m
  let (m, _) ← sh.tap (.receive .saveLabel) m
  check "rename: the new label" (lookup m.records.receiveLabels second == some "Alice, invoice 13" &&
    contains (rendered m) "Alice, invoice 13" && !contains (rendered m) "invoice 12")
  -- remove it
  let (m, _) ← sh.tap (.receive .editLabel) m
  let (m, _) ← sh.tap (.receive .removeLabel) m
  check "remove: the label is gone" ((lookup m.records.receiveLabels second).isNone && !m.receive.editingLabel &&
    contains (rendered m) "Label this address")
  check "remove: and the backend agrees" ((lookup (← backend.records).receiveLabels second).isNone)
  -- one person, on the same page: no sheet of its own, and nothing but their name is asked for
  let card := m
  let page (model : Model) : String := renderedH (receiveSheet model [])
  check "person: Receive offers it under the address, and waits for a name"
    (card.topSheet == some .receive && contains (page card) "From one person" && contains (page card) "Their name" &&
     contains (page card) "Make their address and card" && (stepReceive .makePersonCard card).2.isEmpty)
  -- the card for everybody (the account key) is retired: none is asked for, made or shown
  check "person: no card for everybody on the page" (!contains (page card) "A card for everyone" && !contains (page card) "tpub")
  -- the wallet's own name is not needed: without one the card says nobody's, and the person names it themselves
  let (unnamed, _) := stepReceive (.setCardFor "Dana") card
  check "person: without a name of my own, theirs is enough"
    (card.settings.ownDisplayName.isEmpty && !contains (page card) "Add your name" &&
     (stepReceive .makePersonCard unnamed).2.any fun | .personCard _ none p own => p == "Dana" && own == "" | _ => false)
  let (card, left) ← sh.tap (.receive (.setOwnName "Alice")) card
  check "person: my name is saved" (card.settings.ownDisplayName == "Alice" && left.isEmpty)
  let (forDana, _) ← sh.tap (.receive (.setCardFor " Dana ")) card
  check "person: named, the button says whose it is" (contains (page forDana) "Make Dana’s address and card")
  let (making, cs) := stepReceive .makePersonCard forDana
  check "person card: asked of the backend, for Dana, under my name"
    (making.shareCard.making && cs.any fun | .personCard _ none p own => p == "Dana" && own == "Alice" | _ => false)
  check "person card: a second tap while it is being made asks nothing" ((stepReceive .makePersonCard making).2.isEmpty)
  let asksBefore := ((← sh.asks.get).filter (·.1 == "auth")).size
  let (made, _) ← sh.run making cs
  let some (madeFor, personText) := made.shareCard.personCard | check "person card: made" false s!"{made.shareCard.error}"; return
  check "person card: making it asked the device's owner" (((← sh.asks.get).filter (·.1 == "auth")).size == asksBefore + 1)
  check "person card: shown for Dana on the same page, under the wallet's address, and the button has gone"
    (madeFor == "Dana" && !made.shareCard.making && made.topSheet == some .receive &&
     contains (page made) "A card for Dana" && contains (page made) "If Dana uses Winnow, give them this instead" &&
     contains (page made) made.receive.address && contains (page made) "Your name on the card (optional)" &&
     !contains (page made) "Dana’s address and card")
  check "person card: Dana is a contact with a card" (made.records.people.any fun p => p.name == "Dana" && p.hasCard)
  let some danaAddress := made.shareCard.personAddress | check "person address: on the sheet" false; return
  check "person address: shown under the card, as an ordinary address, with what it is for"
    (danaAddress.startsWith "bcrt1p" && danaAddress != made.receive.address && contains (page made) "An address for Dana" &&
     contains (page made) "For any wallet or an exchange. It changes once it has been paid." && contains (page made) danaAddress)
  check "person address: it comes before the card, which is for a payer on Winnow"
    (((page made).splitOn "An address for Dana").head!.length < ((page made).splitOn "A card for Dana").head!.length)
  check "person address: it is the address the card's own payer pays first"
    ((← backend.personAddress none "Dana") == danaAddress &&
     ((PersonPaste.parse personText network).toOption.bind (·.payTo)).bind (fun p => (p.addressAt 0 network).toOption) == some danaAddress)
  check "person card: no account key in it" (!contains personText "tpub")
  let readBack ← backend.parsePaste personText
  check "person card: another phone reads Alice and a fresh address each payment" (readBack.name == some "Alice" && readBack.payTo == some true)
  let (again, cs) := stepReceive .makePersonCard made
  let (again, _) ← sh.run again cs
  check "person card: shown again it is the same card, and the device's owner is not asked"
    (again.shareCard.personCard == some ("Dana", personText) && ((← sh.asks.get).filter (·.1 == "auth")).size == asksBefore + 1)
  let (other, _) ← sh.tap (.receive (.setCardFor "Erin")) made
  check "person card: another name takes Dana's card and her address off the page"
    (other.shareCard.personCard.isNone && other.shareCard.personAddress.isNone && !contains (page other) "A card for Dana" &&
     contains (page other) "Make Erin’s address and card")
  check "person card: her name typed again offers to show what was made"
    (contains (page (stepReceive (.setCardFor "Dana") other).1) "Show Dana’s address and card")
  let late := onHost (.personCard other.generation "Dana" personText (some danaAddress) other.records) other
  check "person card: a card that arrives for another name is not shown, nor its address"
    (late.1.shareCard.personCard.isNone && late.1.shareCard.personAddress.isNone)
  let bare := onHost (.personCard made.generation "Dana" personText none made.records) made
  check "person address: a card that arrives without one is shown without one"
    (bare.1.shareCard.personCard.isSome && bare.1.shareCard.personAddress.isNone &&
     !contains (page bare.1) "An address for Dana" && contains (page bare.1) "A card for Dana")
  let (renamed, _) ← sh.tap (.receive (.setOwnName "Alicia")) made
  check "person address: under a new name of mine, the card and the address leave the sheet together"
    (renamed.shareCard.personCard.isNone && renamed.shareCard.personAddress.isNone)
  -- declined at the device's prompt: nothing made, nothing said
  sh.auth.set (Lean.Json.mkObj [("ok", Lean.Json.bool false), ("error", Lean.Json.str "User canceled.")])
  let (declining, cs) := stepReceive .makePersonCard other
  let (declined, _) ← sh.run declining cs
  check "person card: declined at the prompt, no card and no error"
    (declined.shareCard.personCard.isNone && !declined.shareCard.making && declined.shareCard.error.isNone &&
     !(declined.records.people.any fun p => p.name == "Erin" && p.hasCard))
  sh.auth.set (Lean.Json.mkObj [("ok", Lean.Json.bool true)])
  -- a payment arrives in a wallet that has made a card: the people and labels are read again, since the sync
  -- named it; in a wallet without one, nothing more is asked
  let incoming : HistoryItem := { txid := String.ofList (List.replicate 64 'd'), height := 0, received := 5_000, spent := 0, fee := none }
  let withPayment (model : Model) : List Cmd :=
    (onHost (.snapshot model.generation { model.status with history := incoming :: model.status.history } model.phase) model).2
  check "person card: a new payment in a wallet with a card reads the records again"
    ((withPayment made).any (· matches .records ..) && !(withPayment card).any (· matches .records ..))
  let seen := (onHost (.snapshot made.generation { made.status with history := incoming :: made.status.history } made.phase) made).1
  check "person card: a payment already shown asks for nothing" (!(withPayment seen).any (· matches .records ..))
  let passEnds (model : Model) : List Cmd :=
    let syncing := { model with status := { model.status with syncing := true } }
    (onHost (.snapshot syncing.generation { syncing.status with syncing := false } syncing.phase) syncing).2
  check "person card: the end of a sync pass reads them again too, in a wallet with a card only"
    ((passEnds seen).any (· matches .records ..) && !(passEnds card).any (· matches .records ..))
  -- from the saved recipients, for someone already there
  let (fromList, cs) := stepPeople (.card ((made.records.people.find? (·.name == "Dana")).map (·.id) |>.getD "")) made
  check "person card: from a saved person, a sheet opens on what was made for them, and asks at once"
    (fromList.topSheet == some .shareCard && fromList.shareCard.forName == "Dana" && fromList.shareCard.making &&
     contains (renderedH (shareCardSheet fromList [])) "From Dana" &&
     cs.any fun | .personCard _ pid p _ => p == "Dana" && pid.isSome | _ => false)
  let (closed, cs) := step .closeSheet m
  check "receive: Done closes the sheet and the mempool window" (closed.sheets.isEmpty && cs.any (· matches .stopWatchingAddress))
  let (closedAfter, _) := step .closeSheet made
  check "receive: closed, what was shown for Dana is gone, and opened again the page starts clean"
    (closedAfter.shareCard.personCard.isNone && closedAfter.shareCard.forName.isEmpty &&
     (step .openReceive { made with sheets := [] }).1.shareCard.personCard.isNone)

/-! ### People (#35) -/

/-- #35: Saved recipients from Send: a person added from a card, renamed, a refused paste and a refused
duplicate, a person added from an address and removed, and one chosen to pay. Returns the model, Robert's id. -/
def peopleScreens (sh : Shell) (backend : Backend) (walletID cardB addressB : String) : IO (Model × String) := do
  let m := readyModel walletID
  let (m, _) ← sh.tap .openSend m
  let (m, _) ← sh.tap (.send .openRecipients) m
  check "people: Saved recipients, empty" (m.topSheet == some .savedRecipients &&
    contains (rendered m) "Save a recipient from a payment in Wallet, or add an address or card here.")
  -- add Bob from his card
  let (m, _) ← sh.tap (.people (.openAdd {} "")) m
  check "add: the sheet" (m.topSheet == some .addPerson && contains (renderedH (addPersonSheet m [])) "Save recipient")
  let (m, _) ← sh.tap (.people (.setName "Bob")) m
  let (m, _) ← sh.tap (.people (.setPasted cardB)) m
  check "add: the card reads as fresh addresses" (m.person.parsed == some { name := some "Bob", payTo := some true } &&
    contains (renderedH (addPersonSheet m [])) "Fresh address each payment")
  check "add: Save is enabled" (m.person.canSave m)
  let (m, _) ← sh.tap (.people .save) m
  let some bob := m.records.people.find? (·.name == "Bob") | check "add: Bob saved" false; return (m, "")
  check "add: the sheet closes on the list" (m.topSheet == some .savedRecipients && bob.payTo == some true)
  check "add: the list shows Bob with Rename and Remove" (contains (rendered m) "\"Bob\"" && contains (rendered m) "Rename")
  -- rename him
  let (m, _) ← sh.tap (.people (.rename bob.id)) m
  let sheet := renderedH (addPersonSheet m [])
  check "rename: the sheet, his name in it, no paste field" (contains sheet "Rename recipient" && m.person.name == "Bob" &&
    !contains sheet "Paste an address or card")
  let (m, _) ← sh.tap (.people (.setName "Robert")) m
  let (m, _) ← sh.tap (.people .save) m
  check "rename: saved" ((m.person? bob.id).map (·.name) == some "Robert" && m.topSheet == some .savedRecipients &&
    contains (rendered m) "Robert")
  -- what is refused: a paste that is no address or card, the same card under another name
  let (m, _) ← sh.tap (.people (.openAdd {} "")) m
  let (m, _) ← sh.tap (.people (.setName "Bobby")) m
  let (garbage, _) ← sh.tap (.people (.setPasted "hello world")) m
  check "refused: a paste that is not an address or card says so, and Save is off"
    (garbage.person.error.isSome && !garbage.person.canSave garbage && (stepPeople .save garbage).2.isEmpty &&
     contains (renderedH (addPersonSheet garbage [])) (garbage.person.error.getD "?"))
  let (dup, _) ← sh.tap (.people (.setPasted cardB)) garbage
  let (dup, _) ← sh.tap (.people .save) dup
  check "refused: the same card twice, on the sheet" (dup.topSheet == some .addPerson && !dup.person.saving &&
    dup.person.error.isSome && contains (renderedH (addPersonSheet dup [])) "Robert")
  let (m, _) ← sh.tap .closeSheet dup
  -- Carol, by one address, then removed
  let (m, _) ← sh.tap (.people (.openAdd {} addressB)) m
  check "add: an address pasted in the sheet" (m.person.parsed.bind (·.payTo) == some false &&
    contains (renderedH (addPersonSheet m [])) "Uses this same address each time")
  let (m, _) ← sh.tap (.people (.setName "Carol")) m
  let (m, _) ← sh.tap (.people .save) m
  let some carol := m.records.people.find? (·.name == "Carol") | check "add: Carol saved" false; return (m, bob.id)
  check "add: Carol listed" (contains (rendered m) "Carol")
  let (m, _) ← sh.tap (.people (.remove carol.id)) m
  check "remove: Carol is no longer a saved recipient" (!contains (rendered m) "Carol" &&
    ((m.person? carol.id).map (·.isSavedRecipient)) == some false && m.recipientsError.isNone)
  check "remove: the backend agrees" (((← backend.records).people.find? (·.id == carol.id)).map (·.isSavedRecipient) == some false)
  -- choose Robert to pay
  let (m, _) ← sh.tap (.people (.choose bob.id)) m
  check "choose: back on Send, paying Robert" (m.topSheet == some .send && m.send.inputs.personID == some bob.id &&
    contains (rendered m) "Robert" && contains (rendered m) "Change")
  let (m, _) := step .closeSheet m
  return (m, bob.id)

/-! ### Home: a payment's screen (#35) -/

def scriptHex (address : String) : IO String := do
  match AddressDecoder.scriptPubKey address network with
  | .ok s => return hex s
  | .error _ => throw (IO.userError s!"no script for {address}")

/-- #35: Home's payment screen over three payments, the people the flow above saved and a receive label:
each section, and what its buttons do, through the real backend. -/
def homeScreens (sh : Shell) (backend : Backend) (walletID robertID bobAddress ownAddress funder : String) : IO Unit := do
  discard <| backend.setReceiveLabel ownAddress "Invoice 12"
  let records ← backend.records
  let bobScript ← scriptHex bobAddress
  check "home fixture: Robert's first address is one of his" (records.recipientByScript.contains (bobScript, robertID))
  let t1 := hex (ByteArray.mk (Array.replicate 32 0x11))
  let t2 := hex (ByteArray.mk (Array.replicate 32 0x22))
  let t3 := hex (ByteArray.mk (Array.replicate 32 0x33))
  let ownScript ← scriptHex ownAddress
  let toBob : TxOut := { index := 0, address := some bobAddress, script := bobScript, amount := 50_000, ownedByWallet := false }
  let change : TxOut := { index := 1, address := some "bcrt1qchange", script := "0014", amount := 9_500, ownedByWallet := true }
  let toUs : TxOut := { index := 0, address := some ownAddress, script := ownScript, amount := 20_000, ownedByWallet := true }
  let sent : HistoryItem :=
    { txid := t1, height := 0, received := 9_500, spent := 60_000, fee := some 500, outputs := some [toBob, change] }
  let received : HistoryItem :=
    { txid := t2, height := 101, received := 20_000, spent := 0, fee := none, outputs := some [toUs], fundingAddresses := [funder] }
  let unstored : HistoryItem := { txid := t3, height := 99, received := 0, spent := 7_300, fee := some 300 }
  let history := [sent, received, unstored]
  let status : Status := { balance := 29_500, history, payments := history.map ({ item := ·, source := .wallet }),
                           feeBumpable := [t1], tipHeight := 101 }
  let m := { readyModel walletID with status, records }
  let home := rendered m
  check "home: the list" (contains home "Sent to Robert" && contains home "Received" && contains home (Ids.historyPayment t2) &&
    contains home "Pending" && contains home "Confirmed")
  -- the payment to Robert
  let (m, left) ← sh.tap (.home (.openPayment t1)) m
  check "payment: opens, nothing to load" (m.routes == [.payment t1] && left.isEmpty && !m.payment.loading)
  let sections := (paymentSections m t1).map renderedH
  check "payment: its row, its recipient, its transaction" (sections.length == 3) s!"{sections.length}"
  check "payment: the row" (contains sections[0]! "Sent to Robert" && contains sections[0]! "Pending")
  check "payment: Robert, the amount, Rename and Remove" (contains sections[1]! "Robert" && contains sections[1]! (satsText 50_000) &&
    contains sections[1]! "Rename recipient" && contains sections[1]! "Remove from saved recipients")
  check "payment: the address and the transaction ID fold under their titles"
    (contains sections[1]! "\"Address\"" && contains sections[2]! "\"Transaction ID\"" && !m.isExpanded "pay.addr.0" && !m.isExpanded "pay.txid")
  let (m, _) ← sh.tap (.setExpanded s!"pay.addr.0" true) m
  let (m, _) ← sh.tap (.setExpanded "pay.txid" true) m
  check "payment: unfolded" (m.isExpanded "pay.addr.0" && m.isExpanded "pay.txid" && contains (rendered m) bobAddress && contains (rendered m) t1)
  let (opened, _) ← sh.tap (.home (.editRecipient bobAddress (some robertID))) m
  check "payment: Rename recipient opens the sheet with his name"
    (opened.topSheet == some .addPerson && opened.person.name == "Robert" && contains (rendered opened) "Rename recipient")
  let (m, _) ← sh.tap (.home (.removeRecipient robertID)) m
  check "payment: Remove from saved recipients" (((m.person? robertID).map (·.isSavedRecipient)) == some false &&
    contains (rendered m) "Save recipient" && !contains (rendered m) "Remove from saved recipients")
  let (m, _) ← sh.tap (.home (.editRecipient bobAddress (some robertID))) m
  check "payment: Save recipient, with his name" (m.person.name == "Robert" && contains (renderedH (addPersonSheet m [])) "Save recipient")
  let (m, _) ← sh.tap (.people .save) m
  check "payment: saved again" (((m.person? robertID).map (·.isSavedRecipient)) == some true && contains (rendered m) "Rename recipient" &&
    m.sheets.isEmpty)
  let (m, _) ← sh.tap (.home .pop) m
  check "payment: Back" (m.routes.isEmpty && contains (rendered m) "Activity")
  -- the payment received: its address label, its sender
  let (m, _) ← sh.tap (.home (.openPayment t2)) m
  let sections := (paymentSections m t2).map renderedH
  check "received: its row, its label, its sender, its transaction" (sections.length == 4) s!"{sections.length}"
  check "received: the label of the address paid" (contains sections[1]! "Receive address labels" && contains sections[1]! "Invoice 12" &&
    contains sections[1]! "Edit address label")
  check "received: no sender yet" (contains sections[2]! "Save sender as person")
  let (m, _) ← sh.tap (.home .labelSender) m
  let sheet := renderedH (addPersonSheet m [])
  check "sender: the sheet offers the saved people and the funding address"
    (contains sheet "Save sender" && contains sheet "Or choose someone saved" && contains sheet "Robert" && contains sheet funder)
  let (m, _) ← sh.tap (.people (.chooseFunding funder .localFunding)) m
  let (m, _) ← sh.tap (.people (.setName "Dave")) m
  let (m, _) ← sh.tap (.people .save) m
  let some dave := m.records.people.find? (·.name == "Dave") | check "sender: Dave saved" false; return
  check "sender: Dave labels the payment, paid at his funding address"
    (lookup m.records.senderByTxid t2 == some dave.id && dave.payTo == some false && dave.provenance == some .localFunding && m.sheets.isEmpty)
  let shown := rendered m
  check "sender: the screen says so" (contains shown "Received from Dave" && contains shown "Send to Dave" && contains shown "Remove sender label")
  let (paying, left) ← sh.tap (.home (.sendToPerson dave.id)) m
  check "sender: Send to Dave opens Send, paying him" (paying.topSheet == some .send && paying.send.inputs.personID == some dave.id &&
    paying.send.inputs.paymentIndex == some 0 && left.any (· matches .resolveRate ..))
  let (m, _) ← sh.tap (.home .removeSenderLabel) m
  check "sender: the label removed" ((lookup m.records.senderByTxid t2).isNone && contains (rendered m) "Save sender as person")
  let (m, _) ← sh.tap (.home .labelSender) m
  let (m, _) ← sh.tap (.people (.chooseSaved dave.id)) m
  check "sender: someone saved, chosen" (lookup m.records.senderByTxid t2 == some dave.id && m.sheets.isEmpty)
  -- the address label, edited from the payment
  let (m, _) ← sh.tap (.home (.editPaymentLabel ownAddress)) m
  let sheet := renderedH (labelSheet m [])
  check "label: the sheet, the label in it" (m.topSheet == some .labelEditor && m.labelEditor.draft == "Invoice 12" &&
    contains sheet "Address label" && contains sheet "Save label" && contains sheet "Remove label")
  let (m, _) ← sh.tap (.receive (.setLabelDraft "Invoice 12, paid")) m
  let (m, _) ← sh.tap (.receive .saveLabel) m
  check "label: saved, the sheet closes, the payment shows it" (m.sheets.isEmpty && contains (rendered m) "Invoice 12, paid")
  let (m, _) ← sh.tap (.home .pop) m
  -- a send whose transaction is not on this phone: its details load
  let (m, cs) := stepHome (.openPayment t3) m
  check "unstored: opening it loads its details" (m.payment.loading && cs.any fun | .loadPaymentDetails _ t => t == t3 | _ => false)
  check "unstored: Loading… meanwhile" (contains (rendered m) "Loading payment details")
  let (m, cs) := onHost (.paymentLoaded m.generation t3) m
  check "unstored: loaded, the wallet read again" (!m.payment.loading && cs.any (· matches .refresh _))
  let (failed, _) := onHost (.failed m.generation (.payment .payment) false "The peer did not send it.") { m with payment := { loading := true } }
  check "unstored: a failure shows, with Load payment details again"
    (contains (rendered failed) "The peer did not send it." && contains (rendered failed) "Load payment details")
  check "unstored: not while syncing" (stepHome .loadPayment { failed with status := { failed.status with syncing := true } }).2.isEmpty
  let (m, _) := stepHome .pop m
  -- one mode: Bump fee for a payment that can be bumped, the transaction behind its title
  let (adv, _) := stepHome (.openPayment t1) m
  let s := rendered adv
  check "payment: Bump fee, the transaction folded" (contains s "Bump fee" && !adv.isExpanded "pay.txid")
  let (adv, _) := step (.setExpanded "pay.txid" true) adv
  check "payment: unfolded, the txid in full and View transaction" (contains (rendered adv) t1 && contains (rendered adv) "View transaction")
  let (adv2, _) := stepHome (.openPayment t2) (stepHome .pop adv).1
  check "payment: no Bump fee for a payment received" (!contains (rendered adv2) "Bump fee")
  -- a payment gone from the history
  let (gone, _) := stepHome (.openPayment (hex (ByteArray.mk (Array.replicate 32 0x44)))) m
  check "gone: says so" (contains (rendered gone) "This payment is no longer in the wallet")

/-! ### The People store: payment indexes and pay-to checks (#35) -/

/-- `advancePaymentIndex`, as two payments to Bob move it, and `validatePayTo`'s refusals, one of them
through the file. -/
def paymentIndexAndPayTo (a b : Phone) : IO Unit := do
  let r ← a.records
  let some bob := r.people.find? (·.name == "Bob") | check "Bob is saved" false; return
  let index (r : Records) : Nat := ((r.people.find? (·.id == bob.id)).map (·.nextPaymentIndex)).getD 999
  check "index: Bob is paid at index 0 first" (index r == 0)
  let (addr0, i0) ← obtain "index: Bob's next address" (nextPaymentAddress a.store bob.id)
  let advance (i : UInt32) : RM Records := withPeople a.store (some a.wallet) fun ps =>
    ps.advancePaymentIndex a.store.keys a.store.writeData bob.id i
  let r ← obtain "index: a payment at 0" (advance i0)
  check "index: the next payment uses 1" (index r == 1)
  let (addr1, i1) ← obtain "index: Bob's next address again" (nextPaymentAddress a.store bob.id)
  check "index: a fresh address" (i1 == 1 && addr1 != addr0)
  let r ← obtain "index: a payment reported at 0 again" (advance 0)
  check "index: never goes back" (index r == 1)
  let r ← obtain "index: a payment at 4" (advance 4)
  check "index: past it" (index r == 5)
  let r ← obtain "index: then one at 2" (advance 2)
  check "index: still past the highest" (index r == 5)
  check "index: on disk" (index (← (← a.reopen).records) == 5)
  refused "index: the last index there is" (kind := "invalidState") (advance PeopleStore.maximumNextIndex)
  refused "index: an unknown person" (kind := "unknownPerson") (withPeople a.store (some a.wallet) fun ps =>
    ps.advancePaymentIndex a.store.keys a.store.writeData "nobody" 1)
  -- validatePayTo
  let some bobRecord := (← a.store.read).people.record? bob.id | check "Bob's record" false; return
  let some bobPayTo := bobRecord.payTo | check "Bob's pay-to" false; return
  let person (id : String) (payTo : Winnow.PersonPayTo) : PersonRecord := { id, name := id, payTo := some payTo }
  let addr ← obtain "B address 11" (wm (b.wallet.address .receive 11))
  let seen ← obtain "payTo: Bob's descriptor" (PeopleStore.validatePayTo bobRecord network {})
  let seen ← obtain "payTo: an address" (PeopleStore.validatePayTo (person "carol" (.address addr)) network seen)
  check "payTo: both counted" (seen.size == 2)
  let seen' ← obtain "payTo: a name-only person" (PeopleStore.validatePayTo { id := "dave", name := "Dave" } network seen)
  check "payTo: a name-only person adds nothing" (seen'.size == 2)
  refused "payTo: two people with Bob's key" (kind := "invalidState") (PeopleStore.validatePayTo (person "bob2" bobPayTo) network seen)
  refused "payTo: two people with one address" (kind := "invalidState") (PeopleStore.validatePayTo (person "carol2" (.address addr)) network seen)
  refused "payTo: an address not in canonical form" (kind := "invalidState")
    (PeopleStore.validatePayTo (person "spaced" (.address s!" {addr}")) network {})
  refused "payTo: a descriptor not in canonical form" (kind := "invalidState")
    (PeopleStore.validatePayTo (person "spaced" (.descriptor s!"{bobPayTo.text}\n")) network {})
  refused "payTo: another network's address" (PeopleStore.validatePayTo (person "main" (.address "bc1qar0srrr7xfkvy5l643lydnw9re59gtzzwf5mdq")) network {})
  refused "payTo: a descriptor that is none" (PeopleStore.validatePayTo (person "junk" (.descriptor "tr(nonsense)")) network {})
  refused "payTo: a silent payment code that is none" (PeopleStore.validatePayTo (person "sp" (.silentPayment "sp1qqnotacode")) network {})
  -- a sealed file holding two people with one key reads as damage
  let path := a.dir / "people.json"
  let good ← IO.FS.readBinFile path
  let key := ((← (a.keys.key "people.regtest").run).toOption.join).getD .empty
  IO.FS.writeBinFile path (SealedStoreFile.sealed (PeopleStore.encode #[bobRecord, { bobRecord with id := "copy", name := "Copy" }] #[]) "people" network key)
  check "payTo: a file with two people sharing a key is damaged" ((← (← a.reopen).records).peopleStorageNotice == some PeopleStore.damagedStorageMessage)
  IO.FS.writeBinFile path good
  check "payTo: the good file reads again" ((← (← a.reopen).records).peopleStorageNotice.isNone)

/-! ### Refused cards, in their own words (#69) -/

/-- The Add-person sheet refuses a card for another network, one from a newer Winnow and one that is no
person card, each with the card's own text (`PersonCardError.description`), and Save stays off. -/
def cardsRefusedOnTheAddPersonSheet (sh : Shell) (walletID : String) : IO Unit := do
  let (m, _) ← sh.tap .openSend (readyModel walletID)
  let (m, _) ← sh.tap (.send .openRecipients) m
  let (m, _) ← sh.tap (.people (.openAdd {} "")) m
  let (m, _) ← sh.tap (.people (.setName "Eve")) m
  let newer := "{\"name\":\"Eve\",\"network\":\"regtest\",\"version\":4,\"winnow\":\"person-card\"}"
  let cards : List (String × String × String) := [
    ("another network's card", (PersonCard.make .mainnet "Eve" none).serialized,
      "This card is for mainnet; this wallet is on regtest."),
    ("a newer Winnow's card", newer,
      "This card was made by a newer Winnow (card version 4). Update the app to read it."),
    ("not a person card", "{\"name\":\"Eve\",\"winnow\":\"signer-card\"}", "That isn't a Winnow card.")]
  for (what, card, text) in cards do
    let (refused, _) ← sh.tap (.people (.setPasted card)) m
    check s!"card refused: {what}, in the card's words" (refused.person.error == some text) s!"{refused.person.error}"
    check s!"card refused: {what}, on the sheet, Save off"
      (contains (renderedH (addPersonSheet refused [])) text && !refused.person.canSave refused)
  discard <| sh.tap .closeSheet m

/-! ### A store's seal, refused by case (#69) -/

/-- `StoreSeal.read` with each `SealFailure`: a sealed file on a phone with no key, an unsealed one once the key
exists, a seal whose code is not hex, and a payload changed under its seal. The case names are what
`RecordsError.name` reports (the Signers merge and the journal read them). -/
def sealFailures (root : System.FilePath) : IO Unit := do
  let store : StoreSeal := { store := "people", keys := StoreKeyVault.inMemory (← IO.mkRef {}) }
  let path := root / "seal-failures.json"
  let payload := "{\"people\":[]}".toUTF8
  discard <| obtain "seal: the first write establishes the key"
    (store.write payload network path fun d p => IO.FS.writeBinFile p d)
  let sealed ← IO.FS.readBinFile path
  discard <| obtain "seal: and reads back" (store.read sealed network)
  let fresh : StoreSeal := { store with keys := StoreKeyVault.inMemory (← IO.mkRef {}) }
  let some nl := sealed.toList.idxOf? 0x0A | throw (IO.userError "seal: no newline")
  let notHex := sealed.set! (nl - 1) 0x7A
  let changed := sealed.set! (sealed.size - 2) (sealed[sealed.size - 2]! ^^^ 0x01)
  for (what, kind, x) in [
      ("a sealed file, and no key on this phone", "keyMissing", fresh.read sealed network),
      ("an unsealed file, once the key exists", "unsealed", store.read payload network),
      ("a seal that is not hex", "malformed", store.read notHex network),
      ("a payload changed under its seal", "verificationFailed", store.read changed network)] do
    refused s!"seal refused: {what}" (kind := kind)
      (matching := (·.description == "The store file could not be verified.")) x

/-! ### Backup and the recovery phrase (#64) -/

/-- Where `needle` first starts in `s`, if anywhere. -/
def positionOf (s needle : String) : Option Nat :=
  match s.splitOn needle with
  | first :: _ :: _ => some first.length
  | _ => none

/-- The arguments the shell was last asked for `clipboard.set` with, from `perform`ing the copies in `cs`
(not the badge's timer, whose answer would come back in the middle of a later flow). -/
def clipboardAsked (sh : Shell) (cs : List Cmd) : IO (Option Lean.Json) := do
  sh.caps.set #[]
  for c in cs do if c matches .copy .. then WinnowApp.perform c sh.fx
  return ((← sh.caps.get).toList.filter (·.1 == "clipboard.set")).getLast?.map (·.2)

/-- #64: the screens between `revealMnemonic` and a person's eyes, as a person uses them. Settings' Backup
section: Show recovery phrase, the words numbered two to a row, hidden while the screen is recorded, copied
local-only for two minutes; going to the background closes it and the other two sensitive sheets (the backup
file, Restore from a file) and forgets what they held, and a phrase that arrives after that is dropped.
The Back up page: Save a backup file with the phrase, and on a new phone Restore from a file pastes
it through to the verification report, and that phone shows the same words. -/
def backupScreens (sh : Shell) (root : System.FilePath) (backend : Backend) (walletID : String) (entropy : UInt8) : IO Unit := do
  tmpDir.set (root / "tmp").toString
  IO.FS.createDirAll (root / "tmp")
  let expected := match Winnow.Keys.BIP39.mnemonic (ByteArray.mk (Array.replicate 16 entropy)) with
    | .ok phrase => phrase.splitOn " "
    | .error _ => []
  let labels := expected.zipIdx.map fun (w, i) => s!"{i + 1}. {w}"
  let showsWords (s : String) : Bool := expected.any fun w => contains s s!"\"{w}\"" || contains s s!". {w}\""
  -- Settings' Backup section: Show recovery phrase
  let (m, _) ← sh.tap (.home .openSettings) (readyModel walletID)
  let settings := rendered m
  check "reveal: Settings offers Show recovery phrase" (contains settings "Show recovery phrase" && !showsWords settings)
  let (m, _) ← sh.tap (.backup .reveal) m
  check "reveal: the sheet opens on the phone's twelve words" (m.topSheet == some .revealPhrase && expected.length == 12 &&
    m.reveal.words == expected && !m.reveal.revealing) s!"{m.reveal.words}"
  let sheet := rendered m
  check "reveal: titled Recovery phrase" (contains sheet "Recovery phrase" && contains sheet "Copy recovery phrase")
  check "reveal: each word with its number" (labels.all fun l => contains sheet s!"\"{l}\"")
  let positions := labels.filterMap (positionOf sheet s!"\"{·}\"")
  check "reveal: numbered 1 to 12 in order" (positions.length == 12 && (positions.zip positions.tail).all fun (a, b) => a < b)
  let rec pairs : List String → List (String × String)
    | a :: b :: rest => (a, b) :: pairs rest
    | _ => []
  check "reveal: two words to a row, 1 beside 2"
    (pairs labels |>.all fun (a, b) => contains sheet (renderedH (.row [body a, .spacer, body b])))
  check "reveal: six rows" ((pairs labels).length == 6 && !contains sheet "\"13. ")
  -- the screen recorded or mirrored, as the shell says it
  let some recording := system (Lean.Json.mkObj [("captured", Lean.Json.bool true)])
    | check "capture: the shell's event reads" false; return
  let (hidden, _) := onHost recording m
  let shown := rendered hidden
  check "capture: the words are hidden while the screen is recorded"
    (hidden.captured && !showsWords shown && contains shown "Hidden while the screen is being recorded or mirrored.")
  check "capture: the sheet stays, so the words come back" (hidden.topSheet == some .revealPhrase && hidden.reveal.words == expected)
  let (back, _) := onHost (.captured false) hidden
  check "capture: recording stops, the words show again"
    ((labels.all fun l => contains (rendered back) s!"\"{l}\"") && !contains (rendered back) "Hidden while the screen")
  -- Copy recovery phrase
  let (copied, cs) := step (.backup .copyPhrase) m
  check "copy: the button says how long" (contains (rendered copied) "Copied for 2 minutes")
  let phrase := " ".intercalate expected
  let some args ← clipboardAsked sh cs | check "copy: the phrase goes to the clipboard" false; return
  check "copy: the whole phrase" ((args.getObjValAs? String "text").toOption == some phrase)
  -- what the shell was asked, without the words
  let policy := s!"localOnly {(args.getObjValAs? Bool "localOnly").toOption}, expiresIn {(args.getObjValAs? Nat "expiresIn").toOption}"
  check "copy: local only, never Universal Clipboard" ((args.getObjValAs? Bool "localOnly").toOption == some true) policy
  check "copy: expires after two minutes" ((args.getObjValAs? Nat "expiresIn").toOption == some 120) policy
  let some other ← clipboardAsked sh (step (.copy "address" "bcrt1qaddress") m).2
    | check "copy: an address goes to the clipboard" false; return
  check "copy: an address is not held to the phrase's policy"
    ((other.getObjValAs? Bool "localOnly").toOption == some false && (other.getObjValAs? Nat "expiresIn").toOption == some 300)
  -- going to the background
  let some leaving := system (Lean.Json.mkObj [("scene", Lean.Json.str "background")])
    | check "background: the shell's event reads" false; return
  let (gone, _) := onHost leaving copied
  check "background: the phrase sheet closes and forgets the words"
    (gone.sheets.isEmpty && gone.reveal.words.isEmpty && !gone.reveal.copied && !showsWords (rendered gone) &&
     !contains (rendered gone) "Recovery phrase\"")
  let (again, _) := onHost (.scene true) gone
  check "background: coming back does not bring it back" (again.sheets.isEmpty && !showsWords (rendered again))
  -- a phrase asked for, then the phone locked before it arrived
  let (asking, cs) := step (.backup .reveal) again
  let (locked, _) := onHost (.scene false) asking
  let (locked, _) := onHost (.scene true) locked
  let (late, _) ← sh.run locked cs
  check "background: a phrase that arrives afterwards is dropped" (late.sheets.isEmpty && late.reveal.words.isEmpty && !showsWords (rendered late))
  -- the backup file with the phrase in it
  let (e, _) ← sh.tap (.backup .openExport) again
  let (e, _) ← sh.tap (.backup (.setIncludeMnemonic true)) e
  let (e, _) ← sh.tap (.backup .createExport) e
  let (e, _) ← sh.tap (.backup .confirmExport) e
  let some file := e.exportState.file | check "background: the backup file is made" false; return
  check "background: the backup file is made, with the phrase" (e.topSheet == some .exportBundle &&
    contains (← IO.FS.readFile file) (expected.headD "?"))
  -- #92's finding 3: a file that carries the phrase is asked for as showing the phrase is
  let authReasons : IO (Array String) := do
    return (← sh.asks.get).filterMap fun (n, a) => if n == "auth" then (a.getObjValAs? String "reason").toOption else none
  check "export: a backup file with the phrase asks the device's owner"
    ((← authReasons).contains "Export your recovery phrase") s!"{← authReasons}"
  let exportWith (withPhrase : Bool) (answer : Lean.Json) : IO Model := do
    sh.asks.set #[]
    sh.auth.set answer
    let (x, _) ← sh.tap (.backup .openExport) again
    let (x, _) ← sh.tap (.backup (.setIncludeMnemonic withPhrase)) x
    let (x, _) ← sh.tap (.backup .createExport) x
    let (x, _) ← if withPhrase then sh.tap (.backup .confirmExport) x else pure (x, [])
    sh.auth.set (Lean.Json.mkObj [("ok", Lean.Json.bool true)])
    return x
  let declined ← exportWith true (Lean.Json.mkObj [("ok", Lean.Json.bool false), ("error", Lean.Json.str "Biometry is locked out.")])
  check "export: declined, no file is made and the sheet says why"
    (declined.exportState.file.isNone && !declined.exportState.busy && declined.exportState.error == some "Biometry is locked out.")
    s!"{repr declined.exportState.error}"
  let cancelled ← exportWith true (Lean.Json.mkObj [("ok", Lean.Json.bool false), ("error", Lean.Json.str "Authentication was cancelled.")])
  check "export: a cancelled prompt makes no file and says nothing"
    (cancelled.exportState.file.isNone && !cancelled.exportState.busy && cancelled.exportState.error.isNone)
    s!"{repr cancelled.exportState.error}"
  let watchOnly ← exportWith false (Lean.Json.mkObj [("ok", Lean.Json.bool false), ("error", Lean.Json.str "no")])
  check "export: a file without the phrase asks nothing"
    (watchOnly.exportState.file.isSome && (← authReasons).isEmpty) s!"{← authReasons}"
  let (eGone, cs) := onHost (.scene false) e
  let (eGone, _) ← sh.run eGone cs
  check "background: the backup file sheet closes and forgets the file"
    (eGone.sheets.isEmpty && eGone.exportState.file.isNone && !eGone.exportState.includeMnemonic &&
     !contains (rendered eGone) "Backup ready")
  check "background: and the staged file is removed" (← waitUntil 2_000 (every := 5) do return !(← System.FilePath.pathExists file))
  -- a sheet that holds no key stays
  let (cloudOpen, _) := step (.cloud .openBackup) again
  let (cloudKept, _) := onHost (.scene false) cloudOpen
  check "background: the iCloud backup sheet stays" (cloudOpen.topSheet == some .cloudBackup && cloudKept.topSheet == some .cloudBackup)
  -- Restore from a file, before a wallet exists
  let fresh : Model := { stage := .onboarding, active := true, settings := { network := .regtest } }
  let (imp, _) := step .openImport fresh
  let (imp, _) := step (.setImportText "{\"version\":1}") imp
  check "background: Restore from a file holds the pasted text" (imp.topSheet == some .importWallet &&
    contains (rendered imp) "Import wallet")
  let (impGone, _) := onHost (.scene false) imp
  check "background: Restore from a file closes and forgets the text"
    (impGone.sheets.isEmpty && impGone.onboarding.importText.isEmpty && !contains (rendered impGone) "Import wallet")

  -- Home stays focused on iCloud backup; manual backup files live in Settings → Backup
  let simple := readyModel walletID
  check "Home: does not nudge a manual backup file while not backed up"
    (!contains (rendered simple) "Save a backup file" && contains (rendered simple) Ids.homeCloudBackupButton)
  let (page, _) ← sh.tap (.home .openSettings) simple
  let shown := rendered page
  check "Settings → Backup: offers backup file and recovery phrase, words hidden"
    (page.routes == [.settings] && contains shown "A backup file is a copy you keep yourself." &&
     contains shown "Save a backup file" && contains shown "Show recovery phrase" && contains shown "iCloud" && !showsWords shown)
  let (page, _) ← sh.tap (.backup .openExport) page
  check "Backup file: opens the file sheet over Settings"
    (page.topSheet == some .exportBundle && contains (rendered page) "Create backup file")
  let (page, _) ← sh.tap (.backup (.setIncludeMnemonic true)) page
  check "Backup file: including the phrase says what that means" (contains (rendered page) "This file includes your phone’s signing key.")
  let (page, _) ← sh.tap (.backup .createExport) page
  check "Backup file: and asks first" (contains (rendered page) "Include the recovery phrase?" && page.exportState.file.isNone)
  let (page, _) ← sh.tap (.backup .confirmExport) page
  let some file := page.exportState.file | check "Backup file: the file is ready" false; return
  check "Backup file: the file is ready to share" (contains (rendered page) "Backup ready" &&
    contains (rendered page) "Includes your recovery words. Keep this file private.")
  let bundle ← IO.FS.readFile file
  let (page, cs) := step .closeSheet page
  let (page, _) ← sh.run page cs
  let (home, _) ← sh.tap (.home .pop) page
  check "Backup file: closing the sheet, then Back, is Home" (page.sheets.isEmpty && home.routes.isEmpty &&
    !contains (rendered home) "Save a backup file")

  -- a new phone restores it: the import sheet through to the verification report
  let restoreRoot := root / "screens-restore"
  IO.FS.createDirAll (restoreRoot / "regtest")
  -- no peer to verify against here (backend-test verifies an import against a node): the wait is cut short
  let (restorer, _, _) ← Backend.realWithMultisig { keyStore := inMemoryKeyStore (← IO.mkRef {}), fetch := fun _ => throw (.other "offline"),
                                                     importPeerWaitMs := 0 }
  match ← restorer.openWallet .regtest (restoreRoot / "regtest").toString with
  | .missing => pure ()
  | _ => check "restore: the new phone has no wallet" false; return
  backendRef.set restorer
  rootDir.set restoreRoot.toString
  check "restore: onboarding offers Restore from a file" (contains (rendered fresh) "Restore from a file")
  let (r, _) ← sh.tap .openImport fresh
  let sheet := rendered r
  check "restore: the import sheet" (r.topSheet == some .importWallet && contains sheet "Import wallet" &&
    contains sheet "Paste your backup file (JSON)" && contains sheet "Import and verify" && !contains sheet "Verification report")
  sh.clipboard.set bundle
  let (r, _) ← sh.tap .pasteImport r
  check "restore: Paste from clipboard fills it" (r.onboarding.importText == bundle)
  let (r, _) ← sh.tap .importWallet r
  let some report := r.onboarding.importReport | check "restore: the verification report" false s!"{r.onboarding.error}"; return
  let sheet := rendered r
  check "restore: the verification report, then Continue" (r.walletID == some walletID && !r.onboarding.busy &&
    contains sheet "Verification report" && contains sheet "Continue" && !contains sheet "Import and verify")
  check "restore: the report says verification waits for peers" (report == Real.verificationWaitingText && contains sheet report) report
  let (r, _) ← sh.tap .finishOnboarding r
  check "restore: Continue opens the wallet, with the Bluetooth card" (r.stage == .ready && r.sheets == [.bluetoothIntro])
  let (r, _) ← sh.tap (.ledgerCard .skipBluetooth) r
  let (r, _) ← sh.tap (.home .openSettings) r
  let (r, _) ← sh.tap (.backup .reveal) r
  check "restore: the new phone shows the same twelve words" (r.topSheet == some .revealPhrase && r.reveal.words == expected)
  backendRef.set backend
  rootDir.set (root / "screens-alice").toString

/-- A version 1 card, as other wallets hand one out (upstream's, and Winnow's own before issue #94): the
account key as the pay-to key. The app no longer makes one; it still reads one and pays it. Built here from
the descriptor in the phone's backup. -/
def accountKeyCard (b : Backend) (name : String) : IO String := do
  let bundle ← match Winnow.ImportBundle.decode (← b.exportBundle false) with
    | .ok bundle => pure bundle
    | .error _ => throw (IO.userError "accountKeyCard: the backup does not decode")
  let some text := bundle.descriptor | throw (IO.userError "accountKeyCard: the backup has no descriptor")
  let descriptor ← match Winnow.Descriptor.parse text with
    | .ok d => pure d
    | .error e => throw (IO.userError s!"accountKeyCard: {e.name}")
  match ← (WinnowApp.RecordsReal.ownPersonCardOf descriptor .regtest name).run with
  | .ok card => return card.serialized
  | .error _ => throw (IO.userError "accountKeyCard: no card")

/-- The screen flows, in one directory. -/
def screens (root : System.FilePath) : IO Unit := do
  failuresReachTheirScreens
  settingsScreen root
  let (alice, aliceID) ← screenPhone root "screens-alice" 0xA1
  let (bob, _) ← screenPhone root "screens-bob" 0xB2
  let cardB ← accountKeyCard bob "Bob"
  let bobAddress ← bob.receiveAddress false
  let otherAddress ← bob.receiveAddress true
  let funder ← bob.receiveAddress true
  backendRef.set alice
  rootDir.set (root / "screens-alice").toString
  let sh ← Shell.new
  receiveScreen sh alice aliceID
  let (_, robertID) ← peopleScreens sh alice aliceID cardB otherAddress
  cardsRefusedOnTheAddPersonSheet sh aliceID
  homeScreens sh alice aliceID robertID bobAddress (← alice.receiveAddress false) funder
  backupScreens sh root alice aliceID 0xA1
  backendRef.set Backend.pending

/-- The explorer and manual-peer rules against what Foundation and the Swift app answered
(`FoundationVectors`, from `scripts/foundation-vectors`): a custom explorer's host, which strings
`explorerBaseURL` keeps (HTTPS anywhere, plain HTTP only on loopback) and how it spells them, the
transaction link under it, and `parsePeer`. -/
def foundationURLRules : IO Unit := do
  let txid := String.join (List.replicate 32 "ab")
  for (s, host, base, tx) in FoundationVectors.urls do
    check s!"url host: {repr s}" (urlHost s == host) s!"{urlHost s}"
    let got := explorerBaseURL .custom s .signet
    check s!"explorer base: {repr s}" (got == base) got
    let link := appendPath got ["tx", txid]
    check s!"transaction link: {repr s}" (link == tx) link
  -- where the app refuses what Foundation accepts: a non-ASCII host (Foundation applies IDNA)
  check "url host: non-ASCII host refused" (urlHost "https://münchen.de" == none)
  check "explorer base: non-ASCII host falls back to the preset"
    (explorerBaseURL .custom "https://münchen.de" .signet == "https://mempool.space/signet")
  for (text, want) in FoundationVectors.peers do
    let got := (parsePeer text).toOption
    check s!"peer: {repr text}" (got == want) s!"{got}"
    check s!"saved peer dials as validated: {repr text}"
      ((Real.parsePeerEndpoint text).map (·.description) == want)

/-! ## Background tasks through `perform` (#68)

iOS launches a task with a system event and expires it with another; the simulator refuses
`bgtask.schedule`, so outside a phone (LeanNative/leannative#22) only this runs them. Each case sends the
shell's event through `system`, the Model and the app's own `perform`, against a shell that records what it
is asked and a backend whose check the case decides, and reads the `bgtask.complete` the shell gets. The
deadline is a manual one (`backgroundDeadline`) that records each run's budget and that the case fires. -/

/-- The shell, for background tasks: what it is asked, each with whether the backend's check had drained
by then. -/
structure TaskShell where
  asked : IO.Ref (Array (String × Lean.Json × Bool))
  drained : IO.Ref Bool

def TaskShell.new : IO TaskShell := do return { asked := ← IO.mkRef #[], drained := ← IO.mkRef true }

def TaskShell.fx (s : TaskShell) : LeanNative.Native.Effects Host where
  post _ := pure ()
  cap _ _ _ := pure ()
  ask name args := do
    let drained ← s.drained.get
    s.asked.modify (·.push (name, args, drained))
    return Task.pure (Lean.Json.mkObj [("ok", Lean.Json.bool true)])

/-- A `bgtask.complete` the shell got: the task, its `success`, whether the check had drained, and the `tag` it
named as sent (none when it named none). -/
abbrev Completion := String × Option Bool × Bool × Option String

/-- The `bgtask.complete`s so far. -/
def TaskShell.completions (s : TaskShell) : IO (Array Completion) := do
  return (← s.asked.get).filterMap fun (n, a, d) =>
    if n == "bgtask.complete" then
      some ((a.getObjValAs? String "id").toOption.getD "", (a.getObjValAs? Bool "success").toOption, d,
        (a.getObjVal? "tag").toOption.map (·.compress))
    else none

/-- The completions once the first has come and a later one has had time to follow. -/
def TaskShell.settled (s : TaskShell) : IO (Array Completion) := do
  discard <| waitUntil 5_000 (every := 2) do return !(← s.completions).isEmpty
  IO.sleep 150
  s.completions

/-- The shell's system event `{key: {id, kind, tag}}` through `system`, the Model and `perform`; without a
`tag` the event names none, as a shell from before LeanNative #67 sends it. -/
def TaskShell.event (s : TaskShell) (key id kind : String) (m : Model) (tag : Option Nat := none) : IO Model := do
  let body := [("id", Lean.Json.str id), ("kind", Lean.Json.str kind)] ++ tag.toList.map fun t => ("tag", Lean.toJson t)
  let some h := system (Lean.Json.mkObj [(key, Lean.Json.mkObj body)])
    | throw (IO.userError s!"{key} is not a system event")
  let (m, cs) := onHost h m
  for c in cs do WinnowApp.perform c s.fx
  return m

/-- The backend's background check as a case decides it: its result, and whether it holds until asked to
stop and then released (`gate`), as the real check drains its networking, or is `slow`: it takes until
the gate opens, asked to stop or not. With `holdsLater`, every check after the first also takes until
`later` opens. Like the real `runBackgroundSync`, it refuses (`false`, counted in `refused`) while another
check runs. -/
structure TaskCheck where
  result : Except String Bool
  holds : Bool
  slow : Bool
  holdsLater : Bool
  runs : IO.Ref (Array String)
  cancels : IO.Ref Nat
  gate : IO.Promise Unit
  later : IO.Promise Unit
  running : IO.Ref Bool
  refused : IO.Ref Nat

def TaskCheck.new (result : Except String Bool) (holds := false) (slow := false) (holdsLater := false) :
    IO TaskCheck := do
  return { result, holds, slow, holdsLater, runs := ← IO.mkRef #[], cancels := ← IO.mkRef 0,
           gate := ← IO.Promise.new, later := ← IO.Promise.new, running := ← IO.mkRef false, refused := ← IO.mkRef 0 }

def TaskCheck.backend (c : TaskCheck) (sh : TaskShell) : Backend :=
  { Backend.pending with
    runBackgroundSync := fun s => do
      if ← c.running.modifyGet fun r => (r, true) then
        c.refused.modify (· + 1)
        return false
      let first ← c.runs.modifyGet fun rs => (rs.isEmpty, rs.push s.network.name)
      sh.drained.set false
      if !first && c.holdsLater then
        while !(← c.later.isResolved) do IO.sleep 2
      else
        if c.holds then
          while (← c.cancels.get) == 0 || !(← c.gate.isResolved) do IO.sleep 2
        if c.slow then
          while !(← c.gate.isResolved) do IO.sleep 2
      sh.drained.set true
      c.running.set false
      match c.result with
      | .ok done => return done
      | .error e => throw (IO.userError e)
    cancelBackgroundSync := c.cancels.modify (· + 1) }

/-- #68: a background task's launch and expiry through `perform`: the budget for its kind, and exactly one
`bgtask.complete` under its id with the run's success and its launch's tag (none for a launch that named
none), whether the check finishes, falls short, fails, or is expired by iOS or its budget, when iOS expires it
after it completed, when iOS launches it again while it runs (the older check stops and drains before the
newer runs, and an expiry naming the older launch leaves the newer run alone, before and after it starts),
when iOS launches both kinds while the app boots (they run one after the other, as the backend refuses a
second check), or one twice, and when iOS expires it before it started. -/
def backgroundTaskCommands : IO Unit := do
  let budgets ← IO.mkRef (#[] : Array (Nat × IO Unit))
  backgroundDeadline.set fun ms => do
    let (d, fire) ← LeanNative.Native.BackgroundRun.Deadline.manual
    budgets.modify (·.push (ms, fire))
    return d
  let refresh := Real.backgroundRefreshID
  let processing := Real.backgroundProcessingID
  let asleep : Model := { readyModel "w" with active := false }
  -- the tag a completion names, as sent
  let tag (n : Nat) : Option String := some (toString n)
  let start (result : Except String Bool) (holds := false) (slow := false) (holdsLater := false) :
      IO (TaskShell × TaskCheck) := do
    let sh ← TaskShell.new
    let c ← TaskCheck.new result holds slow holdsLater
    backendRef.set (c.backend sh)
    budgets.set #[]
    return (sh, c)
  let started (c : TaskCheck) (n := 1) : IO Bool := waitUntil 2_000 (every := 2) do return (← c.runs.get).size == n
  -- a refresh that reaches the tip
  let (sh, c) ← start (.ok true)
  discard <| sh.event "bgtask" refresh "refresh" asleep (some 1)
  let done ← sh.settled
  let schedules := (← sh.asked.get).filterMap fun (n, a, _) =>
    if n == "bgtask.schedule" then some ((a.getObjValAs? String "id").toOption, (a.getObjValAs? String "kind").toOption) else none
  check "refresh task: asks iOS for the next checks, one of each" (schedules.size == 2 &&
    schedules.contains (some refresh, some "refresh") && schedules.contains (some processing, some "processing"))
  check "refresh task: the check runs once, on the wallet's network" ((← c.runs.get) == #["regtest"])
  check "refresh task: 25 s to run" ((← budgets.get).map (·.1) == #[25_000])
  check "refresh task: completed once, successfully, under iOS's id and the launch's tag"
    (done == #[(refresh, some true, true, tag 1)]) (reprStr done)
  check "refresh task: nothing left running" (← WinnowApp.backgroundRuns.get).isEmpty
  -- a launch that names no tag (a shell from before LeanNative #67): its completion names none
  let (sh, _) ← start (.ok true)
  discard <| sh.event "bgtask" refresh "refresh" asleep
  let done ← sh.settled
  check "untagged launch: completed once, successfully, naming no tag" (done == #[(refresh, some true, true, none)]) (reprStr done)
  -- a processing task whose check falls short of the tip
  let (sh, c) ← start (.ok false)
  discard <| sh.event "bgtask" processing "processing" asleep (some 2)
  let done ← sh.settled
  check "processing task: 120 s to run" ((← budgets.get).map (·.1) == #[120_000])
  check "processing task: short of the tip, completed once, unsuccessfully, with its tag"
    (done == #[(processing, some false, true, tag 2)] && (← c.runs.get).size == 1) (reprStr done)
  -- a check that fails
  let (sh, _) ← start (.error "the peer hung up")
  discard <| sh.event "bgtask" refresh "refresh" asleep (some 3)
  let done ← sh.settled
  check "failed check: completed once, unsuccessfully, with its tag" (done == #[(refresh, some false, true, tag 3)]) (reprStr done)
  -- iOS expires it while it runs, twice: the check is stopped once and drains before the completion
  let (sh, c) ← start (.ok true) (holds := true)
  let m ← sh.event "bgtask" processing "processing" asleep (some 4)
  check "expired while running: the check started" (← started c)
  let m ← sh.event "bgtaskExpired" processing "processing" m (some 4)
  discard <| sh.event "bgtaskExpired" processing "processing" m (some 4)
  IO.sleep 50
  check "expired while running: the backend is asked to stop, once" ((← c.cancels.get) == 1)
  check "expired while running: nothing completes until the check drains" (← sh.completions).isEmpty
  c.gate.resolve ()
  let done ← sh.settled
  check "expired while running: completed once, unsuccessfully, with its tag, after the check drained"
    (done == #[(processing, some false, true, tag 4)]) (reprStr done)
  check "expired while running: nothing left running" (← WinnowApp.backgroundRuns.get).isEmpty
  -- the budget runs out: the deadline perform armed expires the run
  let (sh, c) ← start (.ok true) (holds := true)
  discard <| sh.event "bgtask" refresh "refresh" asleep (some 5)
  check "budget spent: the check started" (← started c)
  let some (ms, fire) := (← budgets.get)[0]? | throw (IO.userError "no deadline was armed")
  check "budget spent: a refresh's 25 s" (ms == 25_000)
  fire
  IO.sleep 50
  check "budget spent: the backend is asked to stop" ((← c.cancels.get) == 1 && (← sh.completions).isEmpty)
  c.gate.resolve ()
  let done ← sh.settled
  check "budget spent: completed once, unsuccessfully, with its tag" (done == #[(refresh, some false, true, tag 5)]) (reprStr done)
  -- iOS's expiry comes after the check completed: the task has had its one answer
  let (sh, _) ← start (.ok true)
  let m ← sh.event "bgtask" processing "processing" asleep (some 6)
  let done ← sh.settled
  check "expired after it completed: completed once, successfully, with its tag"
    (done == #[(processing, some true, true, tag 6)]) (reprStr done)
  discard <| sh.event "bgtaskExpired" processing "processing" m (some 6)
  IO.sleep 50
  let done ← sh.completions
  check "expired after it completed: the late expiry answers nothing" (done == #[(processing, some true, true, tag 6)]) (reprStr done)
  -- iOS launches the task again while its check still runs (the shell has ended the first): the older
  -- check is stopped and drains, the newer one runs after it and answers the shell, once, with its own result
  -- and its own launch's tag
  let (sh, c) ← start (.ok true) (holds := true)
  let m ← sh.event "bgtask" refresh "refresh" asleep (some 7)
  check "launched again: the first check started" (← started c)
  discard <| sh.event "bgtask" refresh "refresh" m (some 8)
  IO.sleep 50
  check "launched again: the older check is asked to stop, once" ((← c.cancels.get) == 1)
  check "launched again: the newer check waits for the older to drain"
    ((← c.runs.get).size == 1 && (← sh.completions).isEmpty)
  check "launched again: one run registered under the id"
    (((← WinnowApp.backgroundRuns.get).filter (·.1 == refresh)).length == 1)
  c.gate.resolve ()
  let done ← sh.settled
  check "launched again: the newer check runs once the older drained" ((← c.runs.get).size == 2)
  check "launched again: completed once, by the newer run, successfully, with the newer launch's tag"
    (done == #[(refresh, some true, true, tag 8)]) (reprStr done)
  check "launched again: each launch its 25 s" ((← budgets.get).map (·.1) == #[25_000, 25_000])
  check "launched again: nothing left running" (← WinnowApp.backgroundRuns.get).isEmpty
  -- launched again, and then the shell's expiry of the older launch arrives while the newer waits for it to
  -- drain: the newer run is not expired
  let (sh, c) ← start (.ok true) (holds := true)
  let m ← sh.event "bgtask" refresh "refresh" asleep (some 9)
  check "older launch expired, newer waiting: the first check started" (← started c)
  let m ← sh.event "bgtask" refresh "refresh" m (some 10)
  discard <| sh.event "bgtaskExpired" refresh "refresh" m (some 9)
  IO.sleep 50
  check "older launch expired, newer waiting: nothing more is stopped, nothing answered"
    ((← c.cancels.get) == 1 && (← sh.completions).isEmpty)
  c.gate.resolve ()
  let done ← sh.settled
  check "older launch expired, newer waiting: the newer check runs and completes successfully, with its tag"
    ((← c.runs.get).size == 2 && done == #[(refresh, some true, true, tag 10)]) (reprStr done)
  -- the same, with the older launch's expiry arriving once the newer check runs
  let (sh, c) ← start (.ok true) (holds := true) (holdsLater := true)
  let m ← sh.event "bgtask" refresh "refresh" asleep (some 11)
  check "older launch expired, newer running: the first check started" (← started c)
  let m ← sh.event "bgtask" refresh "refresh" m (some 12)
  c.gate.resolve ()
  check "older launch expired, newer running: the newer check started" (← started c 2)
  discard <| sh.event "bgtaskExpired" refresh "refresh" m (some 11)
  IO.sleep 50
  check "older launch expired, newer running: it keeps running, nothing more is stopped, nothing answered"
    ((← c.cancels.get) == 1 && (← sh.completions).isEmpty &&
      ((← WinnowApp.backgroundRuns.get).map (·.2.2.1)) == [some 12])
  c.later.resolve ()
  let done ← sh.settled
  check "older launch expired, newer running: completed once, successfully, with the newer launch's tag"
    (done == #[(refresh, some true, true, tag 12)]) (reprStr done)
  check "older launch expired, newer running: nothing left running" (← WinnowApp.backgroundRuns.get).isEmpty
  -- launched during boot: it waits for the wallet, then runs
  let (sh, c) ← start (.ok true)
  let m ← sh.event "bgtask" refresh "refresh" {} (some 13)
  check "launched during boot: waits for the wallet" (!m.pendingBackgroundTasks.isEmpty && (← c.runs.get).isEmpty)
  let (_, cs) := onHost (.booted 0 (.opened "w")) m
  for cmd in cs.filter (· matches .runBackgroundTask ..) do WinnowApp.perform cmd sh.fx
  let done ← sh.settled
  check "launched during boot: runs once the wallet opens, completes once, with its tag"
    (done == #[(refresh, some true, true, tag 13)] && (← c.runs.get).size == 1) (reprStr done)
  -- boot lands: perform the runs it starts, then the completions once `n` have come
  let boot (sh : TaskShell) (m : Model) (n : Nat) : IO (Array Completion) := do
    let (_, cs) := onHost (.booted 0 (.opened "w")) m
    for cmd in cs.filter (· matches .runBackgroundTask ..) do WinnowApp.perform cmd sh.fx
    discard <| waitUntil 5_000 (every := 2) do return (← sh.completions).size ≥ n
    IO.sleep 150
    sh.completions
  -- iOS launches both kinds while the app boots: each waits, and once the wallet opens they run one after
  -- the other (the backend refuses a second check while one runs), each to its own success
  let (sh, c) ← start (.ok true) (slow := true)
  let m ← sh.event "bgtask" refresh "refresh" {} (some 14)
  let m ← sh.event "bgtask" processing "processing" m (some 15)
  check "two launched during boot: both wait for the wallet"
    (m.pendingBackgroundTasks.map (·.1) == [refresh, processing] && (← c.runs.get).isEmpty)
  let (_, cs) := onHost (.booted 0 (.opened "w")) m
  for cmd in cs.filter (· matches .runBackgroundTask ..) do WinnowApp.perform cmd sh.fx
  check "two launched during boot: the first check starts" (← started c)
  IO.sleep 50
  check "two launched during boot: the second waits for the first, nothing refused or completed"
    ((← c.runs.get).size == 1 && (← c.refused.get) == 0 && (← sh.completions).isEmpty)
  c.gate.resolve ()
  discard <| waitUntil 5_000 (every := 2) do return (← sh.completions).size ≥ 2
  IO.sleep 150
  let done ← sh.completions
  check "two launched during boot: each runs once the wallet opens, with its kind's budget, none refused"
    ((← c.runs.get).size == 2 && (← c.refused.get) == 0 && (← budgets.get).map (·.1) == #[25_000, 120_000])
  check "two launched during boot: completed one after the other, successfully, each under its own id and tag"
    (done == #[(refresh, some true, true, tag 14), (processing, some true, true, tag 15)]) (reprStr done)
  check "two launched during boot: nothing left running" (← WinnowApp.backgroundRuns.get).isEmpty
  -- one of the two expires before boot lands: it is answered at once, with its tag, the other still runs
  let (sh, c) ← start (.ok true)
  let m ← sh.event "bgtask" refresh "refresh" {} (some 16)
  let m ← sh.event "bgtask" processing "processing" m (some 17)
  let m ← sh.event "bgtaskExpired" refresh "refresh" m (some 16)
  let done ← boot sh m 2
  check "one of two expired during boot: it completes unsuccessfully, the other runs and completes, each with its tag"
    (done == #[(refresh, some false, true, tag 16), (processing, some true, true, tag 17)] && (← c.runs.get).size == 1 &&
      (← budgets.get).map (·.1) == #[120_000]) (reprStr done)
  -- the same task launched twice during boot (the shell has ended the first): it runs once, as the second
  let (sh, c) ← start (.ok true)
  let m ← sh.event "bgtask" refresh "refresh" {} (some 18)
  let m ← sh.event "bgtask" refresh "refresh" m (some 19)
  check "launched twice during boot: waits once" (m.pendingBackgroundTasks == [(refresh, "refresh", some 19)])
  let done ← boot sh m 1
  check "launched twice during boot: runs once, completes once, with the second launch's tag"
    (done == #[(refresh, some true, true, tag 19)] && (← c.runs.get).size == 1) (reprStr done)
  -- launched twice during boot, and the first launch's expiry arrives before boot lands: the second waits on
  let (sh, c) ← start (.ok true)
  let m ← sh.event "bgtask" refresh "refresh" {} (some 20)
  let m ← sh.event "bgtask" refresh "refresh" m (some 21)
  let m ← sh.event "bgtaskExpired" refresh "refresh" m (some 20)
  IO.sleep 50
  check "older launch expired during boot: the newer still waits, nothing answered"
    (m.pendingBackgroundTasks == [(refresh, "refresh", some 21)] && (← sh.completions).isEmpty)
  let done ← boot sh m 1
  check "older launch expired during boot: the newer runs once, completes once, successfully, with its tag"
    (done == #[(refresh, some true, true, tag 21)] && (← c.runs.get).size == 1) (reprStr done)
  -- expired before it started: iOS's time ran out while the app was still booting; with and without a tag
  for t in [some 22, none] do
    let (sh, c) ← start (.ok true)
    let m ← sh.event "bgtask" refresh "refresh" {} t
    let m ← sh.event "bgtaskExpired" refresh "refresh" m t
    let m ← sh.event "bgtaskExpired" refresh "refresh" m t
    let done ← sh.settled
    check s!"expired before it started (tag {t}): completed once, unsuccessfully, however often iOS says so, with its tag"
      (done == #[(refresh, some false, true, t.map toString)]) (reprStr done)
    let (_, cs) := onHost (.booted 0 (.opened "w")) m
    check s!"expired before it started (tag {t}): boot does not run it, no check ran"
      (!cs.any (· matches .runBackgroundTask ..) && (← c.runs.get).isEmpty && (← budgets.get).isEmpty)
  backgroundDeadline.set fun ms => pure (.after ms)
  backendRef.set Backend.pending

/-- #68: test mode pins the seed one way, `WINNOW_E2E_ENTROPY`. A run that sets only Swift's
`WINNOW_E2E_MNEMONIC`, or entropy that is not hex, stops rather than create a real seed. -/
def testModeSeed : IO Unit := do
  let resolve (vars : List (String × String)) := WinnowApp.E2E.resolve fun k => ((("WINNOW_E2E", "1") :: vars).lookup k)
  check "test mode: WINNOW_E2E_ENTROPY pins the seed"
    (match resolve [("WINNOW_E2E_ENTROPY", "000102030405060708090a0b0c0d0e0f")] with
     | .active m => m.entropy.map (·.toList) == some ((List.range 16).map (·.toUInt8))
     | _ => false)
  check "test mode: a recovery phrase alone pins nothing"
    (resolve [("WINNOW_E2E_MNEMONIC", "abandon abandon abandon abandon abandon abandon abandon abandon abandon abandon abandon about")]
      matches .missingPinnedEntropy)
  check "test mode: entropy that is not hex pins nothing" (resolve [("WINNOW_E2E_ENTROPY", "abandon")] matches .missingPinnedEntropy)
  check "test mode: nothing set pins nothing" (resolve [] matches .missingPinnedEntropy)
  check "test mode: the launch reads one seed variable"
    (WinnowApp.e2eVariables.filter (fun v => v == "WINNOW_E2E_ENTROPY" || v == "WINNOW_E2E_MNEMONIC") == ["WINNOW_E2E_ENTROPY"])

/-- A network's wallets on disk: the first in the network's own directory, the others in numbered slots,
found by their `wallet.json` and by nothing else; which was open last is one small file that may be wrong. -/
def walletSlots (root : System.FilePath) : IO Unit := do
  let net := (root / "slots" / "signet").toString
  IO.FS.createDirAll net
  check "slots: the network's own directory is the empty slot"
    (Real.slotDir net "" == net && Real.slotOf net == "" && Real.networkDirOf net == net)
  let two := Real.slotDir net "2"
  check "slots: an added wallet's directory is under wallets/"
    (two == s!"{net}/wallets/2" && Real.slotOf two == "2" && Real.networkDirOf two == net) two
  check "slots: a directory that only looks like one is its own network's"
    (Real.networkDirOf s!"{net}/wallets/x" == s!"{net}/wallets/x" && Real.networkDirOf s!"{net}/other/2" == s!"{net}/other/2")
  check "slots: none while no wallet is kept"
    ((← Real.listSlots net) == [] && (← Real.freeSlot net) == "" && (← Real.resolveSlot net) == "")
  IO.FS.writeFile (Real.walletPath net) "{}"
  check "slots: the first wallet" ((← Real.listSlots net) == [""] && (← Real.freeSlot net) == "1")
  -- an addition that never finished left files and no wallet
  let one := Real.slotDir net "1"
  IO.FS.createDirAll one
  IO.FS.writeFile (Real.dirFile one "people.json") "left behind"
  check "slots: a slot without a wallet is not one" ((← Real.listSlots net) == [""])
  check "slots: …and is cleared before it is used again"
    ((← Real.freeSlot net) == "1" && !(← (Real.dirFile one "people.json").pathExists))
  IO.FS.writeFile (Real.walletPath one) "{}"
  let three := Real.slotDir net "3"
  IO.FS.createDirAll three
  IO.FS.writeFile (Real.walletPath three) "{}"
  check "slots: listed in order, the next free one between them"
    ((← Real.listSlots net) == ["", "1", "3"] && (← Real.freeSlot net) == "2") s!"{← Real.listSlots net}"
  check "slots: with no pointer, the first" ((← Real.resolveSlot net) == "")
  Real.writeActiveSlot net "3"
  check "slots: the one open last" ((← Real.resolveSlot net) == "3")
  IO.FS.removeFile (Real.walletPath three)
  check "slots: a pointer to a wallet that is gone falls back to the first" ((← Real.resolveSlot net) == "")
  Real.writeActiveSlot net "../../elsewhere"
  check "slots: a pointer that names no slot opens nothing else" ((← Real.resolveSlot net) == "")
  Real.discardEmptySlot three
  check "slots: an empty added slot is taken away" (!(← (System.FilePath.mk three).pathExists))
  Real.discardEmptySlot one
  Real.discardEmptySlot net
  check "slots: one that holds a wallet, and the network's own, are left" ((← Real.listSlots net) == ["", "1"])
  check "slots: the gateways answer is one file beside the networks, whichever wallet asks"
    (Real.gatewaysUsedPath net == Real.gatewaysUsedPath two &&
     Real.gatewaysUsedPath net == System.FilePath.mk s!"{root}/slots/peer-gateways.automatic-used")
    s!"{Real.gatewaysUsedPath two}"

/-- Several wallets for one network, as the screens and the commands have them: Settings lists them and opens
another; adding one is onboarding in an empty place, with a way back; and a command acts in the place that
was open when it was given. -/
def walletSwitcher (root : System.FilePath) : IO Unit := do
  let two : List WalletSummary := [{ id := "aaaa1111", slot := "", active := true }, { id := "bbbb2222", slot := "1" }]
  let ready : Model := { stage := .ready, active := true, walletID := some "aaaa1111", wallets := two }
  let page := rendered { ready with routes := [.settings] }
  check "wallets: Settings lists the profiles kept, the open one marked, and offers one more and a rename"
    (contains page "Wallet aaaa1111" && contains page "Wallet bbbb2222" && contains page "Add a profile" && contains page Ids.addWalletButton &&
     contains page Ids.renameWalletButton)
  check "wallets: the Danger zone names the profile it deletes" (contains page "Removes Wallet aaaa1111 (aaaa1111)")
  -- the home: the open profile's name, which opens the list; a rename goes to the backend and closes its sheet
  let home := (LeanNative.Html.toWire (view ready)).toJson.compress
  check "wallets: the home names the open profile" (contains home Ids.walletNameButton && contains home "Wallet aaaa1111")
  let (listed, _) := step (.home .openWallets) ready
  check "wallets: …and its name opens the list of profiles" (listed.sheets == [.wallets])
  let (naming, _) := step (.settings .openRename) listed
  let (typed, _) := step (.settings (.setRenameDraft "Household")) naming
  let (saving, cs) := step (.settings .saveRename) typed
  check "wallets: a name is asked for and saved" (naming.sheets.getLast? == some .renameWallet && saving.renameBusy &&
    cs.any fun c => c matches .renameWallet _ "Household")
  let (refused, _) := onHost (.renamed saving.generation (some "A name is one short line of text.")) saving
  check "wallets: a refused name says why, and the sheet stays" (refused.renameError.isSome && refused.sheets.getLast? == some .renameWallet)
  let (named, _) := onHost (.renamed saving.generation none) saving
  check "wallets: a saved name closes its sheet" (!named.sheets.contains .renameWallet && !named.renameBusy)
  let (renamedList, _) := onHost (.walletPlace named.generation "" [{ id := "aaaa1111", slot := "", active := true, name := "Household" },
    { id := "bbbb2222", slot := "1" }]) named
  check "wallets: the new name is shown" (contains (LeanNative.Html.toWire (view renamedList)).toJson.compress "Household")
  -- accounts by key: this profile's on the home, the others folded under one row, said where they sign
  let ours : MultisigInfo := { id := "a1", name := "Ours", descriptor := "", balance := 5 }
  let theirs : MultisigInfo := { id := "a2", name := "Theirs", descriptor := "", balance := 7, signsHere := false, signsIn := some "Phone" }
  let withAccounts := { ready with multisig := { accounts := [ours, theirs] } }
  let home := (LeanNative.Html.toWire (view withAccounts)).toJson.compress
  check "accounts: the home lists this profile's account and folds the other under Watching"
    (contains home "Ours" && !contains home "Theirs" && contains home Ids.homeWatchingRow && contains home "Watching 1 account" &&
     contains home "in 1 multisig account")
  let list := (LeanNative.Html.toWire (multisigSection withAccounts)).toJson.compress
  check "accounts: the full list says where the other one signs" (contains list "Theirs" && contains list "Signs in Phone")
  let (same, cs) := step (.settings (.selectWallet "")) ready
  check "wallets: the open wallet chosen again changes nothing" (same.generation == ready.generation && cs.isEmpty)
  let (_, cs) := step (.settings (.selectWallet "7")) ready
  check "wallets: a place that keeps none is not opened" cs.isEmpty
  let (switching, cs) := step (.settings (.selectWallet "1")) ready
  check "wallets: another one chosen: its place is opened, in a new generation, and networking goes on (it is the network's)"
    (switching.stage == .loading && switching.walletID.isNone && switching.generation > ready.generation &&
     !cs.any (· matches .stopNetworking) && cs.any fun c => c matches .openSlot _ _ (some "1"))
  let (stale, _) := onHost (.booted ready.generation (.opened "aaaa1111")) switching
  check "wallets: an answer about the wallet left behind is dropped" (stale.stage == .loading && stale.walletID.isNone)
  let (placed, _) := onHost (.walletPlace switching.generation "1" [{ id := "aaaa1111", slot := "" }, { id := "bbbb2222", slot := "1", active := true }]) switching
  let (opened, _) := onHost (.booted switching.generation (.opened "bbbb2222")) placed
  check "wallets: the other wallet is open" (opened.stage == .ready && opened.walletID == some "bbbb2222" && opened.slot == "1")
  -- one more, added beside them
  let (adding, cs) := step (.settings .addWallet) ready
  check "wallets: adding one opens an empty place" (adding.stage == .loading && cs.any fun c => c matches .openSlot _ _ none)
  let (placed, _) := onHost (.walletPlace adding.generation "2" two) adding
  let (empty, cs) := onHost (.booted adding.generation .missing) placed
  let screen := (LeanNative.Html.toWire (view empty)).toJson.compress
  check "wallets: …where onboarding is \"Add a wallet\", with a way back and no change of network"
    (empty.stage == .onboarding && contains screen "Add a profile" && contains screen Ids.cancelAddWalletButton &&
     contains screen Ids.createWalletButton && !contains screen Ids.onboardingTestNetwork && cs.any (· matches .discoverCloud))
  let first : Model := { stage := .onboarding }
  check "wallets: a first wallet's onboarding is as it was"
    (!contains (LeanNative.Html.toWire (view first)).toJson.compress Ids.cancelAddWalletButton &&
     contains (LeanNative.Html.toWire (view first)).toJson.compress Ids.onboardingTestNetwork)
  let (back, cs) := step (.settings .cancelAddWallet) empty
  check "wallets: Cancel goes back to the wallet that was open"
    (back.stage == .loading && cs.any fun c => c matches .openWallet _ _ false)
  let (stay, cs) := step (.settings .cancelAddWallet) ready
  check "wallets: Cancel means nothing with a wallet open" (stay.stage == .ready && cs.isEmpty)
  let (created, _) := onHost (.created empty.generation "cccc3333") empty
  check "wallets: a wallet made there is the one open" (created.stage == .ready && created.walletID == some "cccc3333")
  -- a command acts in the place that was open when it was given
  rootDir.set root.toString
  openPlace.set (some (5, .signet, "1"))
  let dirOf (g : Nat) (n : Network) : IO (Option String) := do
    match ← (placeDir g n).toBaseIO with | .ok d => pure (some d) | .error _ => pure none
  check "wallets: a command given after the place was opened acts there"
    ((← dirOf 5 .signet) == some s!"{root}/signet/wallets/1" && (← dirOf 9 .signet) == some s!"{root}/signet/wallets/1")
  check "wallets: one given before it, for the wallet open then, is refused" ((← dirOf 4 .signet).isNone)
  check "wallets: and one for another network" ((← dirOf 6 .mainnet).isNone)
  openPlace.set none

/-- The version Settings shows is the bundle's, read from its `Info.plist` in either form a build writes one,
and never a number made up here: a file cut short, a file that is something else, or a build setting left
unexpanded gives none, and Settings then says Unknown. -/
def bundleVersion : IO Unit := do
  let xml (version build : String) : String :=
    "<?xml version=\"1.0\" encoding=\"UTF-8\"?>\n<plist version=\"1.0\">\n<dict>\n" ++
    "\t<key>CFBundleIdentifier</key>\n\t<string>com.btcswift.app</string>\n" ++
    s!"\t<key>CFBundleShortVersionString</key>\n\t<string>{version}</string>\n" ++
    s!"\t<key>CFBundleVersion</key>\n\t<string>{build}</string>\n</dict>\n</plist>\n"
  let read (s : String) : Option String := BundleInfo.versionText? s.toUTF8
  check "version: an XML Info.plist" (read (xml "0.9.19" "26") == some "0.9.19 (26)") s!"{read (xml "0.9.19" "26")}"
  check "version: a build setting left unexpanded is not a version"
    (read (xml "$(MARKETING_VERSION)" "$(CURRENT_PROJECT_VERSION)") == none && read (xml "0.9.19" "") == none)
  check "version: without a build number there is none" (read ((xml "0.9.19" "26").replace "CFBundleVersion" "Other") == none)
  check "version: the string must be the key's own"
    (read ((xml "0.9.19" "26").replace "<string>0.9.19</string>" "<true/>") == none)
  check "version: not a property list" (read "not a plist" == none && BundleInfo.versionText? .empty == none)
  -- plutil's binary form of such a file (`plutil -convert binary1`), its display name a UTF-16 string
  let binary := Winnow.ofHex! <|
    "62706c6973743030d50102030405060708090a5f101a434642756e646c6553686f727456657273696f6e537472696e675f1013" ++
    "434642756e646c65446973706c61794e616d655f100f434642756e646c6556657273696f6e5f1012434642756e646c654964656e" ++
    "7469666965725f10124c5352657175697265734950686f6e654f5356302e392e31396600570069006e006e00f600775232365f10" ++
    "10636f6d2e62746373776966742e6170700908133046586d82899699ac0000000000000101000000000000000b00000000000000" ++
    "0000000000000000ad"
  check "version: a binary Info.plist" (BundleInfo.versionText? binary == some "0.9.19 (26)") s!"{BundleInfo.versionText? binary}"
  check "version: a binary plist's UTF-16 string" (BundleInfo.binaryString? binary "CFBundleDisplayName" == some "Winnöw")
  check "version: a key a binary plist lacks" (BundleInfo.binaryString? binary "CFBundleName" == none)
  check "version: a binary plist cut short is none at every length"
    ((List.range binary.size).all fun n => BundleInfo.versionText? (binary.extract 0 n) == none)
  -- Settings → About: what launch read, and Unknown until then
  let settings (m : Model) : String := rendered (update (.home .openSettings) m)
  let unread := settings (readyModel "w")
  check "version: Settings says Unknown before launch has read it" (contains unread "Unknown" && !contains unread "0.1.0")
  let read := settings (update (.host (.versionRead "0.9.19 (26)")) (readyModel "w"))
  check "version: Settings shows the bundle's version" (contains read "0.9.19 (26)" && !contains read "Unknown")

/-- Records an earlier build locked behind Face ID: the home says so and offers the one tap that frees them,
which asks for an authentication and nothing else; with nothing locked there is neither. -/
def recordsLockedRow : IO Unit := do
  let ready : Model := { stage := .ready, active := true, walletID := some "w" }
  check "locked records: nothing is said while none is locked"
    (!contains (rendered ready) Ids.unlockRecordsButton && (step .unlockRecords ready).2.isEmpty)
  let locked := { ready with status := { ready.status with recordsLocked := true } }
  check "locked records: the home says so, with one button" (contains (rendered locked) Ids.unlockRecordsButton &&
    contains (rendered locked) "Unlock with Face ID")
  check "locked records: the tap asks for the authentication" ((step .unlockRecords locked).2.any (· matches .unlockRecords _))

/-- Continued background sync (iOS 26 `BGContinuedProcessingTask`): every manual sync requests one while
foreground-active, keeps networking alive across backgrounding, streams privacy-safe progress, and tears
down cleanly on completion, failure, expiry/cancel, refusal, or wallet/network switch. -/
def continuedBackgroundSync : IO Unit := do
  -- privacy-safe Live Activity copy & progress
  check "continued copy: titles per network"
    (continuedSyncTitle .mainnet == "Syncing Bitcoin" &&
     continuedSyncTitle .signet == "Syncing Signet" &&
     continuedSyncTitle .regtest == "Syncing Regtest")
  check "continued copy: idle/connecting/headers/filters/synced/failed progress"
    (continuedSyncProgress .idle == (0, 100, "Starting sync…") &&
     continuedSyncProgress (.connecting 2 3) == (2, 3, "Connecting to peers… (2/3)") &&
     continuedSyncProgress (.connecting 0 0) == (0, 1, "Connecting to peers…") &&
     continuedSyncProgress (.headers 840000 900000) == (840000, 900000, "Checking headers… 840,000 / 900,000") &&
     continuedSyncProgress (.headers 12 0) == (0, 100, "Checking headers… 12") &&
     continuedSyncProgress (.headers 0 0) == (0, 100, "Checking headers…") &&
     continuedSyncProgress (.filters 12400 15000) == (12400, 15000, "Scanning blocks… 12,400 / 15,000") &&
     continuedSyncProgress (.filters 0 0) == (0, 100, "Scanning blocks…") &&
     continuedSyncProgress .synced == (99, 100, "Finishing sync…") &&
     continuedSyncProgress .peerDiscoveryFailed == (0, 100, "No peers reachable"))
  let idMain := continuedSyncID .mainnet 1
  let idMain2 := continuedSyncID .mainnet 2
  let idSignet := continuedSyncID .signet 1
  check "continued id: bundle-prefixed, single-label suffix under the wildcard"
    (idMain == "com.btcswift.app.chain-sync.mainnet-1" &&
     idMain2 == "com.btcswift.app.chain-sync.mainnet-2" &&
     idMain.startsWith Real.backgroundContinuedPrefix &&
     idMain.startsWith (WinnowApp.manifest.bundleId ++ ".") &&
     !(idMain.drop Real.backgroundContinuedPrefix.length).contains '.')
  -- plain foreground activation does NOT request a continued task
  let readyMain : Model := { stage := .ready, active := true, walletID := some "w", settings := { network := .mainnet } }
  let (activated, cs) := onHost (.scene true) { readyMain with active := false }
  check "continued: plain scene active does not request a continued task"
    (activated.continuedSync.isNone && !cs.any (· matches .continueBackgroundSync ..))
  -- automatic foreground catch-up sync requests continuation once, and stays quiet on already-synced polls
  let (mPoll, cs) := onHost (.snapshot 0 { readyMain.status with syncing := true } .synced) readyMain
  check "continued: routine synced poll does not auto-request bgtask.continue"
    (mPoll.continuedSync.isNone && !cs.any (· matches .continueBackgroundSync ..))
  let (mAuto, cs) := onHost (.snapshot 0 { readyMain.status with syncing := true } (.filters 100 5000)) readyMain
  check "continued: automatic foreground catch-up sync requests bgtask.continue"
    (mAuto.continuedSync == some (.requested idMain .mainnet 0 true) &&
     mAuto.continuedSyncSerial == 1 &&
     cs.any (· matches .continueBackgroundSync _ "Syncing Bitcoin" "Scanning blocks… 100 / 5,000"))
  -- refusal suppresses repeated auto-requests on subsequent ticks, records error/detail for Sync screen,
  -- and re-enables auto-requests once synced (except `unavailable`, which stays suppressed)
  let (mAutoRef, _) := onHost (.continuedSyncRefused idMain "tooManyPending" "queue full") mAuto
  check "continued: refusal records error/detail and suppresses auto-retry while still syncing"
    (mAutoRef.continuedSync.isNone && mAutoRef.continuedSyncAutoSuppressed &&
     mAutoRef.continuedSyncOutcome == .refused "tooManyPending" "queue full" &&
     continuedSyncStatusText mAutoRef == "Refused (tooManyPending: queue full)")
  let (mAutoStill, cs) := onHost (.snapshot 0 { mAutoRef.status with syncing := true } (.filters 200 5000)) mAutoRef
  check "continued: suppressed auto-sync does not spam bgtask.continue"
    (mAutoStill.continuedSync.isNone && !cs.any (· matches .continueBackgroundSync ..))
  let (mAutoCleared, _) := onHost (.snapshot 0 { mAutoStill.status with syncing := false } .synced) mAutoStill
  check "continued: reaching synced clears non-unavailable suppression for the next pass"
    (!mAutoCleared.continuedSyncAutoSuppressed)
  let (mAutoNext, cs) := onHost (.snapshot 0 { mAutoCleared.status with syncing := true } (.headers 10 20)) mAutoCleared
  check "continued: next catch-up pass gets a fresh unique task id"
    (mAutoNext.continuedSync == some (.requested idMain2 .mainnet 0 true) &&
     cs.any (fun c => match c with | .continueBackgroundSync id .. => id == idMain2 | _ => false))
  let (mUnavail, _) := onHost (.continuedSyncRefused idMain2 "unavailable" "needs iOS 26") mAutoNext
  let (mUnavailSynced, _) := onHost (.snapshot 0 { mUnavail.status with syncing := false } .synced) mUnavail
  check "continued: unavailable stays suppressed even after sync finishes"
    (mUnavailSynced.continuedSyncAutoSuppressed && continuedSyncStatusText mUnavailSynced == "Unavailable")
  -- manual trigger after refusal always tries again with a fresh id
  let (mManualAfterRef, cs) := step .syncNow mAutoRef
  check "continued: manual Sync now overrides auto suppression with fresh id"
    (mManualAfterRef.continuedSync == some (.requested idMain2 .mainnet 0 false) &&
     !mManualAfterRef.continuedSyncAutoSuppressed &&
     cs.any (fun c => match c with | .continueBackgroundSync id .. => id == idMain2 | _ => false))
  -- manual sync triggers: Sync now, Retry, Verify from genesis (ON only), iCloud restore, file import, finishOnboarding
  let (m1, cs) := step .syncNow readyMain
  check "continued: Sync now while active requests bgtask.continue"
    (m1.continuedSync == some (.requested idMain .mainnet 0 false) &&
     cs.any (· matches .syncNow 0) &&
     cs.any (· matches .continueBackgroundSync _ "Syncing Bitcoin" _))
  let (mInactive, cs) := step .syncNow { readyMain with active := false }
  check "continued: Sync now while inactive does not request bgtask.continue"
    (mInactive.continuedSync.isNone && !cs.any (· matches .continueBackgroundSync ..))
  let (mRetry, cs) := step .retryPeers readyMain
  check "continued: Retry requests bgtask.continue"
    (mRetry.continuedSync.isSome && cs.any (· matches .retryPeers 0) && cs.any (· matches .continueBackgroundSync ..))
  let (mGenOn, cs) := step (.settings (.setVerifyFromGenesis true)) readyMain
  check "continued: turning Verify from genesis on requests bgtask.continue"
    (mGenOn.continuedSync.isSome && cs.any (· matches .reconnect ..) && cs.any (· matches .continueBackgroundSync ..))
  let (mGenOff, cs) := step (.settings (.setVerifyFromGenesis false)) { readyMain with settings := { readyMain.settings with verifyFromGenesis := true } }
  check "continued: turning Verify from genesis off does not request bgtask.continue"
    (mGenOff.continuedSync.isNone && !cs.any (· matches .continueBackgroundSync ..))
  let onboarding : Model := { stage := .onboarding, active := true, settings := { network := .signet } }
  let (mCloud, cs) := step (.cloud (.restore "backup-1")) onboarding
  check "continued: iCloud restore requests bgtask.continue"
    (mCloud.continuedSync == some (.requested idSignet .signet 0 false) &&
     cs.any (· matches .restoreCloud ..) && cs.any (· matches .continueBackgroundSync _ "Syncing Signet" _))
  let (mImport, cs) := step .importWallet { onboarding with onboarding := { importText := "{}" } }
  check "continued: file import requests bgtask.continue"
    (mImport.continuedSync == some (.requested idSignet .signet 0 false) &&
     cs.any (· matches .importWallet ..) && cs.any (· matches .continueBackgroundSync ..))
  let (mFinSync, cs) := step .finishOnboarding { onboarding with walletID := some "w", phase := .filters 10 20 }
  check "continued: finishOnboarding requests bgtask.continue when still syncing"
    (mFinSync.continuedSync.isSome && cs.any (· matches .continueBackgroundSync ..))
  let (mFinDone, cs) := step .finishOnboarding { onboarding with walletID := some "w", phase := .synced }
  check "continued: finishOnboarding skips bgtask.continue when already synced"
    (mFinDone.continuedSync.isNone && !cs.any (· matches .continueBackgroundSync ..))
  -- full background continuation flow: request -> iOS launches -> background -> progress -> synced -> complete + stopNetworking
  let (m, _) := step .syncNow { readyMain with phase := .connecting 1 3 }
  check "continued Sync row: shows Starting… while requested"
    (continuedSyncStatusText m == "Starting…" &&
     contains (LeanNative.Html.toWire (.list (syncSections m) : H)).toJson.compress Ids.continuedSyncStatus)
  let (m, cs) := onHost (.bgtask idMain "continued" (some 7)) m
  check "continued: launch transitions to running, sends initial progress, does not run periodic check"
    (m.continuedSync == some (.running idMain .mainnet 0 (some 7) false) &&
     continuedSyncStatusText m == "Active" &&
     (match cs with
      | [.progressBackgroundSync id (some 7) 1 3 "Syncing Bitcoin" "Connecting to peers… (1/3)"] => id == idMain
      | _ => false))
  -- duplicate manual sync while already running reuses the task instead of submitting a second one
  let (mDup, cs) := step .syncNow m
  check "continued: second manual sync reuses running task"
    (mDup.continuedSync == some (.running idMain .mainnet 0 (some 7) false) &&
     !cs.any (· matches .continueBackgroundSync ..) &&
     cs.any (· matches .progressBackgroundSync ..))
  -- swipe away to background while syncing: sensitive sheets close, periodic tasks schedule, networking stays alive!
  let mWithSecret := (m.present .revealPhrase)
  let (bg, cs) := onHost (.scene false) mWithSecret
  check "continued: leaving app keeps networking alive while closing sensitive sheets and scheduling periodic tasks"
    (!bg.active && bg.sheets.isEmpty && bg.generation == 1 &&
     bg.continuedSync == some (.running idMain .mainnet 0 (some 7) false) &&
     !cs.any (· matches .stopNetworking) &&
     cs.any (· matches .scheduleBackgroundTasks) &&
     cs.any (· matches .cloudScene false))
  -- snapshot from the kept watcher (syncGen = 0) is accepted across the generation bump and reports progress
  let (bg2, cs) := onHost (.snapshot 0 { bg.status with syncing := true } (.filters 12000 15000)) bg
  check "continued: background snapshot advances progress with tag"
    (bg2.phase == .filters 12000 15000 &&
     bg2.continuedSync == some (.running idMain .mainnet 0 (some 7) true) &&
     (match cs with
      | [.progressBackgroundSync id (some 7) 12000 15000 "Syncing Bitcoin" "Scanning blocks… 12,000 / 15,000"] => id == idMain
      | _ => false))
  -- a single transient sync error keeps going; 3 transient errors or peerDiscoveryFailed stops cleanly
  let (bgTrans, cs) := onHost (.snapshot 0
    { bg2.status with syncing := false, lastSyncError := some "peer dropped", transientSyncError := some "peer dropped", transientSyncFailures := 1 }
    (.filters 12000 15000)) bg2
  check "continued: one transient error keeps continued sync alive"
    (bgTrans.continuedSync.isSome && !cs.any (· matches .completeBackgroundTask ..) && !cs.any (· matches .stopNetworking))
  -- reaching synced while backgrounded completes with success=true AND stops networking
  let (bgDone, cs) := onHost (.snapshot 0 { bg2.status with syncing := false } .synced) bg2
  check "continued: reaching tip in background completes successfully and stops networking"
    (bgDone.continuedSync.isNone && continuedSyncStatusText bgDone == "Last run finished" &&
     (match cs with
      | [.completeBackgroundTask id true (some 7), .stopNetworking] => id == idMain
      | _ => false))
  -- returning to foreground mid-sync rebinds syncGen to the new generation and finishes without stopping networking
  let (fg, _) := onHost (.scene true) bg2
  check "continued: returning to foreground rebinds syncGen to current generation"
    (fg.active && fg.continuedSync == some (.running idMain .mainnet fg.generation (some 7) true))
  let (fgDone, cs) := onHost (.snapshot fg.generation { fg.status with syncing := false } .synced) fg
  check "continued: finishing in foreground completes successfully and keeps networking running"
    (fgDone.continuedSync.isNone &&
     cs.any (· matches .completeBackgroundTask _ true (some 7)) &&
     !cs.any (· matches .stopNetworking))
  -- fast already-synced Sync now (settled := true) completes immediately
  let (mFast, _) := step .syncNow { readyMain with phase := .synced }
  let (mFast, _) := onHost (.bgtask idMain "continued" (some 9)) mFast
  let (mFastPre, cs) := onHost (.snapshot 0 { mFast.status with syncing := false } .synced false) mFast
  check "continued: pre-pass settled=false synced snapshot does not prematurely complete"
    (mFastPre.continuedSync.isSome && !cs.any (· matches .completeBackgroundTask ..))
  let (mFastEnd, cs) := onHost (.snapshot 0 { mFast.status with syncing := false } .synced true) mFastPre
  check "continued: settled=true synced snapshot completes immediately"
    (mFastEnd.continuedSync.isNone &&
     (match cs with | [.completeBackgroundTask id true (some 9)] => id == idMain | _ => false))
  -- peer discovery failure / backend throw while backgrounded completes false and stops networking
  let (bgFail, cs) := onHost (.snapshot 0 { bg2.status with syncing := false } .peerDiscoveryFailed) bg2
  check "continued: peerDiscoveryFailed in background completes false and stops networking"
    (bgFail.continuedSync.isNone &&
     (match cs with | [.completeBackgroundTask id false (some 7), .stopNetworking] => id == idMain | _ => false))
  let (bgThrow, cs) := onHost (.failed 0 (.wallet .sync) false "disk full") bg2
  check "continued: sync failure in background completes false and stops networking"
    (bgThrow.continuedSync.isNone &&
     (match cs with | [.completeBackgroundTask id false (some 7), .stopNetworking] => id == idMain | _ => false))
  -- expiry / user cancellation from Live Activity: stale tag ignored, matching tag completes false + stops networking
  let (bgStaleExp, cs) := onHost (.bgtaskExpired idMain "continued" (some 6)) bg2
  check "continued: expiry naming an older tag leaves running task alone"
    (bgStaleExp.continuedSync.isSome && cs.isEmpty)
  let (bgExp, cs) := onHost (.bgtaskExpired idMain "continued" (some 7)) bg2
  check "continued: expiry in background completes false and stops networking"
    (bgExp.continuedSync.isNone && continuedSyncStatusText bgExp == "Stopped or cancelled" &&
     bgExp.continuedSyncAutoSuppressed &&
     (match cs with | [.completeBackgroundTask id false (some 7), .stopNetworking] => id == idMain | _ => false))
  let (fgExp, cs) := onHost (.bgtaskExpired idMain "continued" (some 7)) fg
  check "continued: expiry in foreground completes false without stopping foreground networking"
    (fgExp.continuedSync.isNone &&
     (match cs with | [.completeBackgroundTask id false (some 7)] => id == idMain | _ => false))
  -- orphan continued launch (sync already gone) is completed immediately
  let (_, cs) := onHost (.bgtask idMain "continued" (some 11)) readyMain
  check "continued: orphan launch completes immediately with its tag"
    (match cs with | [.completeBackgroundTask id false (some 11)] => id == idMain | _ => false)
  -- refusal on iOS < 26 / Mac: clears requested state and stops networking if already backgrounded
  let (mReq, _) := step .syncNow readyMain
  let (bgReq, _) := onHost (.scene false) mReq
  let (bgRefused, cs) := onHost (.continuedSyncRefused idMain "notPermitted" "bad prefix") bgReq
  check "continued: refusal after backgrounding stops networking and shows reason"
    (bgRefused.continuedSync.isNone &&
     continuedSyncStatusText bgRefused == "Refused (notPermitted: bad prefix)" &&
     (cs matches [.stopNetworking]))
  -- switching network, switching wallet, or deleting wallet cancels a running continued task
  let (swNet, cs) := fg.switchNetwork .signet
  check "continued: switching network completes running task unsuccessfully"
    (swNet.continuedSync.isNone && cs.any (· matches .completeBackgroundTask _ false (some 7)))
  let (swWal, cs) := fg.switchWallet (fun g => .openSlot g .mainnet none)
  check "continued: switching wallet completes running task unsuccessfully"
    (swWal.continuedSync.isNone && cs.any (· matches .completeBackgroundTask _ false (some 7)))
  let (delWal, cs) := onHost (.deleted fg.generation) fg
  check "continued: deleting wallet completes running task unsuccessfully"
    (delWal.continuedSync.isNone && cs.any (· matches .completeBackgroundTask _ false (some 7)))
  -- shell capability wiring via Main.perform (ok + unavailable refusal + progress + complete)
  let sh ← Shell.new
  WinnowApp.perform (.continueBackgroundSync idMain "Syncing Bitcoin" "Starting sync…") sh.fx
  WinnowApp.perform (.progressBackgroundSync idMain (some 7) 10 20 "Syncing Bitcoin" "Scanning blocks… 10 / 20") sh.fx
  WinnowApp.perform (.completeBackgroundTask idMain true (some 7)) sh.fx
  discard <| waitUntil 2_000 (every := 5) do return (← sh.asks.get).size ≥ 3
  let asks ← sh.asks.get
  check "continued perform: sends bgtask.continue, bgtask.progress, and bgtask.complete"
    (asks.any (fun (n, a) => n == "bgtask.continue" && (a.getObjValAs? String "id").toOption == some idMain) &&
     asks.any (fun (n, a) => n == "bgtask.progress" && (a.getObjValAs? Nat "completed").toOption == some 10 &&
       (a.getObjValAs? Nat "tag").toOption == some 7) &&
     asks.any (fun (n, a) => n == "bgtask.complete" && (a.getObjValAs? Bool "success").toOption == some true &&
       (a.getObjValAs? Nat "tag").toOption == some 7)) (reprStr (asks.map fun (n, a) => (n, a.compress)))
  -- refusal from shell posts continuedSyncRefused with error and detail
  let refusedPosted ← IO.mkRef (#[] : Array Host)
  let refuseFx : LeanNative.Native.Effects Host :=
    { post := fun h => refusedPosted.modify (·.push h),
      cap := fun _ _ _ => pure (),
      ask := fun _ _ => pure (Task.pure (Lean.Json.mkObj [("ok", false), ("error", "notPermitted"), ("detail", "prefix mismatch")])) }
  WinnowApp.perform (.continueBackgroundSync idMain "Syncing Bitcoin" "Starting sync…") refuseFx
  let gotRefused ← waitUntil 2_000 (every := 5) do
    return (← refusedPosted.get).any fun h => match h with
      | .continuedSyncRefused id "notPermitted" "prefix mismatch" => id == idMain
      | _ => false
  check "continued perform: refused bgtask.continue posts continuedSyncRefused with error and detail" gotRefused

/-- `Pure.parseDouble` (Swift `Double(_:)`): decimal, scientific, hex floats, inf/nan/snan payloads,
overflow/underflow, and malformed forms. -/
def parseDoubleCases : IO Unit := do
  let isInf (o : Option Float) (neg : Bool) : Bool := match o with
    | some f => f.isInf && (if neg then f < 0 else f > 0) | none => false
  let isNaN (o : Option Float) : Bool := match o with | some f => f.isNaN | none => false
  check "parseDouble: decimal, signs, leading/trailing dot, zero"
    (parseDouble "12.5" == some 12.5 && parseDouble "+3.25" == some 3.25 && parseDouble "-0.5" == some (-0.5) &&
     parseDouble ".5" == some 0.5 && parseDouble "5." == some 5.0 &&
     parseDouble "0" == some 0.0 && parseDouble "-0.0" == some (-0.0))
  check "parseDouble: decimal scientific, overflow, underflow"
    (parseDouble "1.5e2" == some 150.0 && parseDouble "15E-1" == some 1.5 && parseDouble "2e+3" == some 2000.0 &&
     isInf (parseDouble "1e500") false && isInf (parseDouble "-1e500") true &&
     parseDouble "1e-500" == some 0.0)
  check "parseDouble: hex floats (lower/upper 0x/0X, p/P, fraction, zero, overflow, underflow)"
    (parseDouble "0x1.8p1" == some 3.0 && parseDouble "0X1.8P-1" == some 0.75 &&
     parseDouble "0x.8p4" == some 8.0 && parseDouble "-0x10p+2" == some (-64.0) &&
     parseDouble "0x10" == some 16.0 && parseDouble "0x0p0" == some 0.0 &&
     isInf (parseDouble "0x1p3000") false && parseDouble "0x1p-3000" == some 0.0)
  check "parseDouble: inf, infinity, nan, snan with decimal and hex payloads"
    (isInf (parseDouble "inf") false && isInf (parseDouble "-INF") true && isInf (parseDouble "+Infinity") false &&
     isNaN (parseDouble "nan") && isNaN (parseDouble "-sNaN") &&
     isNaN (parseDouble "nan(123)") && isNaN (parseDouble "sNaN(0x1f)"))
  check "parseDouble: malformed inputs return none"
    (parseDouble "" == none && parseDouble "." == none && parseDouble "1e" == none &&
     parseDouble "1e+a" == none && parseDouble "1q2" == none && parseDouble "0x" == none &&
     parseDouble "0x." == none && parseDouble "0x1p" == none && parseDouble "0x1q2" == none &&
     parseDouble "nan(bad)" == none && parseDouble "abc" == none)
  check "parseRateMilli: trims, clamps non-positive/NaN to 0"
    (parseRateMilli " 2.5 " == some 2500 && parseRateMilli "\n1.25\n" (trimNewlines := true) == some 1250 &&
     parseRateMilli "nan" == some 0 && parseRateMilli "-3" == some 0 && parseRateMilli "bad" == none)

/-- `Real.AppError.text` and `RecordsReal.StoreKeyVault.ofKeyStore` edge and failure paths. -/
def appErrorsAndVault : IO Unit := do
  let errs : List Real.AppError :=
    [.noWallet, .walletReplaced, .walletAlreadyHere, .walletAlreadyHeld, .paymentDetailsUnavailable,
     .feeDecisionRequired 1.5 5.0, .noStack, .noPeers, .mnemonicUnavailable, .invalidPeer "bad:port",
     .wrongNetwork "mainnet", .sendReviewChanged, .storageDamaged "corrupt", .spendAlreadyInFlight, .noStorage]
  check "AppError.text: every variant produces non-empty message" (errs.all fun e => !e.text.isEmpty)
  -- StoreKeyVault.ofKeyStore against custom KeyStore responses
  let goodHex := Winnow.hex (ByteArray.mk (Array.replicate 32 0xAB))
  let liftE {α} (r : Except Keys.KeyStoreError α) : ExceptT Keys.KeyStoreError IO α := ExceptT.mk (pure r)
  let makeKs (loadR : Except Keys.KeyStoreError Keys.WalletSecret)
      (storeR : Except Keys.KeyStoreError Unit := .ok ())
      (delR : Except Keys.KeyStoreError Unit := .ok ())
      (loadBytesR : Except Keys.KeyStoreError (Option ByteArray) := .ok none)
      (storeBytesR : Except Keys.KeyStoreError Unit := .ok ()) : Keys.KeyStore IO :=
    { store := fun _ _ => liftE storeR, load := fun _ => liftE loadR, delete := fun _ => liftE delR,
      loadBytes := fun _ => liftE loadBytesR, storeBytes := fun _ _ => liftE storeBytesR }
  let v1 := RecordsReal.StoreKeyVault.ofKeyStore (makeKs (.ok (.masterKey goodHex)))
  check "vault: valid 32-byte masterKey hex loads" ((← (v1.key "a").run) matches .ok (some _))
  let vBadLen := RecordsReal.StoreKeyVault.ofKeyStore (makeKs (.ok (.masterKey "0011")))
  check "vault: wrong-length key is malformedKey" ((← (vBadLen.key "a").run) matches .error (.keyVault .malformedKey))
  let vBadHex := RecordsReal.StoreKeyVault.ofKeyStore (makeKs (.ok (.masterKey "zzzz")))
  check "vault: non-hex key is malformedKey" ((← (vBadHex.key "a").run) matches .error (.keyVault .malformedKey))
  let vWrongKind := RecordsReal.StoreKeyVault.ofKeyStore (makeKs (.ok (.mnemonic "words")))
  check "vault: mnemonic secret is malformedKey" ((← (vWrongKind.key "a").run) matches .error (.keyVault .malformedKey))
  let vErr := RecordsReal.StoreKeyVault.ofKeyStore (makeKs (.error .malformedSecret))
  check "vault: other keystore error is malformedKey" ((← (vErr.key "a").run) matches .error (.keyVault .malformedKey))
  let vLocked := RecordsReal.StoreKeyVault.ofKeyStore (makeKs (.error (.keychain RecordsReal.interactionNotAllowed)))
  let beforeRefused ← RecordsReal.refusedStoreKeys.get
  check "vault: interactionNotAllowed records refused account"
    ((← (vLocked.key "locked.test").run) matches .error (.keyVault (.keychain _)) &&
     (← RecordsReal.refusedStoreKeys.get).contains "locked.test")
  RecordsReal.refusedStoreKeys.set beforeRefused
  -- moving recovery path: main notFound, moving present -> restored & deleted
  let deleted ← IO.mkRef (#[] : Array String)
  let movingKs : Keys.KeyStore IO :=
    { load := fun id => liftE (if id.endsWith ".moving" then .ok (.masterKey goodHex) else .error (.notFound id)),
      store := fun _ _ => liftE (.ok ()),
      delete := fun id => ExceptT.mk do deleted.modify (·.push id); pure (.ok ()),
      loadBytes := fun _ => liftE (.ok (some (ByteArray.mk #[1, 2]))),
      storeBytes := fun _ _ => liftE (.error (.alreadyExists "x")) }
  let vm := RecordsReal.StoreKeyVault.ofKeyStore movingKs
  check "vault: recovers key from .moving copy and cleans it up"
    ((← (vm.key "m").run) matches .ok (some _) && (← deleted.get).any (·.endsWith ".moving"))
  check "vault: rawKey & keepRaw handle ok and alreadyExists"
    ((← (vm.rawKey "m").run) matches .ok (some _) && (← (vm.keepRaw "m" .empty).run) matches .ok ())
  -- establishKey / discardKey / rawKey / keepRaw error mappings
  let vAlready := RecordsReal.StoreKeyVault.ofKeyStore (makeKs (.error (.notFound "")) (storeR := .error (.alreadyExists "a"))
    (delR := .error (.notFound "")) (loadBytesR := .error (.keychain (-50))) (storeBytesR := .error (.keychain (-50))))
  check "vault: establishKey alreadyExists, discardKey notFound, rawKey/keepRaw keychain error"
    ((← (vAlready.establishKey "a").run) matches .error (.keyVault (.alreadyEstablished "a")) &&
     (← (vAlready.discardKey "a").run) matches .ok () &&
     (← (vAlready.rawKey "a").run) matches .error (.keyVault (.keychain (-50))) &&
     (← (vAlready.keepRaw "a" .empty).run) matches .error (.keyVault (.keychain (-50))))
  let vKc := RecordsReal.StoreKeyVault.ofKeyStore (makeKs (.error (.notFound "")) (storeR := .error (.keychain (-1)))
    (delR := .error (.keychain (-2))) (loadBytesR := .error .malformedSecret) (storeBytesR := .error .malformedSecret))
  check "vault: establishKey/discardKey keychain and rawKey/keepRaw malformedKey"
    ((← (vKc.establishKey "a").run) matches .error (.keyVault (.keychain (-1))) &&
     (← (vKc.discardKey "a").run) matches .error (.keyVault (.keychain (-2))) &&
     (← (vKc.rawKey "a").run) matches .error (.keyVault .malformedKey) &&
     (← (vKc.keepRaw "a" .empty).run) matches .error (.keyVault .malformedKey))
  let vMal := RecordsReal.StoreKeyVault.ofKeyStore (makeKs (.error (.notFound "")) (storeR := .error .malformedSecret)
    (delR := .error .malformedSecret))
  check "vault: establishKey/discardKey other error -> malformedKey"
    ((← (vMal.establishKey "a").run) matches .error (.keyVault .malformedKey) &&
     (← (vMal.discardKey "a").run) matches .error (.keyVault .malformedKey))

/-- Exhaustive pure unit tests for every message arm and guard of `WinnowApp.stepPeople`. -/
def stepPeopleCases : IO Unit := do
  let alice : Person := { id := "p1", name := "Alice", payTo := some true, savedRecipient := some true }
  let dave : Person := { id := "p2", name := "Dave", payTo := none, savedRecipient := none }
  let base : Model :=
    { stage := .ready, active := true, generation := 7,
      settings := { network := .signet, ownDisplayName := "  Owner  " },
      records := { people := [alice, dave] } }
  let tx := String.ofList (List.replicate 64 'a')
  let addr := "tb1qexampleaddress"
  let parsedPay : PastePreview := { name := some "ParsedName", payTo := some false }
  let parsedNoPay : PastePreview := { name := some "CardOnly", payTo := none }

  -- .openAdd (empty address vs pre-filled address, new vs existing person)
  let (mOpenEmpty, csOpenEmpty) := stepPeople (.openAdd {} "") base
  check "stepPeople.openAdd: empty address opens sheet with no parsePaste"
    (mOpenEmpty.topSheet == some .addPerson && mOpenEmpty.person.name == "" && csOpenEmpty.isEmpty)
  let (mOpenAddr, csOpenAddr) := stepPeople (.openAdd { personID := some "p1" } addr) base
  check "stepPeople.openAdd: pre-filled address fills existing name and emits parsePaste"
    (mOpenAddr.topSheet == some .addPerson && mOpenAddr.person.name == "Alice" && mOpenAddr.person.pasted == addr &&
     (csOpenAddr matches [.parsePaste 7 _]))

  -- .setName, .setPasted (empty/whitespace vs non-empty), .paste
  let (mName, csName) := stepPeople (.setName "Bob") mOpenEmpty
  check "stepPeople.setName: updates name with no commands" (mName.person.name == "Bob" && csName.isEmpty)
  let mWithParsed := { mName with person := { mName.person with parsed := some parsedPay, error := some "old" } }
  let (mBlank, csBlank) := stepPeople (.setPasted "   ") mWithParsed
  check "stepPeople.setPasted: whitespace clears parsed/error with no parsePaste"
    (mBlank.person.pasted == "   " && mBlank.person.parsed.isNone && mBlank.person.error.isNone && csBlank.isEmpty)
  let (mPasted, csPasted) := stepPeople (.setPasted addr) mWithParsed
  check "stepPeople.setPasted: non-empty resets parsed/error and emits parsePaste"
    (mPasted.person.pasted == addr && mPasted.person.parsed.isNone && mPasted.person.error.isNone &&
     (csPasted matches [.parsePaste 7 _]))
  let (_, csPaste) := stepPeople .paste base
  check "stepPeople.paste: requests person clipboard paste" (csPaste matches [.paste .person])

  -- .chooseSaved (with and without txid)
  let (mSavedNoTx, csSavedNoTx) := stepPeople (.chooseSaved "p1") base
  check "stepPeople.chooseSaved: without txid is a no-op" (!mSavedNoTx.person.saving && csSavedNoTx.isEmpty)
  let mLabelMode := { base with person := { mode := { txid := some tx } } }
  let (mSavedTx, csSavedTx) := stepPeople (.chooseSaved "p1") mLabelMode
  check "stepPeople.chooseSaved: with txid marks saving and emits labelSender"
    (mSavedTx.person.saving &&
     (match csSavedTx with | [.labelSender 7 t "p1"] => t == tx | _ => false))

  -- .chooseFunding
  let (mFund, csFund) := stepPeople (.chooseFunding addr .localFunding) mLabelMode
  check "stepPeople.chooseFunding: sets pasted, records selectedFunding, and emits parsePaste"
    (mFund.person.pasted == addr && mFund.person.selectedFunding == some (addr, .localFunding) &&
     (csFund matches [.parsePaste 7 _]))

  -- .askInfer and .infer (missing consent, missing txid, stale gen, changed esplora, !active, valid)
  let (mAsked, csAsked) := stepPeople .askInfer mLabelMode
  check "stepPeople.askInfer: records consent tuple and opens inferSender confirm"
    (mAsked.person.lookupConsent == some (base.settings.esploraBaseURL, 7) &&
     mAsked.confirm == some .inferSender && csAsked.isEmpty)
  let (mNoConsent, csNoConsent) := stepPeople .infer { mLabelMode with confirm := some .inferSender }
  check "stepPeople.infer: missing consent clears confirm and does nothing"
    (mNoConsent.confirm.isNone && !mNoConsent.person.inferring && csNoConsent.isEmpty)
  let (mNoTx, csNoTx) := stepPeople .infer { mAsked with person := { mAsked.person with mode := {} } }
  check "stepPeople.infer: missing txid clears confirm and does nothing"
    (mNoTx.confirm.isNone && !mNoTx.person.inferring && csNoTx.isEmpty)
  let (mStaleGen, csStaleGen) := stepPeople .infer { mAsked with generation := 8 }
  check "stepPeople.infer: stale generation sets connection-changed error"
    (mStaleGen.confirm.isNone && !mStaleGen.person.inferring && mStaleGen.person.error.isSome && csStaleGen.isEmpty)
  let changedSettings : Settings := { base.settings with signet := { explorer := .custom, esploraURL := "https://other.example" } }
  let (mChangedUrl, csChangedUrl) := stepPeople .infer { mAsked with settings := changedSettings }
  check "stepPeople.infer: changed esploraBaseURL sets connection-changed error"
    (mChangedUrl.confirm.isNone && !mChangedUrl.person.inferring && mChangedUrl.person.error.isSome && csChangedUrl.isEmpty)
  let (mInactive, csInactive) := stepPeople .infer { mAsked with active := false }
  check "stepPeople.infer: inactive scene sets connection-changed error"
    (mInactive.confirm.isNone && !mInactive.person.inferring && mInactive.person.error.isSome && csInactive.isEmpty)
  let (mInferOk, csInferOk) := stepPeople .infer mAsked
  check "stepPeople.infer: valid consent starts inferring and emits lookupSender"
    (mInferOk.confirm.isNone && mInferOk.person.inferring && mInferOk.person.error.isNone &&
     (match csInferOk with | [.lookupSender 7 t u] => t == tx && u == base.settings.esploraBaseURL | _ => false))

  -- .save: !canSave guards (saving, empty effectiveName, unparsed paste, regular add without payTo)
  let cannotSaving := { base with person := { name := "Bob", saving := true, parsed := some parsedPay } }
  let cannotEmptyName := { base with person := { name := "  ", parsed := some { payTo := some false } } }
  let cannotUnparsed := { base with person := { name := "Bob", pasted := addr, parsed := none } }
  let cannotNoPay := { base with person := { name := "Bob", pasted := "", parsed := none } }
  check "stepPeople.save: refuses when !canSave (saving, blank name, unparsed paste, regular non-payable)"
    ((stepPeople .save cannotSaving).2.isEmpty &&
     (stepPeople .save cannotEmptyName).2.isEmpty &&
     (stepPeople .save cannotUnparsed).2.isEmpty &&
     (stepPeople .save cannotNoPay).2.isEmpty)

  -- .save: edit existing person (without payTo + payable -> attach with supplied/localFunding/explorerFunding/mismatch;
  --        without payTo + non-payable -> no attach; with payTo + payable -> no attach)
  let editDaveSupplied := { base with person := { mode := { personID := some "p2" }, name := "David", pasted := addr, parsed := some parsedPay } }
  let (mEditSup, csEditSup) := stepPeople .save editDaveSupplied
  check "stepPeople.save: edit existing without payTo attaches supplied destination"
    (mEditSup.person.saving &&
     (match csEditSup with | [.editPerson 7 "p2" "David" (some (a, .supplied, none))] => a == addr | _ => false))
  let editDaveLocal := { base with person := { mode := { personID := some "p2", txid := some tx }, name := "David", pasted := addr,
                                               parsed := some parsedPay, selectedFunding := some (addr, .localFunding) } }
  let (_, csEditLoc) := stepPeople .save editDaveLocal
  check "stepPeople.save: edit existing attaches localFunding with txid source"
    (match csEditLoc with | [.editPerson 7 "p2" "David" (some (a, .localFunding, some s))] => a == addr && s == tx | _ => false)
  let editDaveExp := { base with person := { mode := { personID := some "p2", txid := some tx }, name := "David", pasted := addr,
                                             parsed := some parsedPay, selectedFunding := some (addr, .explorerFunding),
                                             inferredSource := some "mempool.space" } }
  let (_, csEditExp) := stepPeople .save editDaveExp
  check "stepPeople.save: edit existing attaches explorerFunding with inferredSource"
    (match csEditExp with | [.editPerson 7 "p2" "David" (some (a, .explorerFunding, some "mempool.space"))] => a == addr | _ => false)
  let editDaveEdited := { editDaveLocal with person := { editDaveLocal.person with selectedFunding := some ("other", .localFunding) } }
  let (_, csEditOther) := stepPeople .save editDaveEdited
  check "stepPeople.save: editing pasted text away from selectedFunding reverts provenance to supplied"
    (match csEditOther with | [.editPerson 7 "p2" "David" (some (a, .supplied, none))] => a == addr | _ => false)
  let editDaveNoPay := { base with person := { mode := { personID := some "p2" }, name := "David", pasted := "", parsed := none } }
  let (_, csEditNoPay) := stepPeople .save editDaveNoPay
  check "stepPeople.save: edit existing without payTo and no destination passes attach=none"
    (match csEditNoPay with | [.editPerson 7 "p2" "David" none] => true | _ => false)
  let editAlice := { base with person := { mode := { personID := some "p1" }, name := "Alicia", pasted := addr, parsed := some parsedPay } }
  let (_, csEditAlice) := stepPeople .save editAlice
  check "stepPeople.save: edit existing who already has payTo passes attach=none"
    (match csEditAlice with | [.editPerson 7 "p1" "Alicia" none] => true | _ => false)

  -- .save: add new person in labelingSender mode (payable vs non-payable with paste vs empty paste)
  let addSenderPay := { base with person := { mode := { txid := some tx }, name := "Sender", pasted := addr,
                                              parsed := some parsedPay, selectedFunding := some (addr, .localFunding) } }
  let (_, csSenderPay) := stepPeople .save addSenderPay
  check "stepPeople.save: labelingSender payable forwards paste, provenance, source, and txid"
    (match csSenderPay with
     | [.addPerson 7 "Sender" (some a) (some .localFunding) (some s) (some t)] => a == addr && s == tx && t == tx
     | _ => false)
  let addSenderNonPay := { base with person := { mode := { txid := some tx }, name := "", pasted := "card", parsed := some parsedNoPay } }
  let (_, csSenderNonPay) := stepPeople .save addSenderNonPay
  check "stepPeople.save: labelingSender non-payable drops paste and falls back to parsed name"
    (match csSenderNonPay with
     | [.addPerson 7 "CardOnly" none none none (some t)] => t == tx
     | _ => false)
  let addSenderEmpty := { base with person := { mode := { txid := some tx }, name := "NameOnly", pasted := "  ", parsed := none } }
  let (_, csSenderEmpty) := stepPeople .save addSenderEmpty
  check "stepPeople.save: labelingSender empty paste saves name-only with txid"
    (match csSenderEmpty with
     | [.addPerson 7 "NameOnly" none none none (some t)] => t == tx
     | _ => false)

  -- .save: add new regular person (non-empty paste vs whitespace-only paste with parsed payTo)
  let addReg := { base with person := { name := "Carol", pasted := addr, parsed := some parsedPay } }
  let (_, csReg) := stepPeople .save addReg
  check "stepPeople.save: regular add with non-empty paste emits addPerson"
    (match csReg with | [.addPerson 7 "Carol" (some a) none none none] => a == addr | _ => false)
  let addRegBlank := { base with person := { name := "Carol", pasted := "  ", parsed := some parsedPay } }
  let (_, csRegBlank) := stepPeople .save addRegBlank
  check "stepPeople.save: regular add with blank paste sends paste=none"
    (match csRegBlank with | [.addPerson 7 "Carol" none none none none] => true | _ => false)

  -- .choose (missing, no payTo, with payTo)
  let (mChooseMiss, csChooseMiss) := stepPeople (.choose "missing") base
  check "stepPeople.choose: missing person is a no-op" (mChooseMiss.sheets.isEmpty && csChooseMiss.isEmpty)
  let (mChooseNoPay, csChooseNoPay) := stepPeople (.choose "p2") base
  check "stepPeople.choose: person without payTo opens addPerson to attach destination"
    (mChooseNoPay.topSheet == some .addPerson && mChooseNoPay.person.mode == { personID := some "p2" } &&
     mChooseNoPay.person.name == "Dave" && csChooseNoPay.isEmpty)
  let mWithSheet := { base with sheets := [.send, .savedRecipients],
                                send := { inputs := { destination := "old" }, error := some "err" } }
  let (mChoosePay, csChoosePay) := stepPeople (.choose "p1") mWithSheet
  check "stepPeople.choose: person with payTo closes savedRecipients and selects recipient on Send"
    (mChoosePay.sheets == [.send] && mChoosePay.send.inputs.personID == some "p1" &&
     mChoosePay.send.inputs.destination == "" && mChoosePay.send.preview.isNone &&
     mChoosePay.send.error.isNone && csChoosePay.isEmpty)

  -- .rename
  let (mRen, csRen) := stepPeople (.rename "p1") base
  check "stepPeople.rename: opens addPerson for that person"
    (mRen.topSheet == some .addPerson && mRen.person.mode == { personID := some "p1" } &&
     mRen.person.name == "Alice" && csRen.isEmpty)

  -- .card (missing vs present)
  let (mCardMiss, csCardMiss) := stepPeople (.card "missing") base
  check "stepPeople.card: missing person is a no-op" (mCardMiss.sheets.isEmpty && csCardMiss.isEmpty)
  let (mCardOk, csCardOk) := stepPeople (.card "p1") base
  check "stepPeople.card: present person opens shareCard and emits trimmed ownDisplayName"
    (mCardOk.topSheet == some .shareCard && mCardOk.shareCard.forName == "Alice" &&
     mCardOk.shareCard.forPerson == some "p1" && mCardOk.shareCard.making &&
     (match csCardOk with | [.personCard 7 (some "p1") "Alice" "Owner"] => true | _ => false))

  -- .remove
  let (mRem, csRem) := stepPeople (.remove "p1") { base with recipientsError := some "stale" }
  check "stepPeople.remove: clears recipientsError and emits updateRecipient"
    (mRem.recipientsError.isNone && (csRem matches [.updateRecipient 7 "p1" none false false]))

/-- Exhaustive pure unit tests for every arm and guard of `stepMultisigAccount` and `stepMultisigCollect`. -/
def stepMultisigAccountAndCollectCases : IO Unit := do
  let screenOf (prog : MultisigProgress) (held : List HeldKey := []) : MultisigScreen :=
    { outputs := [], inputTotal := 50_000, fee := 500, signatures := [(false, 1, 2)], progress := prog, heldKeys := held }
  let draftOfScreen (s : Option MultisigScreen) : MultisigDraftInfo :=
    { psbt := "cHNidP8=", txid := "tx1", screen := s }
  let acctWith (id : String) (builds : Bool := true) (nextRecv : Nat := 3) (draft : Option MultisigDraftInfo := none) : MultisigInfo :=
    { id, name := s!"Acct {id}", descriptor := "tr(x)", balance := 100_000,
      buildsPayments := builds, nextReceiveIndex := nextRecv, draft }
  let acctMain := acctWith "a1" (builds := true) (nextRecv := 4)
    (draft := some (draftOfScreen (some (screenOf { phoneHolds := true, phoneUnsigned := true, ledgerHolds := true, ledgerUnsigned := true }
      [{ walletID := "w2", unsigned := true, slot := "1", name := "Second" },
       { walletID := "w3", unsigned := false, slot := "2", name := "Signed" }]))))
  let acctComplete := acctWith "aDone" (builds := true) (nextRecv := 1)
    (draft := some (draftOfScreen (some (screenOf { complete := true, phoneHolds := true, phoneUnsigned := true, ledgerUnsigned := true }
      [{ walletID := "w2", unsigned := true, slot := "1", name := "Second" }]))))
  let acctSigned := acctWith "aSigned" (builds := true) (nextRecv := 1)
    (draft := some (draftOfScreen (some (screenOf { complete := false, phoneHolds := true, phoneUnsigned := false, ledgerHolds := true, ledgerUnsigned := false }))))
  let acctWatch := acctWith "aWatch" (builds := false) (nextRecv := 0) (draft := none)
  let base : Model :=
    { stage := .ready, active := true, generation := 5,
      settings := { network := .signet },
      status := { feeFloorMilli := some 1200 },
      multisig := { accounts := [acctMain, acctComplete, acctSigned, acctWatch], notice := some "damaged" } }
  let onAcct : Model := { base with routes := [.multisigAccount "a1"], multisigAccountError := some "old" }

  -- stepMultisigAccount: .newAddress (on account route vs other route)
  let (mAddrOk, csAddrOk) := stepMultisig .newAddress onAcct
  check "stepMultisigAccount.newAddress: clears error and emits newMultisigAddress on account route"
    (mAddrOk.multisigAccountError.isNone && (csAddrOk matches [.newMultisigAddress 5 "a1"]))
  check "stepMultisigAccount.newAddress: no-op off account route"
    ((stepMultisig .newAddress base).2.isEmpty)

  -- .askRemove and .remove
  let (mAskRem, csAskRem) := stepMultisig .askRemove onAcct
  check "stepMultisigAccount.askRemove: sets removeMultisig confirm on account route"
    (mAskRem.confirm == some (.removeMultisig "a1") && csAskRem.isEmpty)
  check "stepMultisigAccount.askRemove: no-op off account route"
    ((stepMultisig .askRemove base).1.confirm.isNone)
  let (mRemOk, csRemOk) := stepMultisig .remove mAskRem
  check "stepMultisigAccount.remove: clears confirm/error and emits removeMultisigAccount"
    (mRemOk.confirm.isNone && mRemOk.multisigAccountError.isNone && (csRemOk matches [.removeMultisigAccount 5 "a1"]))
  check "stepMultisigAccount.remove: no-op without matching confirm"
    ((stepMultisig .remove { onAcct with confirm := some .setAsideMultisig }).2.isEmpty)

  -- .askSetAside and .setAside
  let (mAskSA, csAskSA) := stepMultisig .askSetAside base
  check "stepMultisigAccount.askSetAside: sets confirm when notice is present"
    (mAskSA.confirm == some .setAsideMultisig && csAskSA.isEmpty)
  check "stepMultisigAccount.askSetAside: no-op when notice is none"
    ((stepMultisig .askSetAside { base with multisig := { base.multisig with notice := none } }).1.confirm.isNone)
  let (mSAOk, csSAOk) := stepMultisig .setAside mAskSA
  check "stepMultisigAccount.setAside: clears confirm and emits setAsideMultisig"
    (mSAOk.confirm.isNone && (csSAOk matches [.setAsideMultisig 5]))
  check "stepMultisigAccount.setAside: no-op without matching confirm"
    ((stepMultisig .setAside base).2.isEmpty)

  -- .sendFrom (buildsPayments=false, fresh sheet, already-open sheet, sending in progress)
  let (mSendWatch, csSendWatch) := stepMultisig (.sendFrom "aWatch") base
  check "stepMultisigAccount.sendFrom: refused for watch-only / non-building account"
    (mSendWatch.sheets.isEmpty && csSendWatch.isEmpty)
  let (mSendFresh, csSendFresh) := stepMultisig (.sendFrom "a1") base
  check "stepMultisigAccount.sendFrom: opens Send sheet with accountID and resolves fee rate"
    (mSendFresh.sheets == [.send] && mSendFresh.send.inputs == { network := .signet, accountID := some "a1" } &&
     (match csSendFresh with | [.resolveRate 5 inp (some 1200)] => inp.accountID == some "a1" | _ => false))
  let (mSendOpen, csSendOpen) := stepMultisig (.sendFrom "a1") { base with sheets := [.send] }
  check "stepMultisigAccount.sendFrom: reuses open Send sheet without duplicating"
    (mSendOpen.sheets == [.send] && csSendOpen.length == 1)
  let mSending := { base with send := { sending := true, inputs := { destination := "keep" } } }
  let (mSendBusy, csSendBusy) := stepMultisig (.sendFrom "a1") mSending
  check "stepMultisigAccount.sendFrom: while sending, presents sheet without clobbering SendState"
    (mSendBusy.sheets == [.send] && mSendBusy.send.sending && mSendBusy.send.inputs.destination == "keep" && csSendBusy.isEmpty)

  -- .pasteForAccount (busy vs idle)
  let mBusyCollect := { base with collect := { busy := true, error := some "e" } }
  check "stepMultisigAccount.pasteForAccount: no-op when collect is busy"
    ((stepMultisig (.pasteForAccount "a1") mBusyCollect).2.isEmpty)
  let (mPasteAcc, csPasteAcc) := stepMultisig (.pasteForAccount "a1") { base with collect := { error := some "old" } }
  check "stepMultisigAccount.pasteForAccount: clears collect error and pastes accountPSBT"
    (mPasteAcc.collect.error.isNone && (csPasteAcc matches [.paste (.accountPSBT "a1")]))

  -- .verifyAddress (off route, missing account, already checking, ok)
  check "stepMultisigAccount.verifyAddress: no-op off account route"
    ((stepMultisig .verifyAddress base).2.isEmpty)
  check "stepMultisigAccount.verifyAddress: no-op when account id is missing from overview"
    ((stepMultisig .verifyAddress { base with routes := [.multisigAccount "missing"] }).2.isEmpty)
  check "stepMultisigAccount.verifyAddress: no-op when already checking"
    ((stepMultisig .verifyAddress { onAcct with ledgerVerify := { checking := true } }).2.isEmpty)
  let (mVerOk, csVerOk) := stepMultisig .verifyAddress onAcct
  check "stepMultisigAccount.verifyAddress: starts checking at nextReceiveIndex and emits verifyLedgerAddress"
    (mVerOk.ledgerVerify.id == "a1" && mVerOk.ledgerVerify.index == 4 && mVerOk.ledgerVerify.checking &&
     (csVerOk matches [.verifyLedgerAddress 5 "a1" 4]))

  -- .rebroadcast, .askAbandon, .abandon, and fallback arm
  let (mReb, csReb) := stepMultisig (.rebroadcast "a1" "tx99") { base with payment := { error := some "err" } }
  check "stepMultisigAccount.rebroadcast: clears payment error and emits rebroadcastSpend"
    (mReb.payment.error.isNone && (csReb matches [.rebroadcastSpend 5 "a1" "tx99"]))
  let (mAskAb, csAskAb) := stepMultisig (.askAbandon "a1" "tx99") base
  check "stepMultisigAccount.askAbandon: sets abandonSpend confirm"
    (mAskAb.confirm == some (.abandonSpend "a1" "tx99") && csAskAb.isEmpty)
  let (mAbOk, csAbOk) := stepMultisig .abandon mAskAb
  check "stepMultisigAccount.abandon: clears confirm and emits abandonSpend"
    (mAbOk.confirm.isNone && (csAbOk matches [.abandonSpend 5 "a1" "tx99"]))
  check "stepMultisigAccount.abandon: no-op without matching confirm"
    ((stepMultisig .abandon base).2.isEmpty)
  check "stepMultisigAccount: non-account message hits fallback no-op"
    ((stepMultisigAccount .openAdd base).2.isEmpty)

  -- stepMultisigCollect: .setPasted, .pastePSBT, .addPasted
  let (mSetP, csSetP) := stepMultisig (.setPasted "psbt-data") base
  check "stepMultisigCollect.setPasted: sets pasted text" (mSetP.collect.pasted == "psbt-data" && csSetP.isEmpty)
  check "stepMultisigCollect.pastePSBT: emits paste multisigPSBT"
    ((stepMultisig .pastePSBT base).2 matches [.paste .multisigPSBT])
  check "stepMultisigCollect.addPasted: no-op when busy or blank"
    ((stepMultisig (.addPasted "a1") { mSetP with collect := { mSetP.collect with busy := true } }).2.isEmpty &&
     (stepMultisig (.addPasted "a1") { base with collect := { pasted := "   " } }).2.isEmpty)
  let (mAddP, csAddP) := stepMultisig (.addPasted "a1") { mSetP with collect := { mSetP.collect with epoch := 3, error := some "old" } }
  check "stepMultisigCollect.addPasted: bumps epoch, marks busy, clears error, emits adoptDraft"
    (mAddP.collect.epoch == 4 && mAddP.collect.busy && mAddP.collect.error.isNone &&
     (csAddP matches [.adoptDraft 5 4 "a1" "psbt-data"]))

  -- .sign (busy, missing/no-draft, already signed, already complete, ok)
  check "stepMultisigCollect.sign: guarded by busy, missing draft, already signed, and complete"
    ((stepMultisig (.sign "a1") mBusyCollect).2.isEmpty &&
     (stepMultisig (.sign "aWatch") base).2.isEmpty &&
     (stepMultisig (.sign "aSigned") base).2.isEmpty &&
     (stepMultisig (.sign "aDone") base).2.isEmpty)
  let (mSignOk, csSignOk) := stepMultisig (.sign "a1") base
  check "stepMultisigCollect.sign: runs collect and emits signDraft when phoneUnsigned && !complete"
    (mSignOk.collect.busy && mSignOk.collect.epoch == 1 && !mSignOk.collect.ledgerSigning &&
     (csSignOk matches [.signDraft 5 1 "a1"]))

  -- .switchToSign (busy, complete, wrong slot, signed slot, ok)
  check "stepMultisigCollect.switchToSign: guarded by busy, complete, wrong slot, and already-signed slot"
    ((stepMultisig (.switchToSign "a1" "1") mBusyCollect).2.isEmpty &&
     (stepMultisig (.switchToSign "aDone" "1") base).2.isEmpty &&
     (stepMultisig (.switchToSign "a1" "9") base).2.isEmpty &&
     (stepMultisig (.switchToSign "a1" "2") base).2.isEmpty)
  let (mSwitchOk, csSwitchOk) := stepMultisig (.switchToSign "a1" "1") base
  check "stepMultisigCollect.switchToSign: emits handOverDraft for unsigned held slot"
    (mSwitchOk.collect.busy && (csSwitchOk matches [.handOverDraft 5 1 "a1" "1"]))

  -- .signWithLedger (busy, complete, already signed, missing draft, ok)
  check "stepMultisigCollect.signWithLedger: guarded by busy, complete, already signed, and missing draft"
    ((stepMultisig (.signWithLedger "a1") mBusyCollect).2.isEmpty &&
     (stepMultisig (.signWithLedger "aDone") base).2.isEmpty &&
     (stepMultisig (.signWithLedger "aSigned") base).2.isEmpty &&
     (stepMultisig (.signWithLedger "aWatch") base).2.isEmpty)
  let (mLedOk, csLedOk) := stepMultisig (.signWithLedger "a1") base
  check "stepMultisigCollect.signWithLedger: sets ledgerSigning and emits signDraftWithLedger"
    (mLedOk.collect.busy && mLedOk.collect.ledgerSigning && (csLedOk matches [.signDraftWithLedger 5 1 "a1"]))

  -- .broadcast (busy, incomplete, spendingInFlight, ok)
  check "stepMultisigCollect.broadcast: guarded by busy and incomplete progress"
    ((stepMultisig (.broadcast "aDone") mBusyCollect).2.isEmpty &&
     (stepMultisig (.broadcast "a1") base).2.isEmpty)
  let (mBcastFlight, csBcastFlight) := stepMultisig (.broadcast "aDone") { base with spendingInFlight := true }
  check "stepMultisigCollect.broadcast: sets error when spendingInFlight is true"
    (mBcastFlight.collect.error == some "Another payment is already being signed and broadcast. Wait for it to finish." &&
     !mBcastFlight.collect.busy && csBcastFlight.isEmpty)
  let (mBcastOk, csBcastOk) := stepMultisig (.broadcast "aDone") base
  check "stepMultisigCollect.broadcast: sets spendingInFlight and emits broadcastDraft when complete"
    (mBcastOk.collect.busy && mBcastOk.spendingInFlight && (csBcastOk matches [.broadcastDraft 5 1 "aDone"]))

  -- .askDiscard, .discard, and fallback arm
  let (mAskDisc, csAskDisc) := stepMultisig (.askDiscard "a1") base
  check "stepMultisigCollect.askDiscard: sets discardDraft confirm"
    (mAskDisc.confirm == some (.discardDraft "a1") && csAskDisc.isEmpty)
  let (mDiscOk, csDiscOk) := stepMultisig .discard mAskDisc
  check "stepMultisigCollect.discard: clears confirm, runs collect, emits discardDraft"
    (mDiscOk.confirm.isNone && mDiscOk.collect.busy && (csDiscOk matches [.discardDraft 5 1 "a1"]))
  check "stepMultisigCollect.discard: no-op without matching confirm"
    ((stepMultisig .discard base).2.isEmpty)
  check "stepMultisigCollect: non-collect message hits fallback no-op"
    ((stepMultisigCollect .openAdd base).2.isEmpty)

/-- Targeted pure unit tests for `WinnowApp.E2E.looksSecret` covering valid/invalid BIP39 windows,
Unicode whitespace separators, the 512-word cutoff, all extended private key prefixes, and clean text. -/
def looksSecretCases : IO Unit := do
  let m12 := match Winnow.Keys.BIP39.mnemonic (ByteArray.mk (Array.replicate 16 0x00)) with
    | .ok s => s
    | .error _ => ""
  let m24 := match Winnow.Keys.BIP39.mnemonic (ByteArray.mk (Array.replicate 32 0x00)) with
    | .ok s => s
    | .error _ => ""
  let nbsp := String.singleton (Char.ofNat 0x00A0)
  let ideo := String.singleton (Char.ofNat 0x3000)
  check "looksSecret: valid 12-word and 24-word mnemonics are detected"
    (!m12.isEmpty && !m24.isEmpty &&
     WinnowApp.E2E.looksSecret m12 && WinnowApp.E2E.looksSecret m24)
  check "looksSecret: valid 12-word and 24-word mnemonics embedded in prose are detected"
    (WinnowApp.E2E.looksSecret s!"notes before {m12} and after" &&
     WinnowApp.E2E.looksSecret s!"prefix words {m24} suffix")
  let m12Unicode := nbsp.intercalate (m12.splitOn " ")
  let m24Unicode := ideo.intercalate (m24.splitOn " ")
  check "looksSecret: mnemonics separated by Unicode whitespace (\\u00A0, \\u3000) are detected"
    (WinnowApp.E2E.looksSecret s!"  before{nbsp}{nbsp}{m12Unicode}{nbsp}after  " &&
     WinnowApp.E2E.looksSecret m24Unicode)
  let invalid12 := " ".intercalate (List.replicate 12 "abandon")
  let invalid24 := " ".intercalate (List.replicate 24 "abandon")
  check "looksSecret: invalid 12-word and 24-word BIP39 checksums return false"
    (!WinnowApp.E2E.looksSecret invalid12 && !WinnowApp.E2E.looksSecret invalid24)
  let filler500 := " ".intercalate (List.replicate 500 "hello")
  let filler501 := " ".intercalate (List.replicate 501 "hello")
  check "looksSecret: exact 512-word window scans BIP39 while >512 words skips it"
    (WinnowApp.E2E.looksSecret s!"{filler500} {m12}" &&
     !WinnowApp.E2E.looksSecret s!"{filler501} {m12}")
  check "looksSecret: >512 words still detects extended private key prefixes"
    (WinnowApp.E2E.looksSecret s!"{filler501} XPRV9s21ZrQH143K")
  let prefixes := ["xprv", "tprv", "yprv", "zprv", "vprv", "uprv",
                   "XPRV", "TpRv", "YPRV", "zPrV", "VPRV", "UPRV"]
  check "looksSecret: detects all extended private key prefixes case-insensitively"
    (prefixes.all fun p => WinnowApp.E2E.looksSecret s!"key={p}9s21ZrQH")
  check "looksSecret: clean text, empty string, whitespace-only, and xpub/tpub return false"
    (!WinnowApp.E2E.looksSecret "" &&
     !WinnowApp.E2E.looksSecret s!"  {nbsp}  " &&
     !WinnowApp.E2E.looksSecret "Sent 12,345 sats to Alice" &&
     !WinnowApp.E2E.looksSecret "xpub661MyMwAqRbcFtXgS5sYJABqqG9YLmC4Q1Rdap9gSE8NqtwybGhePY2gZ29ESFjqJoCu1Rupje8YtGqsefD265TMg7usUDFdp6W1EGMcet8" &&
     !WinnowApp.E2E.looksSecret "tpubD6NzVbkrYhZ4XgiXtGrdW5XDAPFCL9h7wf1vwgmpnY6k")

  -- E2E.Mode.carriesThisRunsSeed and E2E.refusesFieldName
  let ent16 := ByteArray.mk (Array.replicate 16 0xAB)
  let words16 := match Winnow.Keys.BIP39.mnemonic ent16 with | .ok w => w | .error _ => ""
  let baseMode : WinnowApp.E2E.Mode :=
    { runID := "unit", peer := none, challenge := none, entropy := some ent16, reset := false,
      clipboard := none, forcedNetwork := none, requireDeviceAuthentication := false,
      controlFile := none, peerCount := none, syncIntervalSeconds := none }
  let noSeedMode := { baseMode with entropy := none }
  let emptySeedMode := { baseMode with entropy := some ByteArray.empty }
  let nonBip39SeedMode := { baseMode with entropy := some (ByteArray.mk #[0xDE, 0xAD, 0xBE, 0xEF]) }
  check "carriesThisRunsSeed: none and empty entropy return false"
    (!noSeedMode.carriesThisRunsSeed "clean" &&
     !noSeedMode.carriesThisRunsSeed "" &&
     !emptySeedMode.carriesThisRunsSeed "clean" &&
     !emptySeedMode.carriesThisRunsSeed "")
  check "carriesThisRunsSeed: detects run entropy hex and derived mnemonic case-insensitively, allows clean text"
    (!words16.isEmpty &&
     baseMode.carriesThisRunsSeed s!"seed={(Winnow.hex ent16).toUpper}" &&
     baseMode.carriesThisRunsSeed s!"backup: {words16.toUpper}" &&
     !baseMode.carriesThisRunsSeed "Sent 5,000 sats to Bob")
  check "carriesThisRunsSeed: non-BIP39 entropy length still detects hex and returns false on clean text"
    (nonBip39SeedMode.carriesThisRunsSeed "leak=DEADBEEF!" &&
     !nonBip39SeedMode.carriesThisRunsSeed "Sent 5,000 sats to Bob")

  let forbiddenKeys := ["entropy", "user_entropy_hex", "Mnemonic", "recovery-mnemonic",
                        "privateKey", "wallet_private_key", "secretNonce", "SECRET_NONCE_2",
                        "seedHex", "my-seed-hex"]
  let allowedKeys := ["", "12345", "txid", "amount", "phase", "id", "public_key", "address"]
  check "refusesFieldName: blocks all forbidden secret field substrings and allows normal keys"
    (forbiddenKeys.all WinnowApp.E2E.refusesFieldName &&
     allowedKeys.all (!WinnowApp.E2E.refusesFieldName ·))

/-- Pure unit tests covering every remaining branch of `stepHome`, `stepSend`, and `Model.onRelay`. -/
def stepHomeAndSendCases : IO Unit := do
  let ready : Model := { stage := .ready, active := true, generation := 4, settings := { network := .signet } }
  let loading : Model := { ready with stage := .loading }
  let onPay : Model := { ready with routes := [.payment "tx1"] }

  -- stepHome.openNetwork (.peers, .sync ready vs non-ready, .explorer, .verification)
  let (mSyncReady, csSyncReady) := stepHome (.openNetwork .sync) ready
  check "stepHome.openNetwork(.sync) while ready loads connected peers"
    (mSyncReady.routes == [.network .sync] && (csSyncReady matches [.connectedPeers 4]))
  let (mSyncLoad, csSyncLoad) := stepHome (.openNetwork .sync) loading
  check "stepHome.openNetwork(.sync) while not ready emits no connectedPeers"
    (mSyncLoad.routes == [.network .sync] && csSyncLoad.isEmpty)
  let (mExp, csExp) := stepHome (.openNetwork .explorer) ready
  check "stepHome.openNetwork(.explorer) pushes route with no commands"
    (mExp.routes == [.network .explorer] && csExp.isEmpty)

  -- stepHome.warningSettings (.routing, .network ready vs non-ready)
  let (mWarnNetReady, csWarnNetReady) := stepHome (.warningSettings .network) { ready with confirm := some (.homeWarning .network) }
  check "stepHome.warningSettings(.network) while ready opens Sync and loads peers"
    (mWarnNetReady.confirm.isNone && mWarnNetReady.routes == [.settings, .network .sync] &&
     (csWarnNetReady matches [.connectedPeers 4]))
  let (mWarnNetLoad, csWarnNetLoad) := stepHome (.warningSettings .network) loading
  check "stepHome.warningSettings(.network) while not ready emits no connectedPeers"
    (mWarnNetLoad.routes == [.settings, .network .sync] && csWarnNetLoad.isEmpty)
  let (mWarnRoute, csWarnRoute) := stepHome (.warningSettings .routing) ready
  check "stepHome.warningSettings(.routing) opens Peers and loads gateway draft"
    (mWarnRoute.routes == [.settings, .network .peers] && !csWarnRoute.isEmpty)

  -- stepHome payment-route guards (present vs absent)
  check "stepHome payment actions no-op when not on a payment route"
    ((stepHome .labelSender ready).2.isEmpty && (stepHome .labelSender ready).1.sheets.isEmpty &&
     (stepHome (.attachSenderDestination "p1") ready).1.sheets.isEmpty &&
     (stepHome .removeSenderLabel ready).2.isEmpty &&
     (stepHome .openFeeBump ready).2.isEmpty && (stepHome .openFeeBump ready).1.sheets.isEmpty)
  let (mLbl, _) := stepHome .labelSender onPay
  let (mAtt, _) := stepHome (.attachSenderDestination "p1") onPay
  let (_, csRemLbl) := stepHome .removeSenderLabel onPay
  let (mOpenBump, csOpenBump) := stepHome .openFeeBump onPay
  check "stepHome payment actions act when on a payment route"
    (mLbl.topSheet == some .addPerson && mLbl.person.mode == { txid := some "tx1" } &&
     mAtt.topSheet == some .addPerson && mAtt.person.mode == { personID := some "p1", txid := some "tx1" } &&
     (csRemLbl matches [.removeSenderLabel 4 "tx1"]) &&
     mOpenBump.topSheet == some .feeBump && (csOpenBump matches [.pendingFeeRate 4 "tx1"]))

  -- stepHome fee-bump guards (.setBumpRate, .reviewBump, .bump)
  let bumpPreview : WinnowApp.FeeBumpPreview := { feeRateMilli := 5000, fee := 700, change := some 1000 }
  let mReplaced := { ready with feeBump := { txid := "tx1", targetText := "3", replacement := some "tx2" } }
  check "stepHome.setBumpRate ignores edits after replacement broadcast"
    ((stepHome (.setBumpRate "9") mReplaced).1.feeBump.targetText == "3")
  check "stepHome.setBumpRate updates targetText when no replacement yet"
    ((stepHome (.setBumpRate "9") { ready with feeBump := { txid := "tx1" } }).1.feeBump.targetText == "9")
  check "stepHome.reviewBump no-ops on unparseable rate and previews valid rate"
    ((stepHome .reviewBump { ready with feeBump := { txid := "tx1", targetText := "bad" } }).2.isEmpty &&
     ((stepHome .reviewBump { ready with feeBump := { txid := "tx1", targetText := "5.5" } }).2 matches [.previewFeeBump 4 "tx1" "5.5" 5500]))
  let mReviewed := { ready with feeBump := { txid := "tx1", reviewed := some ("5.5", bumpPreview) } }
  check "stepHome.bump guards: no preview, already bumping, spendingInFlight, and ok"
    ((stepHome .bump ready).2.isEmpty &&
     (stepHome .bump { mReviewed with feeBump := { mReviewed.feeBump with bumping := true } }).2.isEmpty &&
     (let (mf, cf) := stepHome .bump { mReviewed with spendingInFlight := true }
      mf.feeBump.error.isSome && cf.isEmpty) &&
     (let (mb, cb) := stepHome .bump mReviewed
      mb.feeBump.bumping && mb.spendingInFlight && (cb matches [.bumpFee 4 "tx1" _])))

  -- stepSend guards (.choosePerson, .review, .sendPayment, .editPayment, .newPayment)
  let (mChosen, csChosen) := stepSend (.choosePerson "p1") { ready with send := { inputs := { destination := "tb1qold" } } }
  check "stepSend.choosePerson sets personID and clears destination"
    (mChosen.send.inputs.personID == some "p1" && mChosen.send.inputs.destination == "" && csChosen.isEmpty)
  let validSend : Model := { ready with send := { inputs := { destination := "tb1qdest", amount := "10000" } } }
  check "stepSend.review guards: reviewing, sending, !canReview, and valid previewSend"
    ((stepSend .review { validSend with send := { validSend.send with reviewing := true } }).2.isEmpty &&
     (stepSend .review { validSend with send := { validSend.send with sending := true } }).2.isEmpty &&
     (stepSend .review { ready with send := { inputs := { destination := "tb1qdest", amount := "0" } } }).2.isEmpty &&
     ((stepSend .review validSend).2 matches [.previewSend 4 _]))
  let prevWallet : Preview :=
    { destination := "tb1qdest", amount := 10_000, fee := 200, feeRateMilli := 2000,
      inputCount := 1, change := some 500, locktimeLagsTip := false }
  let acctSrc : AccountSource := { id := "a1", name := "Shared", threshold := 2, signerCount := 2, psbt := "cHNidP8=" }
  let mPrev := { validSend with send := { validSend.send with preview := some prevWallet } }
  let mPrevAcct := { validSend with send := { validSend.send with preview := some { prevWallet with account := some acctSrc } } }
  check "stepSend.sendPayment guards: no preview, sending, spendingInFlight, wallet send, and multisig signAndDraft"
    ((stepSend .sendPayment validSend).2.isEmpty &&
     (stepSend .sendPayment { mPrev with send := { mPrev.send with sending := true } }).2.isEmpty &&
     (let (mf, cf) := stepSend .sendPayment { mPrev with spendingInFlight := true }
      mf.send.error.isSome && cf.isEmpty) &&
     (let (mw, cw) := stepSend .sendPayment mPrev
      mw.send.sending && mw.spendingInFlight && (cw matches [.sendPayment 4 _ _])) &&
     (let (ma, ca) := stepSend .sendPayment mPrevAcct
      ma.send.sending && ma.spendingInFlight && (ca matches [.signAndDraft 4 _ _])))
  check "stepSend.editPayment ignores while sending and clears preview otherwise"
    ((stepSend .editPayment { mPrev with send := { mPrev.send with sending := true } }).1.send.preview.isSome &&
     (stepSend .editPayment mPrev).1.send.preview.isNone)
  let (mNew, csNew) := stepSend .newPayment { mPrev with expanded := ["send.details", "send.fee", "send.review", "other"] }
  check "stepSend.newPayment resets send state, collapses send disclosures, and resolves rate"
    (mNew.send.preview.isNone && mNew.expanded == ["other"] && (csNew matches [.resolveRate 4 _ _]))

  -- Model.onRelay (wrong txid, announced, requested new & dup, echoed new & dup, feeFloorExceeded, confirmed missing/unconfirmed/confirmed)
  let sent : Model := { ready with send := { sentTxid := some "tx1" } }
  check "Model.onRelay ignores events for another txid"
    ((sent.onRelay "other" (.announced 2)).send.relayLog.isEmpty)
  let r1 := sent.onRelay "tx1" (.announced 3)
  let r2 := (r1.onRelay "tx1" (.requested "p1")).onRelay "tx1" (.requested "p1")
  let r3 := (r2.onRelay "tx1" (.echoed "p2")).onRelay "tx1" (.echoed "p2")
  let r4 := r3.onRelay "tx1" .feeFloorExceeded
  check "Model.onRelay records announced, deduplicated requested/echoed peers, and feeFloorExceeded"
    (r4.send.relayLog == ["Announced to 3 peer(s)", "Relayed to p1"] &&
     r4.send.relayedPeers == ["p1", "p2"] && r4.send.feeFloorNotice)
  let hUnconf : HistoryItem := { txid := "tx1", height := 0, received := 0, spent := 10_000, fee := some 200 }
  let hConf : HistoryItem := { hUnconf with height := 420 }
  check "Model.onRelay(.confirmed) handles missing, height 0, and confirmed height"
    ((r4.onRelay "tx1" .confirmed).send.confirmedHeight.isNone &&
     (({ r4 with status := { history := [hUnconf] } }).onRelay "tx1" .confirmed).send.confirmedHeight.isNone &&
     (({ r4 with status := { history := [hConf] } }).onRelay "tx1" .confirmed).send.confirmedHeight == some 420)

/-- Pure unit tests covering missed branches in `stepMultisigBuild`, `Model.onPeopleHost`, and `Model.onSystemHost`. -/
def stepMultisigBuildAndHostCases : IO Unit := do
  let kPhone := "kPhone"
  let kBob := "kBob"
  let kCarol := "kCarol"
  let sBob : SignerInfo := { id := "sBob", isLedger := false, name := "Bob", keys := [kBob], keysText := "11111111" }
  let acctEligible : MultisigInfo :=
    { id := "mElig", name := "Pair", descriptor := "tr(x)", balance := 0, policy := some "2 of 2",
      signerExpressions := [kPhone, kCarol], threshold := 2, signerCount := 2 }
  let acctThreshold : MultisigInfo :=
    { id := "mThresh", name := "Trio", descriptor := "tr(y)", balance := 0, policy := some "2 of 3",
      signerExpressions := [kPhone, kCarol, "kDave"], threshold := 2, signerCount := 3 }
  let acctNested : MultisigInfo := { acctEligible with id := "mNest", isNested := true }
  let base : Model :=
    { stage := .ready, active := true, generation := 9, settings := { network := .signet },
      sheets := [.signerPicker],
      multisig := { keyExpression := some kPhone, signers := [sBob], accounts := [acctEligible, acctThreshold, acctNested] },
      multisigBuild := { members := [{ keys := [{ key := kPhone, label := phoneLabel }] }] } }

  -- stepMultisigBuild: .pickSigner (missing, duplicate key, ok)
  check "stepMultisigBuild.pickSigner: missing signer and already-used key are no-ops"
    ((stepMultisig (.pickSigner "missing") base).1.multisigBuild.members.length == 1 &&
     (let mDup := { base with multisigBuild := { base.multisigBuild with
        members := [{ keys := [{ key := kBob, label := "Bob" }] }] } }
      (stepMultisig (.pickSigner "sBob") mDup).1.multisigBuild.members.length == 1))
  let (mPickedS, _) := stepMultisig (.pickSigner "sBob") base
  check "stepMultisigBuild.pickSigner: adds fresh signer and closes signerPicker"
    (mPickedS.multisigBuild.members.length == 2 && !mPickedS.hasSheet .signerPicker)

  -- stepMultisigBuild: .pickAccount (missing, ineligible nested, duplicate non-phone key, ok whole & threshold)
  check "stepMultisigBuild.pickAccount: missing, nested, and duplicate non-phone key are no-ops"
    ((stepMultisig (.pickAccount "missing") base).1.multisigBuild.members.length == 1 &&
     (stepMultisig (.pickAccount "mNest") base).1.multisigBuild.members.length == 1 &&
     (let mDupKey := { base with multisigBuild := { base.multisigBuild with
        members := [{ keys := [{ key := kPhone, label := phoneLabel }] },
                    { keys := [{ key := kCarol, label := "Carol" }] }] } }
      (stepMultisig (.pickAccount "mElig") mDupKey).1.multisigBuild.members.length == 2))
  let (mPickA1, _) := stepMultisig (.pickAccount "mElig") base
  let (mPickA2, _) := stepMultisig (.pickAccount "mThresh") base
  check "stepMultisigBuild.pickAccount: adds eligible account (equal and lower threshold) and closes picker"
    (mPickA1.multisigBuild.members.length == 1 && mPickA1.multisigBuild.members[0]!.threshold.isNone && !mPickA1.hasSheet .signerPicker &&
     mPickA2.multisigBuild.members.length == 1 && mPickA2.multisigBuild.members[0]!.threshold == some 2)

  -- stepMultisigBuild: .setRecoveryMode (0 and 1), .create (!canCreate vs canCreate), .registerLedger (busy vs idle), fallback
  check "stepMultisigBuild.setRecoveryMode clamps to 0 or 1"
    ((stepMultisig (.setRecoveryMode 1) base).1.multisigBuild.recoveryMode == 1 &&
     (stepMultisig (.setRecoveryMode 0) base).1.multisigBuild.recoveryMode == 0 &&
     (stepMultisig (.setRecoveryMode 5) base).1.multisigBuild.recoveryMode == 0)
  check "stepMultisigBuild.create guards !canCreate and emits createMultisigAccount when ready"
    ((stepMultisig .create base).2.isEmpty &&
     (let mReady := { base with multisigBuild := { base.multisigBuild with name := "Vault", preview := some (.ok "2 of 2") } }
      let (mc, cc) := stepMultisig .create mReady
      mc.multisigBuild.creating && (cc matches [.createMultisigAccount 9 "Vault" ..])))
  check "stepMultisigBuild.registerLedger guards busy and emits registerLedger when idle"
    ((stepMultisig (.registerLedger "mElig") { base with ledgerRegistering := some "other" }).2.isEmpty &&
     (let (mr, cr) := stepMultisig (.registerLedger "mElig") { base with ledgerRegisterError := some ("mElig", "old") }
      mr.ledgerRegistering == some "mElig" && mr.ledgerRegisterError.isNone && (cr matches [.registerLedger 9 "mElig"])))
  check "stepMultisigBuild fallback arm returns unchanged"
    ((stepMultisigBuild .openAdd base).2.isEmpty)

  -- Model.onPeopleHost (.pasteParsed stale/mismatched/ok/err, .senderLookup ok/stale/wrong-txid, fallback)
  let mPeople : Model := { base with person := { mode := { txid := some "tx1" }, pasted := "addr1", inferring := true } }
  let prev : PastePreview := { name := some "Alice", payTo := some true }
  check "Model.onPeopleHost.pasteParsed drops stale gen and mismatched text, applies ok and error"
    ((mPeople.onPeopleHost (.pasteParsed 8 "addr1" (.ok prev))).1.person.parsed.isNone &&
     (mPeople.onPeopleHost (.pasteParsed 9 "other" (.ok prev))).1.person.parsed.isNone &&
     (mPeople.onPeopleHost (.pasteParsed 9 "addr1" (.ok prev))).1.person.parsed == some prev &&
     (mPeople.onPeopleHost (.pasteParsed 9 "addr1" (.error "bad"))).1.person.error == some "bad")
  let (mLookOk, _) := mPeople.onPeopleHost (.senderLookup 9 "tx1" "mempool.space" ["tb1q1"])
  check "Model.onPeopleHost.senderLookup applies matching lookup and drops stale/wrong txid"
    (!mLookOk.person.inferring && mLookOk.person.inferredAddresses == ["tb1q1"] &&
     mLookOk.person.inferredSource == some "mempool.space" &&
     (mPeople.onPeopleHost (.senderLookup 8 "tx1" "src" ["tb1q1"])).1.person.inferring &&
     (mPeople.onPeopleHost (.senderLookup 9 "tx2" "src" ["tb1q1"])).1.person.inferring)
  check "Model.onPeopleHost fallback arm returns unchanged"
    ((mPeople.onPeopleHost (.launched none)).2.isEmpty)

  -- Model.onSystemHost (.copiedExpired, .bgtaskExpired via continuedSync id, pending mismatch,
  -- .continuedSyncRefused wrong-id/none-unavailable/none-other/running, .scene true with send/receive/onboarding/loading, .sceneInactive, fallback)
  let (mCopClr, _) := ({ base with copied := some "k1" }).onSystemHost (.copiedExpired "k1")
  let (mCopKeep, _) := ({ base with copied := some "k1" }).onSystemHost (.copiedExpired "k2")
  check "Model.onSystemHost.copiedExpired clears matching key only"
    (mCopClr.copied.isNone && mCopKeep.copied == some "k1")
  let cid := continuedSyncID .signet 1
  let mContReq := { base with continuedSync := some (.requested cid .signet 9 false) }
  let mContRun := { base with continuedSync := some (.running cid .signet 9 (some 3) false) }
  let (mExpById, csExpById) := mContReq.onSystemHost (.bgtaskExpired cid "processing" (some 3))
  check "Model.onSystemHost.bgtaskExpired routes by continuedSync id even when kind != continued"
    (mExpById.continuedSync.isNone && (csExpById matches [.completeBackgroundTask _ false (some 3)]))
  let mPend := { base with pendingBackgroundTasks := [("t1", "refresh", some 1)] }
  let (_, csPendMiss) := mPend.onSystemHost (.bgtaskExpired "t2" "refresh" (some 1))
  let (_, csPendTagMiss) := mPend.onSystemHost (.bgtaskExpired "t1" "refresh" (some 2))
  check "Model.onSystemHost.bgtaskExpired emits expireBackgroundTask when pending id or tag differs"
    ((csPendMiss matches [.expireBackgroundTask "t2" (some 1)]) &&
     (csPendTagMiss matches [.expireBackgroundTask "t1" (some 2)]))
  check "Model.onSystemHost.continuedSyncRefused handles wrong id, none+unavailable, none+other, and running"
    ((mContReq.onSystemHost (.continuedSyncRefused "other-id" "err" "")).1.continuedSync.isSome &&
     (let (mu, _) := base.onSystemHost (.continuedSyncRefused cid "unavailable" "ios<26")
      mu.continuedSyncOutcome == .refused "unavailable" "ios<26" && mu.continuedSyncAutoSuppressed) &&
     (base.onSystemHost (.continuedSyncRefused cid "tooManyPending" "")).1.continuedSyncOutcome == .none &&
     (mContRun.onSystemHost (.continuedSyncRefused cid "err" "")).1.continuedSync.isSome)
  let mSendRecv := { base with active := false, sheets := [.send, .receive], receive := { address := "tb1qaddr" } }
  let (_, csSceneReady) := mSendRecv.onSystemHost (.scene true)
  let (_, csSceneEmptyAddr) := ({ mSendRecv with receive := { address := "" } }).onSystemHost (.scene true)
  let (_, csSceneOnbNoW) := ({ base with active := false, stage := .onboarding, walletID := none }).onSystemHost (.scene true)
  let (_, csSceneOnbW) := ({ base with active := false, stage := .onboarding, walletID := some "w1" }).onSystemHost (.scene true)
  let (_, csSceneLoad) := ({ base with active := false, stage := .loading }).onSystemHost (.scene true)
  check "Model.onSystemHost.scene(true) covers send rate, receive watchAddress, onboarding with/without wallet, and loading"
    (csSceneReady.any (· matches .resolveRate ..) &&
     csSceneReady.any (· matches .watchAddress 9 "tb1qaddr") &&
     !csSceneEmptyAddr.any (· matches .watchAddress ..) &&
     csSceneOnbNoW.any (· matches .discoverCloud) &&
     csSceneOnbW.any (· matches .startNetworking ..) && !csSceneOnbW.any (· matches .discoverCloud) &&
     !csSceneLoad.any (· matches .startNetworking ..))
  check "Model.onSystemHost.sceneInactive and fallback arm"
    (((base.onSystemHost .sceneInactive).2 matches [.journal "app.scenePhase" [("phase", "inactive")]]) &&
     (base.onSystemHost (.launched none)).2.isEmpty)

/-- Pure unit tests covering edge branches in `URLText.validScheme`, `URLText.ipLiteral`,
`PeerRoutingState`, `E2E.isWhitespaceCluster`, and `E2E.swiftInt?`. -/
def pureHelperEdgeCases : IO Unit := do
  -- URLText.validScheme
  check "URLText.validScheme covers empty, non-alpha start, upper/lower/digits/+/-/. and invalid tail"
    (!URLText.validScheme "" && !URLText.validScheme "1http" &&
     URLText.validScheme "a" && URLText.validScheme "Z" &&
     URLText.validScheme "Http+v2-a.0" && !URLText.validScheme "http_s")

  -- URLText.ipLiteral
  check "URLText.ipLiteral covers plain, sub-delim, invalid/non-ASCII addr, valid/re-encoded zones"
    (URLText.ipLiteral "::1" == some "::1" &&
     URLText.ipLiteral "v1.a!b" == some "v1.a!b" &&
     URLText.ipLiteral "fe80::1/2" == none &&
     URLText.ipLiteral s!"fe80::{String.singleton (Char.ofNat 0x00E9)}" == none &&
     URLText.ipLiteral "fe80::1%25en0" == some "fe80::1%25en0" &&
     URLText.ipLiteral "fe80::1%25en 0" == some "fe80::1%2525en%200" &&
     URLText.ipLiteral "fe80::1%en0" == some "fe80::1%25en0" &&
     URLText.ipLiteral "fe80::1%en 0" == some "fe80::1%25en%200" &&
     URLText.ipLiteral s!"fe80::1%{String.singleton (Char.ofNat 0x00E9)}" == some "fe80::1%25%C3%A9")

  -- PeerRoutingState helpers across all 8 states
  let states : List PeerRoutingState :=
    [.checking, .overlay true true, .overlay true false, .overlay false true,
     .mixed, .direct true, .direct false, .offline]
  check "PeerRoutingState.message/warns/shortLabel/alertTitle/symbol cover all states"
    (states.all (fun s => !s.message.isEmpty && !s.symbol.isEmpty && !s.alertTitle.isEmpty) &&
     (PeerRoutingState.overlay false true).message == "Private: peers reached through I2P" &&
     (PeerRoutingState.overlay true false).message == "Private: peers reached through Tor" &&
     (PeerRoutingState.direct false).message == "Direct: peers can see your IP address" &&
     PeerRoutingState.offline.warns && PeerRoutingState.offline.shortLabel == "Routing settings invalid" &&
     PeerRoutingState.offline.alertTitle == "Peer routing is offline" &&
     !PeerRoutingState.checking.warns && PeerRoutingState.checking.shortLabel == "")

  -- E2E.isWhitespaceCluster across every Unicode White_Space scalar range plus empty and non-whitespace
  let wsScalars : List Nat :=
    [0x09, 0x0A, 0x0D, 0x20, 0x85, 0xA0, 0x1680, 0x2000, 0x200A, 0x2028, 0x2029, 0x202F, 0x205F, 0x3000]
  let nonWsScalars : List Nat := [0x08, 0x0E, 0x41, 0x200B, 0x2060]
  check "E2E.isWhitespaceCluster covers empty, all Unicode White_Space codepoints, and non-whitespace"
    (!WinnowApp.E2E.isWhitespaceCluster "" &&
     wsScalars.all (fun n => WinnowApp.E2E.isWhitespaceCluster (String.singleton (Char.ofNat n))) &&
     nonWsScalars.all (fun n => !WinnowApp.E2E.isWhitespaceCluster (String.singleton (Char.ofNat n))))

  -- E2E.swiftInt?
  check "E2E.swiftInt? covers empty, lone signs, non-digits, signed/unsigned values, and int64 bounds"
    (WinnowApp.E2E.swiftInt? "" == none &&
     WinnowApp.E2E.swiftInt? "+" == none &&
     WinnowApp.E2E.swiftInt? "-" == none &&
     WinnowApp.E2E.swiftInt? "12a" == none &&
     WinnowApp.E2E.swiftInt? "0" == some 0 &&
     WinnowApp.E2E.swiftInt? "42" == some 42 &&
     WinnowApp.E2E.swiftInt? "+42" == some 42 &&
     WinnowApp.E2E.swiftInt? "-42" == some (-42) &&
     WinnowApp.E2E.swiftInt? "9223372036854775807" == some 9223372036854775807 &&
     WinnowApp.E2E.swiftInt? "9223372036854775808" == none &&
     WinnowApp.E2E.swiftInt? "-9223372036854775808" == some (-9223372036854775808) &&
     WinnowApp.E2E.swiftInt? "-9223372036854775809" == none)

def main : IO UInt32 := runMain "records-test" do
  let root ← IO.FS.createTempDir
  IO.println s!"records-test in {root}"
  syncErrorBookkeeping
  parseDoubleCases
  appErrorsAndVault
  stepPeopleCases
  stepMultisigAccountAndCollectCases
  looksSecretCases
  stepHomeAndSendCases
  stepMultisigBuildAndHostCases
  pureHelperEdgeCases
  foundationURLRules
  bundleVersion
  peerGatewayModel
  homeWarnings
  syncBookkeepingScreens
  backgroundRuns
  backgroundTaskCommands
  continuedBackgroundSync
  testModeSeed
  walletSlots root
  walletSwitcher root
  recordsLockedRow
  try
    let a ← newPhone root "A"
    let b ← newPhone root "B"
    peopleAndPastes a b
    personCards a b
    receiveLabels a b
    lookupSenderTest b
    let before ← a.records
    tamper root a
    reopenFromDisk a before
    paymentIndexAndPayTo a b
    sealFailures root
    screens root
  catch e =>
    check "the script ran to the end" false (toString e)
