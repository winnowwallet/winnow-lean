# Out-of-band private payments: a silent payment address and a tweak per person

Proposal for [issue #94](https://github.com/winnowwallet/winnow-lean/issues/94), written 2026-11-14.

> Status at this revision: built end to end on regtest. The derivation
> (`Lean/Winnow/Keys/SilentPaymentPairing.lean`); a wallet that issues cards, finds what is paid with them,
> spends it and restores it (`Lean/Winnow/Wallet/Wallet.lean`); and the app: Receive → Share my card has "A
> card for one person", a saved person can be paid by the card they sent, and a payment made with a card is
> named as its person's. None of it has run on a device, on signet or on mainnet. "Results" says what was
> checked and how.

## The problem

Winnow's card (Receive → Share my card) carries the wallet's account key:
`tr([fingerprint/86'/coin'/0']xpub…/<0;1>/*)`. Everybody gets the same card. Each holder can derive every
receive and change address the wallet has or will have, so each holder can read the wallet's whole history
and balance from the chain.

A silent payment address (BIP352) does not have that problem, but its payments are found by scanning: the
address a payment goes to depends on the coins the payer spent, so the recipient has to try every
transaction on the chain. A wallet that syncs by compact filters cannot do that from filters, and Winnow
sends silent payments but does not receive them.

The issue asks for the cooperative alternative: the two sides agree on something beforehand, so the
recipient need not scan, and the payment is still an ordinary transaction only the recipient can spend.

## The design

The recipient hands one person, once, **their silent payment address and a tweak made for that person**.
The payer's wallet does the silent payment calculation with that tweak where BIP352 has the number made
from the payer's coins. Nothing else changes.

```
Bob's address       scan key  m/352'/coin'/0'/1'/0        spend key  m/352'/coin'/0'/0'/0      (BIP352's paths)
tweak for person k  x_k    = hash_Winnow/SilentPayment/Pairing(b_scan ‖ ser32(k))
shared secret       shared = x_k·B_scan                    BIP352: (input_hash·a)·B_scan
payment i           t_i    = hash_BIP0352/SharedSecret(ser_P(shared) ‖ ser32(i))
                    P_i    = B_spend + t_i·G               scriptPubKey 0x51 0x20 x(P_i)
Bob spends with     p_i    = b_spend + t_i mod n
```

- `hash_tag(m)` is BIP340's tagged hash. `ser32` is big-endian. `ser_P` is the 33-byte compressed point.
- The last two lines are BIP352's own output step, and the code that computes them is the function Winnow
  already uses to send silent payments (`SilentPaymentSending.outputScript`), held to BIP352's vectors.
- Because no input of the payer's enters, Bob knows every `P_i` before it is paid. His wallet keeps the
  next 20 for each person in the set it matches compact filters against. There is no scan and the payer
  sends nothing afterwards.
- `i` counts that person's payments (the saved person's payment index), not one transaction's outputs.
- `x_k` is a hash of the scan private key and the person's index, so the recovery phrase gives back every
  tweak the wallet ever handed out. A hash that is 0 or at least `n` is refused, for `x_k` and for `t_i`,
  about once in 2^128.
- A standard silent payment scan does not find these outputs. They are found by knowing `x_k`.

### The card

The person card Winnow already has, with `version` raised to 2 and one new field:

```json
{"name":"Bob","network":"regtest","payTo":"tsp1…","tweak":"<32 bytes, hex>","version":2,"winnow":"person-card"}
```

A Winnow from before this answers a version 2 card with "This card was made by a newer Winnow". It must
not read it as a plain silent payment address: paid the standard way, the payment would not be found. The
card is bounded as cards are (64 KiB), is about 300 bytes, and names no transaction, amount or height, so
it has no hint that could be wrong.

## Who knows what

| | Bob (recipient) | The person the card is for | Anyone else |
| --- | --- | --- | --- |
| `b_spend`, and so every `p_i` | yes | no | no |
| The address, `x_k`, and so every `t_i` and `P_i` | yes | yes | only if they get the card |
| That `P_i` is Bob's | yes | yes | no |

The payer cannot spend: `p_i = b_spend + t_i`, the payer knows `t_i` and `B_spend`, and finding `b_spend`
from `B_spend` is the discrete logarithm problem. `card-keys-test` checks the practical half for every
vector, and `card-regtest` checks it with Bitcoin Core: the recipient's key signs for the output; the
person's tweak, the output's tweak and the spend key alone do not.

The tweak is a privacy secret and not a spending secret. Whoever obtains a card can find the payments
made with it and can pay it. They cannot spend, and they learn nothing about another person's payments or
about the wallet's ordinary addresses.

Watching needs no private key: Bob made `x_k`, and `x_k·B_scan` is computed from public keys. Issuing a
card reads the scan private key, and spending reads the spend private key.

## What this packaging costs

Three consequences of using the wallet's one silent payment address for every person. Each was weighed
against a design with a separate key per person, which the first prototype used, and accepted.

1. **Two people who compare cards can tell they pay the same wallet.** Every card shows the same address.
   What they cannot do is find each other's payments: those need the other's tweak.
2. **A wallet that holds only its account key cannot make these cards.** BIP352's keys are below the
   master key. Such a wallet is told so (`cardsNeedThePhrase`) and nothing is recorded.
3. **The bare address is not safe to hand out on its own.** If someone copies the address out of a card
   and pays it the standard way from another wallet, Winnow does not find that payment: it would take a
   silent payment scan, or a notice from the payer. Winnow never shows the address by itself.

A coin records its card and its payment index, which is `{tweak data, k}` in BIP352's terms. Receiving a
standard silent payment by a notice from the payer would use the same record, with the tweak data taken
from the notice. That is not built.

## Alternatives considered

| | Messages | Recipient takes part first | The seed alone recovers | What the payer can derive |
| --- | --- | --- | --- | --- |
| A fresh address, handed over each time | one per payment | every time | yes | that one address |
| The shared account-key card (today) | one, ever | once | yes | every address of the wallet |
| A standard descriptor per person | one per person | once | yes | that person's addresses |
| **Address and tweak per person (built)** | one per person | once | yes | that person's addresses |
| A secret the payer picks | one per payment or per person, payer to recipient | no | no | what they paid |
| Standard BIP352 with a notice from the payer | one per payment, for prompt discovery | no | by scanning | nothing reusable |

- **A fresh address each time** is complete for two people standing together and needs nothing new. Its
  cost is an exchange per payment.
- **A descriptor per person** is the same idea in BIP32's terms: an unhardened child of a key `K` with
  chain code `c` is `K + HMAC-SHA512(c, K ‖ i)·G`, and the chain code plays the tweak's part. Other
  wallets can pay it. An extended key carries its parent's fingerprint and its child number.
- **A secret the payer picks** lets the recipient do nothing beforehand. The recipient's seed cannot
  reconstruct it, so a coin exists before the recipient holds what finds it, and a lost message can be a
  lost coin. It also needs the wallet to revisit old filters when the secret arrives late.
- **Standard BIP352 with a notice** keeps the payment fully standard and recoverable by a scan. It needs
  a message per payment and everything silent payment receiving needs.

## Hidden script paths

A Taproot output can be spent by its key or by a script committed inside the key. `P` has a script path
when `P = Q + hash_TapTweak(Q ‖ m)·G` for an internal key `Q` and a script tree `m` that someone knows.

A wallet that accepted any scalar `t` with `P = B + t·G` could be robbed: the payer takes `Q = B + x·G`,
puts their own key in `m`, supplies `t = x + hash_TapTweak(Q ‖ m)`, and later sweeps the coin through the
script. Here every `t_i` is a hash the wallet computes itself from the card and the index, so building
such an output needs a collision between two hashed lists, about 2^128 work.

The rule the wallet follows: it stores what a tweak is derived from (the card and the payment index) and
derives it, for watching, for signing and when it reads a backup. It never stores or accepts an output's
tweak. A person's tweak `x_k` is different: it is not secret from the payer and it is stored. A made-up
`x_k` under the wallet's own address still gives outputs only the wallet can spend, which
`multisig-test` shows.

## Backup and recovery

- **The phrase alone.** The address and every tweak derive from it. The wallet's state lists the cards it
  has issued, so in ordinary use nothing is guessed. A wallet rebuilt from the phrase alone looks ahead
  over cards (`Wallet.restoreCards`: 20 past the last one found paid) and scans back, repeating until a
  pass finds no further card. The cards it recorded stay recorded, paid or not, so an index that may have
  been handed out is never issued to someone else. The app does not run this yet: its phrase-only restore
  does not scan back for ordinary addresses either (the README: "words alone do not reconstruct its past
  transaction history"). The library's bounded back-scan does, and the regtest run uses it.
- **The backup file** carries the address, the issued cards and each coin's card and index, as version 3
  of the format (`docs/import.html`). A file with the phrase is refused if its address or any card's
  tweak is not what the phrase derives. The iCloud backup carries the same bundle.
- **The people file lost or damaged** (the recipient's): coins are found and spent as before. Who each
  card was for is lost.
- **The payer's phone lost.** The payer asks for the card again; it is the same card. A payer restored
  from an older backup repeats indices, which reuses addresses between the same two people. The coins are
  still credited: they are keyed by outpoint.
- **Gaps.** The recipient watches each card 20 indices past the highest one seen. The payer's index
  advances when a send commits. Twenty committed sends in a row that never confirm would put a later
  payment outside the window until a recovery scan widens it.
- **A card given to two people.** Both pay the same sequence and each can see the other's payments. The
  screen says the card is for one person and to send it only to them.
- **Showing a card again** is safe: person `k`'s card is always the same.

## States

The recipient's side has no pending state that depends on a message. A card is issued (written to the
wallet's state, with the address, before it is shown). A payment is credited when a block that passed the
wallet's filter-header and merkle checks contains an output whose script the wallet derived; the amount is
the output's own. From there it is a coin like any other: confirmations, a reorg that drops and re-finds
it, a spend.

- A payer's fee bump keeps its outputs, so the recipient credits whichever transaction confirms, once.
- Two outputs to the same `P_i` are two coins.
- A card pasted twice is one person: the address's two keys and the tweak identify it.
- An unconfirmed payment made with a card is not shown. The mempool window watches only the address on
  the Receive sheet.

The payer's side is the saved recipient Winnow already has: a person, a payment index, a review that
shows the address, device authentication, a send.

## Discovery

`0x51 0x20 x(P_i)` is in the BIP158 basic filter of the block that creates it and of the block that spends
it. The wallet matches whole scripts, so a card's scripts are more items in the set it already matches,
and a hit is verified against the block as every hit is. Nothing goes on the chain to help: no marker
output, no OP_RETURN.

Each card adds its used indices plus 20 scripts to the watched set. A wallet issues at most 1,000 cards.

## The channel

The card's confidentiality and integrity are those of whatever carried it.

- **A QR code on the screen** is read by whoever can see the screen. In person this is the strongest
  channel available. Winnow shows QR codes and cannot scan them: LeanNative has no camera capability, so
  between two Winnows the card travels as text.
- **The share sheet** hands the text to whatever the person picks. A channel that lets a third party
  replace the text lets them be paid instead, exactly as with a replaced address.
- **Paste** reads the system clipboard, which other apps can read and which may sync to the person's
  other devices. What leaks is the card.
- **Bluetooth.** LeanNative's `ble.*` is the central role only. Phone to phone needs the peripheral role,
  which it does not have, and a session of its own, since a connection without pairing is not encrypted.
- **NFC.** Reading a tag and behaving as a card are different capabilities on iPhone, with different
  entitlements. None of this was tested, and LeanNative has no NFC capability. Proximity is not
  authentication.

Nothing in the design depends on the channel. A camera, Bluetooth and NFC are LeanNative work that any
later transport shares.

## Privacy: what is established and what is not

Established by the construction and held by tests:

- The outputs are ordinary key-path Taproot outputs.
- Two people's tweaks differ, and a card derives its own scripts and no others.
- The account key, which the shared card carries, derives none of these: the silent payment keys are on
  another hardened branch.

Limits the construction does not address:

- Everyone given a card of one wallet sees the same address.
- The payer knows which outputs they paid.
- When the recipient spends such a coin together with other coins, the transaction ties them together for
  any observer, and tells the payer about coins they did not pay.
- Amounts, timing, and the metadata of the channel that carried the card.

Not offered: these are Taproot outputs with their public keys on the chain, so this is not quantum-secure
Bitcoin. Whether an attacker who can compute discrete logarithms could link one person's payments was not
analysed: with the scan private key they can derive every tweak.

## What is built

- **Keys.** `SilentPaymentPairing`: the address from the master key, a person's tweak, the shared secret,
  each payment's script (through `SilentPaymentSending.outputScript`) and the spending secret.
- **Wallet.** `Wallet.issueCard` records the address and the card before answering; the watched set holds
  each card's window; a coin records its card and index; `Wallet.spendSecret` signs with
  `b_spend + t_i` after holding the address to the key; the backup carries all of it as version 3 and
  import derives every script again; `Wallet.restoreCards` serves a wallet rebuilt from the phrase. A
  wallet that never issues a card writes the same wallet file and the same version 2 backup as before.
- **People and the screen.** A person's pay-to can be an address with a tweak (`PersonPayTo.card`), read
  from a version 2 person card. On the card sheet, "A card for one person" comes first: a name, the
  device's owner is asked, the card is shown with its QR code, Copy and Share; shown again it reads no key
  and does not ask. The card everybody can be given is under it. Saved recipients have "Make a card" /
  "Their card". The person is saved as a contact with a link to their card; the card stays in the wallet's
  state. When a block pays a card, the sync labels the payment with the card's person, unless it already
  has a label, and the screen reads its records again.

## Results

All on 2026-11-14, every test executable rebuilt first.

- **The derivation.** `card-keys-test`: 207 checks, 0 failed, against `Lean/Vectors/card-keys-vectors.json`
  (4 cards, 18 payments, output keys of both parities), which `scripts/card-keys-vectors` computes with the
  Python standard library and none of the wallet's code. Each script is also checked to be
  `SilentPaymentSending.outputScript`'s answer for the shared secret, and not what a standard silent
  payment to the same address pays. The recipient's key signs for every output; the person's tweak, the
  output's tweak and the spend key alone do not.
- **The wallet, without a node.** `multisig-test`: 791 checks, 0 failed, 74 of them in seven tests of cards.
  A payer that holds only a card's text pays three indices in one transaction; the two inside the window
  are credited and the one outside is not. A spend of card coins with an ordinary coin, and its fee bump,
  carry signatures that verify under BIP341's sighash for each coin's key. A fork takes a payment away and
  it is found again once. Backups round-trip; twelve altered backups are refused. An address claimed
  without the phrase is watched and not signed for; a made-up tweak under the wallet's own address is
  watched and spent. A wallet that holds only its account key is refused a card. A wallet rebuilt from the
  phrase finds nothing, records the cards it could have issued, then finds and spends all three payments.
- **Regtest, Bitcoin Core 31.1 as the payer.** `card-regtest`: 24 checks, 0 failed. Core pays two indices;
  the wallet finds both through the basic filters Core serves. Core replaces a third payment before it
  confirms; it is credited once, under the replacement's txid. Its block is invalidated and the payment
  mined again; it is credited once in the block that then holds it. One transaction spending a card's
  coin is offered to Core four times: signed with the person's tweak, with the output's tweak, or with
  the spend key alone, Core answers "Invalid Schnorr signature"; signed with the spend key plus the
  output's tweak, Core takes it. A second wallet from the same phrase, its frontier already past every
  payment, finds none; after `restoreCards` and two passes of `scanRange` over the same filters it holds
  the same three coins and spends them in a transaction Core mines.
- **The app.** `records-test`: 1,517 checks, 0 failed: the people store (a card by name and by ID, the same
  card when asked again, the link through an iCloud restore plan, a card for another network or with a bad
  tweak refused in a sentence) and the card sheet through the app's own `perform` with a fake shell (the
  per-person section first; making a card asks the device's owner once, declining makes none and says
  nothing, showing it again does not ask). `backend-test`: 346 checks, 0 failed, three runs: its two-phone
  flow has Bob make a card for Alice, Alice pay it twice from her saved person at addresses the shared
  card's key does not derive in its first 200, and Bob's wallet find both, name both as Alice's and spend
  them. The journey `cardForOnePerson` passes headless with the other nine.
- **The rest, unchanged in behaviour:** `silent-payment-test` 272, `crypto-test` 4,246, `ledger-test` 230,
  `multisig-app-test` 667, `cloud-backup-test` 194, `ledger-transport-test` 17, `io-test` 404,
  `multisig-differential` 588, `fuzz` 230,000 cases; all 0 failed.
- **One earlier failure, not seen again.** With the first prototype (a separate key per person),
  `backend-test` failed once in ten runs: five checks in an existing flow that races a sync against
  loading a payment's details (`paymentRaceFlow`, "Another"). It passed three times of three on main and
  three of three at this revision. The cause was not found.
- **Two simulators, by hand.** The iOS app on an iPhone 17 Pro and an iPhone 17 simulator (iOS 26.5), each
  with its own wallet, against one regtest node. Alice made a card for Bob on the card sheet and copied
  its text; the text was moved to the other simulator's pasteboard with `simctl`, since the simulator has
  no AirDrop. Bob pasted it into a new saved recipient, which read "Fresh address each payment", and paid
  250,000 sats to the address his app showed for her, which is the output the mined transaction carries.
  After one block Alice's Home showed 250,000 sats and "Received from Bob · Confirmed". The run found two
  layout faults, both since fixed and looked at again in the simulator: the shared card's explanation was
  drawn a second time under the person's card, and the card button pushed Remove off a saved recipient's
  row. It also found that "Paste from clipboard" reads nothing in this simulator, which cannot show iOS's
  paste prompt; the text field's own Paste was used. Whether the button works on a device was not checked.
- **What these runs do not show:** a device, an unconfirmed payment, more than one peer, mainnet or signet,
  or two real phones exchanging a card by QR code, AirDrop or a message.

## Open

1. **The shared card.** It stays, under the per-person section. Retire it or keep it.
2. **Receiving standard silent payments**, by a notice from the payer or by a scan, which would also make
   the bare address safe to hand out.
3. **The app recovering cards from the phrase**, by running the back-scan the library has.
4. **Showing an unconfirmed payment** made with a card.
5. **LeanNative capabilities**: a camera for QR codes, the Bluetooth peripheral role, NFC, and in which
   order.
6. **A per-payment request** with an amount and an expiry, for "pay exactly this, now".

## References

- [BIP352](https://bips.dev/352/), including its out-of-band notifications appendix
- [BIP32](https://bips.dev/32/), [BIP340](https://bips.dev/340/),
  [BIP341](https://bips.dev/341/#constructing-and-spending-taproot-outputs)
- [BIP157](https://bips.dev/157/), [BIP158](https://bips.dev/158/)
- `Lean/Winnow/Keys/SilentPaymentPairing.lean`, `Lean/CardKeysTest.lean`, `scripts/card-keys-vectors`
