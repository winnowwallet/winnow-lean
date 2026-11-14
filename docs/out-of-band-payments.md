# Out-of-band private payments: a card per person

Proposal for [issue #94](https://github.com/winnowwallet/winnow-lean/issues/94), written 2026-11-14.

> Status at this revision: built end to end on regtest. The card code and its derivation
> (`Lean/Winnow/Keys/CardKeys.lean`); a wallet that issues cards, finds what is paid to them, spends it and
> restores it (`Lean/Winnow/Wallet/Wallet.lean`); and the app: Receive → Share my card has "A card for one
> person", a saved person can be paid by the card they sent, and a payment to a card is named as its
> person's. None of it has run on a device, on signet or on mainnet. The sections "What the wallet does"
> and "Results" say what was checked and how.

## The problem

Winnow's card (Receive → Share your card) carries the wallet's account key:
`tr([fingerprint/86'/coin'/0']xpub…/<0;1>/*)`. Everybody gets the same card. Each holder can derive every
receive and change address the wallet has or will have, so each holder can read the wallet's whole history
and balance from the chain, and two holders can tell that they pay the same wallet.

The issue asks whether a secret exchanged privately between two parties can do better, and what it costs.
It names three constructions and a baseline. This document compares them, chooses one for a prototype,
and says what is left open.

## Decisions already taken (2026-11-14)

- The recipient issues the material: one card per person, derived from the recipient's own wallet seed.
  The payer chooses nothing.
- What finds and spends the coins lives in the wallet's state and its backup. The people file holds a link
  from a person to their card and nothing a coin depends on.
- The first transports are the ones the app has: a QR code on the screen and the share sheet going out,
  Paste coming in.

## Constructions compared

`B` is a recipient public key, `b` its private key, `G` the generator, `n` the group order.

| | Messages | Recipient takes part before the payment | The seed alone recovers | What the payer can derive | New in Winnow |
| --- | --- | --- | --- | --- | --- |
| A. A fresh address, handed over each time | one per payment | yes, every time | yes | that one address | nothing |
| B. The shared account-key card (today) | one, ever | once | yes | every address of the wallet | nothing |
| C. A standard descriptor per person | one per person | once | yes | that person's addresses | watching and signing for more than one key branch |
| D. A card code per person (prototype) | one per person | once | yes | that person's addresses | C's work, plus one derivation and one code format |
| E. A secret the payer picks, per payment | one per payment, payer to recipient | no | **no** | that one address | import, historical rescan, a backed-up secret per coin |
| F. A seed the payer picks, per relationship | one per relationship, payer to recipient | no | **no** | that relationship's addresses | E's work, plus lookahead and gap rules |
| G. BIP352 with a private notification | none required; one per payment for prompt discovery | no | by scanning every eligible transaction | nothing reusable | BIP352 receiving, spending and recovery |

On the chain all seven produce ordinary Taproot outputs that an observer cannot tie to each other or to
the recipient by the derivation alone. They differ in who must be present, what is lost with a message,
and how much one party learns about the other.

### A. A fresh address each time

Receive already shows a fresh address with its QR code and a Share button. For two people standing
together this is complete: the payer learns one address, the seed recovers the coin, and nothing new
needs review. Its cost is an interaction per payment. A nearby exchange over NFC or Bluetooth that only
carries an address needs no new derivation at all.

What a secret-based design gains over A is not privacy on the chain. It is that one exchange covers every
later payment, and that the recipient can tell who paid without being told.

### B. The shared card

One message, unlimited payments, recovery from the seed. Its cost is the problem this document starts
from.

### C. A standard descriptor per person

The recipient derives a key for each person along a hardened path and hands over
`tr(xpub…/0/*)`. The payer derives address `i` by BIP32's unhardened step. Winnow's payer side already
accepts this shape (`PersonPayTo.ofDescriptor`, `receiveOnlyDerivation`), and so does any wallet that
reads descriptors.

### D. A card code per person

The construction below. It is C with a different hash and a different envelope. BIP32's unhardened child
of a key `K` with chain code `c` is `K + HMAC-SHA512(c, K ‖ i)·G`; a card's payment is
`B + SHA256-tagged(network ‖ B ‖ s ‖ i)·G`. The chain code and the seed play the same part.

What D has that C lacks:

- The code carries a key and a seed and nothing else. An extended public key also carries its depth, its
  child number and its parent's fingerprint. Two cards of one wallet made as extended keys below one
  parent show the same parent fingerprint, so two holders who compare cards learn that they pay the same
  wallet, and the child numbers show how many cards came between. Zeroing those fields is possible and is
  then no longer what other software writes.
- The network is bound into every tweak and named by the code's prefix, so a card pasted into a wallet on
  another network is refused before anything is derived.
- The output key is used as it is, without BIP86's extra tweak. This saves nothing that matters.

What C has that D lacks:

- Other wallets can pay it.
- No construction of our own to review. D's derivation is small and follows BIP352's output step, but it
  is still ours, and only Winnow will ever pay a card code.

The wallet's work to watch and spend the coins is the same for both. Which of the two goes on the wire is
left to the owner (see "Open decisions"); the prototype uses D because the issue asks for the
secret-based design to be tried.

### E and F. A secret the payer picks

The recipient publishes one key `B`, which can be public. The payer draws a random `r`, pays
`B + H(tag ‖ network ‖ B ‖ r)·G` and sends `r` to the recipient afterwards. F exchanges a seed once and
counts.

Gains: the recipient does nothing before the payment, `B` can be printed anywhere without linking the
payments made to it, and the recipient scans nothing.

Costs, each of which the issue names:

- The recipient's seed cannot reconstruct `r`. A coin exists on the chain before the recipient holds what
  finds it. If the message is lost and the payer cannot be asked again, the coin is lost. No backup the
  recipient makes can cover a secret they have not received.
- The secret can arrive after its block was scanned. The wallet must then revisit old filters. The
  library can (`FilterSyncIO.scanRange`); the app never does, for any kind of address.
- A height the payer supplies is a claim. Trusting it to bound the rescan lets a wrong height hide the
  payment.
- If the wallet accepted a tweak instead of deriving it, the payer could build a hidden spending path
  (see "Hidden script paths").
- F adds index allocation across the payer's devices, gaps and lookahead.

Neither is built. They are the right tool only where the recipient cannot be reached before the first
payment, and for that case G is the standard answer.

### G. BIP352 with a notification

Standard silent payments, with the payer privately sending the outpoint and tweak so the recipient need
not scan. The derivation stays BIP352's, so scanning remains a recovery path that needs only the seed.
Winnow sends to codes and does not receive at one: receiving needs a scan key and a spend key, change
labels, verification that a notified output really follows BIP352 (a notified output that does not would
be spendable today and unrecoverable from the seed), and a scan that a compact-filter client cannot do
from filters alone, because the tweak depends on each transaction's inputs. The wallet file refuses the
`silentPaymentTweak` field upstream once wrote. Bringing receiving back is a project of its own.

## The construction

```
node_k = account private key / 2' / k'
b_k    = node_k's private key              B_k = b_k·G, 33 bytes compressed
s_k    = hash_Winnow/Card/Seed(node_k's chain code)
t_i    = hash_Winnow/Card/Tweak(network ‖ B_k ‖ s_k ‖ ser32(i))
P_i    = B_k + t_i·G                       scriptPubKey 0x51 0x20 x(P_i)
p_i    = b_k + t_i mod n
```

- `hash_tag(m)` is BIP340's tagged hash, `SHA256(SHA256(tag) ‖ SHA256(tag) ‖ m)`.
- `network` is one byte: 0 mainnet, 1 signet, 2 regtest. `ser32` is big-endian.
- `t_i` is not reduced. A hash that is 0 or at least `n` is refused (`invalidTweak`), about one index in
  2^128, so both sides always agree on what an index pays.
- A sum at infinity is refused. It needs `t_i = -b_k`, which the payer cannot aim for without `b_k`.
- `account` is the wallet's account key, `m/86'/coin'/0'`. Both steps below it are hardened. The account's
  public key, which the shared card carries, derives no card: hardened derivation needs the private key.
  A wallet that holds only its account private key can still derive its cards, which a path beside the
  account (`m/86'/coin'/1'`, say) would not allow.
- The seed comes from the node's chain code, which BIP32 derives separately from the node's private key.
  Knowing `s_k` says nothing about `b_k`.
- BIP340 signing negates a secret whose point has odd y, so `p_i` signs for `x(P_i)` at either parity.

### The code

Bech32m. The prefix names the network: `wnc` mainnet, `twnc` signet, `rwnc` regtest. The first data
character is the version, 0. The payload is `B_k ‖ s_k`, 65 bytes. A version 0 code is 115 or 116
characters. Decoding refuses bech32 (not bech32m), mixed case, an unknown prefix, another version, a
payload that is not 65 bytes, a key that is not on the curve, and text over 1,023 characters.

### The card

A card code travels in the person card Winnow already has, with `version` raised to 2:

```json
{"name":"Alice","network":"regtest","payTo":"rwnc1q…","version":2,"winnow":"person-card"}
```

A Winnow that predates card codes answers a version 2 card with "This card was made by a newer Winnow".
The card is bounded as cards are today (64 KiB) and is about 200 bytes, which fits a QR code, shared text
or a file. It names the network, the scheme (the version and the prefix) and the recipient's material. It
names no transaction, output, amount or height, so it has no hint that could be wrong.

## Who knows what

| | Issuer | The person the card is for | Anyone else |
| --- | --- | --- | --- |
| `b_k`, and so every `p_i` | yes | no | no |
| `B_k`, `s_k`, and so every `t_i` and `P_i` | yes | yes | only if they get the card |
| That `P_i` belongs to the issuer | yes | yes | no |

The payer cannot spend: `p_i = b_k + t_i`, the payer knows `t_i` and `B_k = b_k·G`, and finding `b_k` from
`B_k` is the discrete logarithm problem. `card-keys-test` checks the easy half of this for every vector:
the issuer's secret signs for the output, and neither the tweak nor the card's own private key does.

The seed is a privacy secret and not a spending secret. Whoever obtains a card can find the payments made
to it and can pay it. They cannot spend, and they learn nothing about another card or about the wallet's
own addresses.

There is no session secret. The card is a message that is safe to send once over a channel the two people
trust and useless to an attacker who cannot read that channel. If a nearby radio channel is added, its
session keys are separate from the seed and never reach the wallet's state (see "The channel").

## Hidden script paths

A Taproot output can be spent by its key or by a script committed inside the key. An output `P` has a
script path when `P = Q + hash_TapTweak(Q ‖ m)·G` for an internal key `Q` and a script tree `m` that
someone knows.

With a card the payer chooses neither `B_k` nor `s_k`, so every `t_i` is fixed before the payer acts. A
payer who pays some other key has not paid the card, and the wallet does not see it.

Where the payer picks the secret (E, F) the rule matters. A wallet that accepts any scalar `t` with
`P = B + t·G` can be robbed: the payer takes `Q = B + x·G`, puts their own key in a script tree `m`, and
supplies `t = x + hash_TapTweak(Q ‖ m)`. The recipient sees a matching output and credits it; the payer
sweeps it back through the script. Deriving `t` from a hash of the secret closes this to a collision
between two hashed lists, about 2^128 work, the same margin the curve gives. The rule for any future
construction is therefore: the wallet stores what a tweak is derived from and derives it, and never
stores or accepts a tweak.

The wallet follows that rule for cards as well: a coin records its card and index, signing derives the
tweak from them, and a backup's card coins are checked by deriving their scripts.

## Backup and recovery

- **The seed alone.** Card `k`'s key and seed derive from the account key, so the seed finds every card
  coin by trying cards 0, 1, 2, … and indices 0, 1, 2, … under each, as it tries addresses. The wallet's
  state lists the cards it has issued, so in ordinary use nothing is guessed. A wallet rebuilt from the
  phrase alone looks ahead over cards (`Wallet.restoreCards`: 20 past the last card found paid) and scans
  back, repeating until a pass finds no further card. The cards it recorded stay recorded, paid or not,
  so an index that may have been handed out is never issued to someone else. The app does not run this
  yet: its phrase-only restore does not scan back for ordinary addresses either (the README: "words alone
  do not reconstruct its past transaction history"). The library's bounded back-scan does, and the regtest
  run uses it.
- **The backup file** carries the issued cards and each coin's card and index, as version 3 of the format
  (`docs/import.html`). A file with the recovery phrase is refused if one of its cards is not the card the
  phrase derives. The iCloud backup carries the same bundle.
- **The people file lost or damaged** (the recipient's): coins are found and spent as before. Who each
  card was for is lost.
- **The payer's phone lost.** The payer loses the card and the index. They ask for the card again; it is
  the same card. A payer restored from an older backup repeats indices, which reuses addresses between
  the same two people. Coins are still credited: they are keyed by outpoint.
- **Gaps.** The recipient watches each card `gapLimit` (20) indices past the highest one seen. The
  payer's index advances when a send commits. Twenty committed sends in a row that never confirm would
  put a later payment outside the window until a recovery scan widens it.
- **A card given to two people.** Both pay the same sequence and each can see the other's payments to it.
  The screen says the card is for one person and to send it only to them.
- **Showing a card again** is safe: card `k` is always the same code.

## States

The recipient's side has no pending state that depends on a message. A card is issued (written to the
wallet's state before the code is shown). A payment to it is credited when a block that passed the
wallet's filter-header and merkle checks contains an output whose script the wallet derived; the amount
is the output's own. From there it is a coin like any other: confirmations, a reorg that drops and
re-finds it, a spend.

- A payer's fee bump keeps its outputs, so the replacement pays the same script and the recipient credits
  whichever confirms, once.
- Two outputs to the same `P_i` are two coins.
- A card pasted twice is one person: the code's key and seed identify it.
- An unconfirmed card payment is not shown. The mempool window watches only the address on the Receive
  sheet. This is a limit of the prototype.

The payer's side is the saved recipient Winnow already has: a person, a payment index, a review that
shows the address, device authentication, a send.

Not specified here: a message per payment that carries an amount, a request identifier and an expiry. A
card makes it unnecessary for paying. It would be needed for "pay exactly this, now" at a counter, and
could ride the same channels (see "Open decisions").

## Discovery

`0x51 0x20 x(P_i)` is in the BIP158 basic filter of the block that creates it, and in the filter of the
block that spends it. The wallet matches whole scripts (`filterMatches`), so a card's scripts are more
items in the set it already matches, and a hit is verified against the block as every hit is. Nothing
goes on the chain to help: no marker output, no OP_RETURN.

Each card adds its used indices plus 20 scripts to the watched set. A wallet issues at most 1,000 cards.

## The channel

The card's confidentiality and integrity are those of whatever carried it.

- **A QR code on the screen** is read by whoever can see the screen. In person this is the strongest
  channel available: the payer knows whose phone they are looking at. Winnow shows QR codes and cannot
  scan them: LeanNative has no camera capability. Between two Winnows the card therefore travels as text.
- **The share sheet** hands the text to whatever the person picks. A message to the wrong chat discloses
  the card. A channel that lets a third party replace the text lets them be paid instead, exactly as with
  a replaced address; the payer's review shows the person's name and the address, which catches neither.
- **Paste** reads the system clipboard, which other apps can read and which may sync to the person's
  other devices. What leaks is the card.
- **Bluetooth.** LeanNative's `ble.*` is the central role only, which is how Winnow reaches a Ledger.
  Phone to phone needs one phone to advertise (the peripheral role), which LeanNative does not have. A
  connection without pairing is not encrypted, so the card would need a session of its own: a reviewed
  handshake (Noise), and a way to know the peer, which without a camera means comparing a short code on
  both screens. It would carry the same card and improve nothing but convenience.
- **NFC.** Reading a tag and behaving as a card are different capabilities on iPhone, with different
  entitlements; an iPhone reading another iPhone needs the second to emulate a card. None of this was
  tested, and LeanNative has no NFC capability. A passive tag can hold a card, and anyone who reads the
  tag then has it. Proximity is not authentication: NFC can be relayed and overheard.

Nothing in the card's design depends on the channel. Adding Bluetooth, NFC or a camera is LeanNative
work, each with its own headless stand-in for the journeys.

## Privacy: what is established and what is not

Established by the construction and held by tests:

- Card outputs are ordinary key-path Taproot outputs.
- Two cards of one wallet share neither key nor seed, and the account's public key derives no card.
- A card derives its own scripts and no others.

Limits that the construction does not address:

- The payer knows which outputs they paid, with any construction.
- When the recipient spends a card coin together with other coins, the transaction ties them together for
  any observer, and tells the payer about coins they did not pay. Winnow's coin selection does not keep
  card coins apart.
- Amounts, timing, and the metadata of the channel that carried the card.

Conjectural:

- **Linking by an attacker who can compute discrete logarithms.** Such an attacker recovers `p_i` from any
  output and still cannot tell which outputs belong to one card without `s_k`, which is a hash output.
  That argument needs the seed to stay secret from the attacker, and `s_k` descends from the account's
  private key and chain code. The shared card publishes the account's public key and chain code, so the
  same attacker holding a shared card derives every card. The property is a hypothesis about a wallet
  whose account key was never handed out. It is not claimed.

Not offered:

- **Theft by that attacker.** These are Taproot outputs with their public keys on the chain. This is not
  quantum-secure Bitcoin.

## What the wallet does

Three pull requests.

1. **The construction** (done): the code, the derivation, vectors written by an independent
   implementation, fuzz targets, this document.
2. **The wallet** (done, in the library): `Wallet.issueCard` records a card in the wallet's state before
   answering its code; the watched set holds each card's window of scripts; a coin records its card and
   index; `Wallet.spendSecret` signs with `b_k + t_i` after checking the card against the key; the backup
   bundle carries cards (version 3) and import checks them; `Wallet.restoreCards` serves a wallet rebuilt
   from the phrase. A wallet that never issues a card writes the same wallet file and the same version 2
   backup as before.
3. **People and the screen** (done): a person's pay-to can be a card code (`PersonPayTo.card`), carried by a
   version 2 person card or pasted alone. On the card sheet, "A card for one person" takes a name, asks the
   device's owner, issues the card and shows it with its QR code, Copy and Share; shown again it reads no
   key and does not ask. Saved recipients have "Make a card" / "Their card". The person is saved as a
   contact with a link to their card (`PersonRecord.issuedCard`); the card itself stays in the wallet's
   state. When a block pays a card, the sync labels the payment with the card's person, unless it already
   has a label, and the screen reads its records again.

## Results

- 2026-11-14, pull request 1. `card-keys-test`: 257 checks, 0 failed, against
  `Lean/Vectors/card-keys-vectors.json` (5 cards, 22 payments, output keys of both parities), which
  `scripts/card-keys-vectors` computes with the Python standard library and none of the wallet's code.
  `fuzz`, 10,000 iterations: `card-keys` took 1,255 mutated inputs; `card-code` took 2, since a
  mutation almost always breaks the checksum. These show that the derivation matches a second implementation and that the issuer's
  secret, and neither secret the payer could hold, signs for an output. They show nothing about a wallet.
- 2026-11-14, pull request 2, without a node. `multisig-test`: 782 checks, 0 failed, 65 of them new, in
  seven tests of the wallet with cards. A payer that holds only the card's text pays three indices in one
  transaction; the two inside the window are credited and the one outside is not; the card's cursor moves
  and the wallet's address cursors do not. A spend of the card's coins together with an ordinary coin, and
  its fee bump, carry signatures that verify under BIP341's sighash for each coin's key. A fork takes a
  payment away and it is found again once. A silent payment from a card's coin pays the script BIP352
  derives from that coin's key. Backups round-trip; ten altered backups are refused;
  a card claimed without the phrase is watched and is not signed for. A wallet rebuilt from the phrase
  finds nothing, records the cards it could have issued, and then finds and spends all three payments.
- 2026-11-14, pull request 2, regtest. `card-regtest`: 23 checks, 0 failed, against Bitcoin Core 31.1, which
  is the payer. Core pays two indices of a card; the wallet finds both through the basic filters Core
  serves and credits them at their block. Core replaces a third payment before it confirms (`bumpfee`);
  the wallet credits it once, under the replacement's txid. The block is invalidated and the payment mined
  again in another; the wallet rolls back and credits it once in the block that now holds it. One
  transaction spending a card's coin is offered to Core three times (`testmempoolaccept`): signed with the
  tweak, which is all the payer holds, Core answers "Invalid Schnorr signature"; signed with the card's
  private key alone, the same; signed with their sum, Core takes it. A second wallet made from the same
  phrase, with its frontier already past every payment, finds none; after `restoreCards` and two passes of
  `scanRange` over the same filters it holds the same three coins, spends them all in one transaction that
  Core relays and mines, and the first wallet sees its card's coins spent.
- 2026-11-14, pull request 3. `records-test`: 1,513 checks, 0 failed. The store: a card for a person by
  name and by ID, the same card when asked again, another person's card, the link in the people file and
  through an iCloud restore plan, two people on one card refused, a card for another network refused in a
  sentence. The screen, through the app's own `perform` with a fake shell: making a card asks the device's
  owner once, declining makes none and says nothing, showing it again does not ask.
  `backend-test`: 346 checks, 0 failed, 18 of them a two-phone flow on Core 31.1: Bob makes a card for
  Alice, Alice pays it twice from her saved person, the two addresses are none the shared card's key
  derives in its first 200, Bob's wallet finds both, names both as Alice's and spends them, and his backup
  is version 3. The journey `cardForOnePerson` passes headless with the other nine.
- One unexplained failure. `backend-test` ran ten times across these changes: three times on main (328
  checks), three at pull request 2 (328) and four at pull request 3 (346). One run at pull request 2 failed
  five checks, all in an existing flow that races a sync against loading a payment's details
  (`paymentRaceFlow`, the "Another" case: "Finishing sync. Try loading the payment again in a moment.").
  The other nine passed. The card changes do not touch that flow; whether they make the race likelier was
  not established.
- What these runs do not show: a device, the simulator (the journeys ran headless only), an unconfirmed
  payment, more than one peer, mainnet or signet, or two real phones exchanging a card by QR code, AirDrop
  or a message. The exchange itself is Share and Paste, which the app already had.

## Open decisions

1. **C or D on the wire.** The prototype uses the card code. A per-person descriptor would let other
   wallets pay and removes our own derivation; it costs the metadata an extended key carries.
2. **The shared card.** It is still there, above the new section, with its own words about what it shows.
   Keep both, or retire it.
3. **Issuing a card** reads the wallet's private key, and the app asks for device authentication before
   every read of it. Issuing will therefore ask; showing an issued card again reads no key and will not.
   Say if issuing should not ask.
4. **Lookahead over cards** on a restore from the phrase. The library looks 20 cards past the last one
   found paid, and keeps them, which costs 400 watched scripts on a restored wallet.
5. **Payer-picked secrets (E, F).** This document recommends against building them: the recipient cannot
   back up what they have not received.
6. **BIP352 receiving (G)**, as the answer for a recipient who cannot be reached first.
7. **LeanNative capabilities**: a camera for QR codes, the Bluetooth peripheral role, NFC, and in which
   order.
8. **A per-payment request** with an amount and an expiry.

## References

- [BIP32](https://bips.dev/32/), [BIP86](https://bips.dev/86/), [BIP340](https://bips.dev/340/),
  [BIP341](https://bips.dev/341/#constructing-and-spending-taproot-outputs), [BIP350](https://bips.dev/350/)
- [BIP352](https://bips.dev/352/), including its out-of-band notifications appendix
- [BIP157](https://bips.dev/157/), [BIP158](https://bips.dev/158/)
- `Lean/Winnow/Keys/CardKeys.lean`, `Lean/CardKeysTest.lean`, `scripts/card-keys-vectors`
