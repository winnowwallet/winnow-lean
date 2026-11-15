# Out-of-band private payments: a shared secret and a spend key per person

Proposal for [issue #94](https://github.com/winnowwallet/winnow-lean/issues/94), written 2026-11-14, revised
2026-11-15 twice: the form a card's address is written in, and then what a card carries (a code, in place
of the wallet's two keys and a tweak).

> Status at this revision: built end to end on regtest. The derivation
> (`Lean/Winnow/Keys/SilentPaymentPairing.lean`); a wallet that issues cards, finds what is paid with them,
> spends it and restores it (`Lean/Winnow/Wallet/Wallet.lean`); and the app: Receive, under "From one person", makes an
> address and a card for one person, a saved person can be paid by the card they sent, a payment made with a card is
> named as its person's, and a phone restored from a backup looks for the cards made after it. The card
> for everybody is retired. Build 0.9.12 (TestFlight, internal group) made cards that carried the wallet's
> two keys and a tweak; those are still read and still found ("Cards made by 0.9.12"). "Results" says what
> was checked and how.

## The problem

Winnow's card (Receive → Share my card) carried the wallet's account key:
`tr([fingerprint/86'/coin'/0']xpub…/<0;1>/*)`. Everybody got the same card. Each holder can derive every
receive and change address the wallet has or will have, so each holder can read the wallet's whole history
and balance from the chain. Winnow no longer makes that card (decided 2026-11-14). One that another wallet
hands over is still read, saved and paid, and what is paid to one already handed out is still found: its
addresses are the wallet's own receive addresses.

A silent payment address (BIP352) does not have that problem, but its payments are found by scanning: the
address a payment goes to depends on the coins the payer spent, so the recipient has to try every
transaction on the chain. A wallet that syncs by compact filters cannot do that from filters, and Winnow
sends silent payments but does not receive them.

The issue asks for the cooperative alternative: the two sides agree on something beforehand, so the
recipient need not scan, and the payment is still an ordinary transaction only the recipient can spend.

## The design

A silent payment's payer multiplies the recipient's scan key by a number made from the coins being spent,
and what comes out, the shared secret, decides the address. Here the recipient makes that shared secret
beforehand, one per person, and hands it over: **the card carries the shared secret where a silent payment
address has the scan key, and a spend key made for that one person where it has the spend key.** The
payer's wallet starts the silent payment calculation one step in. Nothing after that step changes.

```
Bob's keys          scan key  m/352'/coin'/0'/1'/0        spend key  m/352'/coin'/0'/0'/0      (BIP352's paths)
tweak for person k  x_k = hash_Winnow/SilentPayment/Pairing(b_scan ‖ ser32(k))
shared secret       S_k = x_k·B_scan                       BIP352: (input_hash·a)·B_scan
label for person k  L_k = hash_BIP0352/Label(b_scan ‖ ser32(k + 1))     BIP352's label k + 1
their spend key     B_k = B_spend + L_k·G                  BIP352's labelled spend key
the card's code     S_k, B_k                               66 bytes
payment i           t_i = hash_BIP0352/SharedSecret(ser_P(S_k) ‖ ser32(i))
                    P_i = B_k + t_i·G                      scriptPubKey 0x51 0x20 x(P_i)
Bob spends with     p_i = b_spend + L_k + t_i mod n
```

- `hash_tag(m)` is BIP340's tagged hash. `ser32` is big-endian. `ser_P` is the 33-byte compressed point.
- The payment's two lines are BIP352's own output step, and the code that computes them is the function
  Winnow already uses to send silent payments (`SilentPaymentSending.outputScript`), held to BIP352's
  vectors. The label is BIP352's too, held to the labelled addresses in the same vectors. Label 0 is the one
  BIP352 keeps for change, so person `k` has label `k + 1`.
- `(B_scan, B_k)` is the labelled silent payment address BIP352 would give that person. The card holds its
  second half, and in place of the first what a payer would have made from it.
- The payer never holds `B_scan`, `B_spend` or `x_k`. Two cards of one wallet have no byte in common.
- Because no input of the payer's enters, Bob knows every `P_i` before it is paid. His wallet keeps the
  next 20 for each person in the set it matches compact filters against. There is no scan and the payer
  sends nothing afterwards.
- `i` counts that person's payments (the saved person's payment index), not one transaction's outputs.
- `x_k` and `L_k` are hashes of the scan private key and the person's index, so the recovery phrase gives
  back every card the wallet ever handed out. A hash that is 0 or at least `n` is refused, for `x_k`, `L_k`
  and `t_i`, about once in 2^128.
- A standard silent payment scan does not find these outputs. They are found by knowing `x_k`.

### The card

The person card Winnow already has, with `version` raised to 3 and its `payTo` a code:

```json
{"name":"Bob","network":"regtest","payTo":"twinnowcard1p…","version":3,"winnow":"person-card"}
```

The code is written like a silent payment address: bech32m over 66 bytes, with the human-readable part
`winnowcard` on mainnet and `twinnowcard` on every test network where a silent payment address has `sp` and
`tsp`, and as version 1 (`…1p…`). A wallet that does not know cards refuses such a string as an address of
no kind it knows, which is the point: it is not something another wallet can pay, and nothing in it can be
turned into something another wallet would pay to this wallet.

The code is the whole of what a card pays with, so Add person takes it pasted on its own as well as inside
a card; the card adds the name. Send does not take it as a destination: a card is paid through its person,
who counts its payments ("That is a Winnow card. Add it under Saved recipients and pay that person…").

Version 0 under the same prefix (`…1q…`) is the wallet's own two keys. The wallet's file and its backups
record them in that form and no screen shows them. They are never written as `sp1…`: an address copied
out and paid the standard way from another wallet makes an output only a scan of the chain finds, and
Winnow does no such scan.

A Winnow from before this answers a version 3 card with "This card was made by a newer Winnow". The card is
bounded as cards are (64 KiB), is about 200 bytes, and names no transaction, amount or height, so it has no
hint that could be wrong.

### Cards made by 0.9.12

For one build a card was version 2 and carried the wallet's two keys (`winnowcard1q…`) and the tweak:

```json
{"name":"Bob","network":"regtest","payTo":"twinnowcard1q…","tweak":"<32 bytes, hex>","version":2,"winnow":"person-card"}
```

Its payer computed `S_k = x_k·B_scan` and paid `B_spend + t_i·G`: the same shared secret, and the wallet's
own spend key with no label. Such a card is the code `S_k, B_spend`, and that is how it is kept:

- **Paying one.** A version 2 card is still read, as that code, and pays the addresses it always paid. A
  person saved by 0.9.12 is read into the same code when the people store is opened.
- **Having issued one.** An issued card records the spend key made for it, and a card from 0.9.12 has none:
  it is watched and spent under the wallet's own spend key, as before, and a backup with only such cards is
  still version 3. Handed out again, it is shown as the code `S_k, B_spend`.
- **Restoring from the phrase.** The phrase cannot say in which form a card was handed out, so a card
  recorded by a restore is watched in both, and a coin's form is read off its script when it is spent.
- The two keys pasted on their own, without the tweak, pay nothing and are refused ("That is the address
  from inside a Winnow card. On its own it cannot be paid: paste the whole card."), as is a card whose keys
  are written `sp1…` ("That card carries a plain silent payment address…").

### An address any wallet can pay

A card is paid by a Winnow. An exchange, or a person with another wallet, pays an ordinary address, so
under a person's card the sheet shows one: "An address for …". It is `P_i` for the card's lowest payment
not yet seen paid (`Wallet.nextCardAddress`), written as the Taproot address it is.

- It is inside the window the wallet already watches for that card, so the payment is found like any other
  made with the card, and is named as that person's. Nothing new is watched and no key is read.
- Once it is seen paid, the sheet shows the next. A payer that kept the old one and pays it again reuses
  an address; the payment is still found.
- The person's own Winnow counts its payments for itself, from 0. If one person pays both ways, a payment
  from their Winnow and one to this address can land on the same `P_i`: an address used twice, and both
  found.
- What the payer learns is one address. It is not the card: it derives nothing.

## Who knows what

| | Bob (recipient) | The person the card is for | Anyone else |
| --- | --- | --- | --- |
| `b_spend`, `L_k`, and so every `p_i` | yes | no | no |
| `B_scan`, `B_spend`, `x_k` | yes | no | no |
| `S_k`, `B_k`, and so every `t_i` and `P_i` | yes | yes | only if they get the card |
| That `P_i` is Bob's | yes | yes | no |

The payer cannot spend: `p_i = b_spend + L_k + t_i`, the payer knows `t_i` and `B_k`, and finding
`b_spend + L_k` from `B_k` is the discrete logarithm problem. `card-keys-test` checks the practical half
for every vector, and `card-regtest` checks it with Bitcoin Core: the recipient's key signs for the output;
the person's tweak, the output's tweak, the spend key alone and the spend key without the label do not.

The code is a privacy secret and not a spending secret. Whoever obtains a card can find the payments made
with it and can pay it. They cannot spend, and they learn nothing about another person's payments, about
the wallet's ordinary addresses, or about which other cards are this wallet's.

Watching needs no private key: Bob made `x_k` and recorded `B_k`, and `x_k·B_scan` is computed from public
keys. Issuing a card reads the scan private key, and spending reads both: the label is derived again from
the scan private key, never read from a file.

## What this packaging costs

Two consequences of deriving every person's card from the wallet's one pair of silent payment keys. Each
was weighed against a design with a separate key per person, which the first prototype used, and accepted.

1. **A wallet that holds only its account key cannot make these cards.** BIP352's keys are below the
   master key. Such a wallet is told so (`cardsNeedThePhrase`) and nothing is recorded.
2. **A card is not something another wallet can pay.** What it carries is not an address, and the wallet
   shows its real silent payment address nowhere, because a payment made to that the standard way is one
   Winnow does not find: that takes a silent payment scan, or a notice from the payer. The day Winnow can
   receive standard silent payments it will show the `sp1…` form as something separate from a card.

A third was removed on 2026-11-15. While a card carried the wallet's two keys, every card showed them, and
two people who compared cards could tell they paid the same wallet. A code holds neither key.

A coin records its card and its payment index, which is `{tweak data, k}` in BIP352's terms. Receiving a
standard silent payment by a notice from the payer would use the same record, with the tweak data taken
from the notice. That is not built.

## Alternatives considered

| | Messages | Recipient takes part first | The seed alone recovers | What the payer can derive |
| --- | --- | --- | --- | --- |
| A fresh address, handed over each time | one per payment | every time | yes | that one address |
| The shared account-key card (today) | one, ever | once | yes | every address of the wallet |
| A standard descriptor per person | one per person | once | yes | that person's addresses |
| **A shared secret and a spend key per person (built)** | one per person | once | yes | that person's addresses |
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
tweak, and it derives a card's label again from the scan private key whenever it signs. A person's tweak
`x_k` and spend key `B_k` are different: they are stored, since watching needs them and neither can spend.
A made-up `x_k` under the wallet's own keys still gives outputs only the wallet can spend, which
`multisig-test` shows; a made-up `B_k` is refused when the phrase is at hand, and without it gives outputs
the wallet watches and cannot sign for.

## Backup and recovery

- **The phrase alone.** The wallet's keys and every card's tweak and label derive from it. The wallet's
  state lists the cards it has issued, so in ordinary use nothing is guessed. A wallet rebuilt from the
  phrase alone looks ahead over cards (`Wallet.restoreCards`: 20 past the last one found paid) and scans
  back, repeating until a pass finds no further card. It cannot know whether a card was handed out as a
  code or by 0.9.12, so it watches each recorded card under both spend keys (`plainToo`), which doubles
  those cards' scripts. The cards it recorded stay recorded, paid or not, so an index that may have been
  handed out is never issued to someone else.
- **The app restoring from a backup.** A backup lists the cards made before it. Cards made after it are
  not in it, and a card made after a backup is paid after it. So a phone restored from a backup that
  carries the phrase records the cards it could have made (`Wallet.beginCardRestore`) before it scans
  forward from the backup's height, and that scan watches for them. If one of them was paid there may be
  more after it, paid in blocks the scan has passed: once the scan is at the tip, a sync pass records the
  next cards, scans those blocks again for their scripts alone, and repeats until a round records none
  (`finishCardRestore`). Whether there is anything to look for is read from the wallet's file; the phrase
  is read only when there is. The search is marked in the wallet's file until it ends, so one that a peer
  or the app's exit cuts short starts again. What this costs: every phone restored from a backup with the
  phrase keeps at least 20 cards recorded, watches their scripts, and from then on writes version 4
  backups, whether or not it ever made a card. What it does not do: look below the backup's height. The
  app never searches the past chain from a phrase (the README: "words alone do not reconstruct its past
  transaction history"), and a card left out of a backup that was made before it is found only from that
  height on. A backup without the phrase restores a wallet that cannot derive a card, and none is looked
  for. Who each found card was for is not recovered unless the people file is restored too.
- **The backup file** carries the wallet's two keys, the issued cards and each coin's card and index
  (`docs/import.html`). It is version 4 of the format once a card has a spend key of its own, so that
  0.9.12, which would take such a card for one paid to the wallet's key, refuses the file; with only cards
  0.9.12 issued it is version 3, as that build wrote it. A file with the phrase is refused if its keys, or
  any card's tweak or spend key, are not what the phrase derives. The iCloud backup carries the same
  bundle.
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
- A card pasted twice is one person: the code's two points identify it.
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
- Two people's cards have no key in common, and a card derives its own scripts and no others.
- A card holds neither of the wallet's silent payment keys.
- The account key, which a version 1 card carries, derives none of these: the silent payment keys are on
  another hardened branch.

Limits the construction does not address:

- The payer knows which outputs they paid.
- When the recipient spends such a coin together with other coins, the transaction ties them together for
  any observer, and tells the payer about coins they did not pay.
- Amounts, timing, and the metadata of the channel that carried the card.

Not offered: these are Taproot outputs with their public keys on the chain, so this is not quantum-secure
Bitcoin. Whether an attacker who can compute discrete logarithms could link one person's payments was not
analysed: with the scan private key they can derive every tweak and label.

## What is built

- **Keys.** `SilentPaymentPairing`: the wallet's two keys from the master key, a person's tweak, shared
  secret, label and spend key, their code (`CardCode`) and its bech32m form, each payment's script (through
  `SilentPaymentSending.outputScript`) and the spending secret; and a 0.9.12 card as a code (`codeOf`).
- **Wallet.** `Wallet.issueCard` records the wallet's keys and the card, with its spend key, before
  answering; the watched set holds each card's window under each spend key the card allows; a coin records
  its card and index; `Wallet.spendSecret` signs with `b_spend + L_k + t_i` (or `b_spend + t_i` for a coin
  paid to the wallet's own spend key, which it reads off the coin's script) after holding the recorded keys
  to the phrase; the backup carries all of it as version 4 (3 with only 0.9.12's cards) and import derives
  every script again; `Wallet.restoreCards` serves a wallet rebuilt from the phrase, and
  `beginCardRestore`, `wantsMoreCards` and `endCardRestore` a phone restored from a backup. A wallet that
  never issues a card and was never restored writes the same wallet file and the same version 2 backup as
  before.
- **People and the screen.** A person's pay-to can be a card's code (`PersonPayTo.card`), read from a
  version 3 person card, from the code pasted alone, or from a version 2 card of 0.9.12. Receive is one page: the
  wallet's own address at once, and under it "From one person", where a name gives that person's ordinary
  address and their card, each with its QR code, Copy and Share. The device's owner is asked the first time;
  shown again it reads no key and does not ask. The wallet's own name on the card is optional. Until
  2026-11-15 Receive asked for a label before it showed an address, and the card was on a sheet of its own
  ("Make a card") that asked for two names. The card for everybody is no longer made or shown.
  Under each saved recipient is "Make …’s address and card" or "Show …’s address and card". The person is saved
  as a contact with a link to their card; the card stays in the wallet's
  state. When a block pays a card, the sync labels the payment with the card's person, unless it already
  has a label, and the screen reads its records again.

## Results

On 2026-11-14, and every count below again on 2026-11-15 at the revision that made Receive one page;
every test executable rebuilt first.

- **Receive as one page (2026-11-15).** `records-test`: the address is shown at once and nothing is asked
  first; a label is asked for only from "Label this address", and Cancel goes back; "From one person" is on
  the same page and needs only their name, with or without a name of the wallet's own; what is made is shown
  on that page, the address before the card, and the button is gone once it is; another name takes it off,
  and closing Receive clears it. The journey makes Dana's address and card from Receive with her name alone,
  finds her address is not the wallet's own, and reopens Receive to see the same card. In the simulator
  (iPhone 17, iOS 26.5, Debug build): Receive opened on the address, and "Carol" typed under "From one
  person" showed her address and her card on the same page. Not shown: a device.

- **An address any wallet can pay (2026-11-15).** `multisig-test`: the address is the card's first payment
  as its person's code derives it; paid from outside it is the card's coin and the address becomes the
  next; paid again at the old address the payment is found and the address does not go back; after the
  person's own Winnow pays further on, it is the payment after that; another card's does not move; the
  coins are spent; and a 0.9.12 card's address is that card's next payment in its own form. `records-test`:
  by name and by ID, another person's is another, a person without a card or nobody has none, and asking
  issues no card; on the sheet it is shown under the card with what it is for, leaves with the card, and a
  card that arrives without one is shown without one. `backend-test`, regtest: Bitcoin Core, which knows
  nothing of cards, pays Alice's address; Bob's wallet finds the payment, names it as Alice's without Bob
  labelling it, and the address is then another. It is also the address Alice's own phone would have paid
  next. The journey reads the address under the card and finds it is the card's first. In the simulator
  (iPhone 17, iOS 26.5, Debug build), on the wallet a build of that morning left with a card in 0.9.12's
  form: the wallet opened, the card was shown again as a version 3 card with a `twinnowcard1p…` code, and
  under it "An address for Carol" with a `bcrt1p…` address, its QR code, Copy and Share. Not shown: a real
  exchange, a mainnet payment, and a device.

- **A card carries a code (2026-11-15).** The vectors were written again by `scripts/card-keys-vectors`:
  every field they had is unchanged, and each case gains the person's label, spend key and code and the
  payments made to it (15), with the code a 0.9.12 card becomes. `card-keys-test` holds the label to BIP352's
  own vectors (the 8 labelled addresses in `bip352-send-receive-vectors.json`), and adds that a code holds
  neither of the wallet's keys, that two codes of one wallet share none, that a 0.9.12 card and its code pay
  the same scripts, that the spend key without the label is refused for a labelled output, and what a
  damaged code or one of another network is answered. `multisig-test` adds a wallet file written as 0.9.12
  wrote it (its card still watched and spent, handed out again as the code that pays the same scripts, its
  backup still version 3, the next card labelled and the backup then version 4), a restore from the phrase
  that finds one payment made in each form and spends both in one transaction, and five more altered
  backups refused. `records-test` adds the code pasted alone, a 0.9.12 card and a person saved by 0.9.12
  read into the code, and the new sentences. `backend-test` adds that Send refuses a code typed as a
  destination. `card-regtest` adds that Core refuses a spend signed without the card's label. Also read,
  with the new code: a real card 0.9.12 made on mainnet, which gives the same first three addresses the
  independent Python gives for it. Not shown: 0.9.12 itself reading a version 3 card or a version 4 backup
  (its refusals are what its code says, not something run here), and a device.

- **The card's address under its own prefix (2026-11-15).** The vectors were written again by
  `scripts/card-keys-vectors` with the new prefixes: only each case's `hrp` and `address` changed, and no
  key, tweak or output. `card-keys-test` adds that a reader of silent payment addresses refuses a card's
  address on either kind of network, and that the same keys under another prefix pay the same script.
  `multisig-test` adds that a backup naming the wallet's own keys as `tsp1…` is refused, and that a wallet
  file which holds them as `tsp1…` is read into the card's form while one with another network's prefix
  is damage. `records-test` adds the two sentences ("The card") and that a saved person whose card was
  written `tsp1…` is read into the card's form; the check that used to assert that a card's address pasted
  alone was "an ordinary silent payment address" now asserts its refusal. `backend-test` adds that Send
  refuses the card's address alone. A real file was also read: the people store that the simulator run
  below left on 2026-11-14, with Alice saved from a `tsp1…` card. The new code decoded it, validated it,
  and derived her next address; then the app itself, on that simulator, opened the wallet, refused a
  `twinnowcard1…` address typed into Send with the sentence, made a card whose text reads
  `"payTo":"twinnowcard1…`, and wrote the people store back with no `tsp1` in it. Not shown: a wallet file
  written by those builds that had issued a card (none was left to read; the rule is tested on a file
  rewritten in the old form), and a device.

- **The derivation.** `card-keys-test`: 350 checks, 0 failed, against `Lean/Vectors/card-keys-vectors.json`
  (4 cards, 18 payments in 0.9.12's form and 15 in the code's, output keys of both parities), which `scripts/card-keys-vectors` computes with the
  Python standard library and none of the wallet's code. Each script is also checked to be
  `SilentPaymentSending.outputScript`'s answer for the shared secret, and not what a standard silent
  payment to the same address pays. The recipient's key signs for every output; the person's tweak, the
  output's tweak and the spend key alone do not.
- **The wallet, without a node.** `multisig-test`: 845 checks, 0 failed, 128 of them in nine tests of cards.
  A payer that holds only a card's text pays three indices in one transaction; the two inside the window
  are credited and the one outside is not. A spend of card coins with an ordinary coin, and its fee bump,
  carry signatures that verify under BIP341's sighash for each coin's key. A fork takes a payment away and
  it is found again once. Backups round-trip; eighteen altered backups are refused. An address claimed
  without the phrase is watched and not signed for; a made-up tweak under the wallet's own address is
  watched and spent. A wallet that holds only its account key is refused a card. A wallet rebuilt from the
  phrase finds nothing, records the cards it could have issued, then finds and spends all three payments.
  The restore's search is begun, says without a key whether there is more to look for, is marked in the
  wallet's file and not in a backup, and ends; a wallet with only its account key, or none, begins none.
- **Regtest, Bitcoin Core 31.1 as the payer.** `card-regtest`: 25 checks, 0 failed. Core pays two indices;
  the wallet finds both through the basic filters Core serves. Core replaces a third payment before it
  confirms; it is credited once, under the replacement's txid. Its block is invalidated and the payment
  mined again; it is credited once in the block that then holds it. One transaction spending a card's
  coin is offered to Core five times: signed with the person's tweak, with the output's tweak, with the
  spend key alone, or with the spend key plus the output's tweak and no label, Core refuses it; signed
  with the spend key plus the card's label plus the output's tweak, Core takes it. A second wallet from the same phrase, its frontier already past every
  payment, finds none; after `restoreCards` and two passes of `scanRange` over the same filters it holds
  the same three coins and spends them in a transaction Core mines.
- **The app.** `records-test`: 1,605 checks, 0 failed: the people store (a card by name and by ID, the same
  card when asked again, the link through an iCloud restore plan, a card for another network or with a bad
  tweak refused in a sentence) and the card sheet through the app's own `perform` with a fake shell (no
  card for everybody is asked for, made or shown; making a card asks the device's owner once, declining
  makes none and says nothing, showing it again does not ask; a failure to make one lands on the sheet).
  `backend-test`: 369 checks, 0 failed, three runs. Its two-phone flow has Bob make a card for Alice, Alice
  pay it twice from her saved person at addresses Bob's account key does not derive in its first 200, and
  Bob's wallet find both, name both as Alice's and spend them. The journey `cardForOnePerson` passes
  headless with the other nine.
- **A phone restored from a backup made before its cards** (`backend-test`'s `cardRestoreFlow`, regtest).
  Bob backs up with his phrase, then makes 23 cards; Alice pays the 6th and the 23rd, and the node pays an
  ordinary address of Bob's in the same block. A new phone with only the old backup records 20 cards
  before it scans, finds the payment to the 6th in the scan forward, and then in two rounds of the search
  finds the payment to the 23rd in a block the scan had already passed. That block is applied twice and
  each payment is in the history once. The search ends once, with 43 cards recorded; the next card the
  phone makes is index 43; its backup is version 4; and it spends all three coins in a transaction the
  node mines. A backup without the phrase begins no search. Not shown: a search cut short and resumed, a
  range that must wait for a filter checkpoint (regtest's chain is shorter than one interval), or a
  restore from iCloud, which goes through the same import.
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
  That run was made while the card for everybody was still on the sheet; after it was retired the sheet
  was looked at once more in the simulator ("Make a card": the wallet's name and "A card for one person",
  nothing else), and the payment was not run again.
- **What these runs do not show:** a device, an unconfirmed payment, more than one peer, mainnet or signet,
  or two real phones exchanging a card by QR code, AirDrop or a message.

## Open

Decided on 2026-11-14, and done in this revision:

- **The shared card is retired.** The app no longer makes or shows it.
- **The app recovers cards** when it restores from a backup that carries the phrase ("Backup and
  recovery").

Decided, and left for now:

- **Receiving standard silent payments: yes, if we know how to find them.** With what Winnow has, we do
  not; the next section says why and what the ways are. It is left until there is a way that needs no
  server: Winnow will not name a tweak server to trust, and a notice from the payer for every payment is
  not wanted. Until then the wallet writes its address as `sp1…` nowhere: the wallet's file and a backup
  hold its two keys under the card's prefix, and a card holds neither key ("The card"), so there is none to
  copy out and pay.
- **A boring address for a payer who is not Winnow: yes.** An exchange or another wallet pays an ordinary
  address. Each person's card also shows one, taken from the card's own sequence ("An address any wallet
  can pay").

Still open:

1. **Showing an unconfirmed payment** made with a card.
2. **LeanNative capabilities**: a camera for QR codes, the Bluetooth peripheral role, NFC, and in which
   order.
3. **A per-payment request** with an amount and an expiry, for "pay exactly this, now".

## Finding a standard silent payment

A standard payment's output is `B_spend + hash(input_hash · a · B_scan ‖ k) · G`. To recognise it the
recipient needs, for that transaction, the sum of the public keys of its inputs. A compact filter does
not give that: it answers "does this block touch a script I already know", and the script is what the
recipient is trying to work out. Three ways are known, and Winnow has none of them today:

- **A full scan.** Every transaction with a Taproot output, with its inputs' public keys. A Taproot
  key-path input shows a signature and not its key, so the key comes from the output it spends, which a
  wallet that fetches only matched blocks does not have. This is a full node's work, not a phone's.
- **A tweak index.** A server computes one 33-byte value per eligible transaction and the wallet fetches
  them per block, then fetches the blocks its own outputs are in. BIP352's appendix describes it and
  there are servers that do it, but as of this writing it is not a peer-to-peer service: Bitcoin Core's
  own silent payment work was still in review, and the write-ups found call the light-client protocol a
  pre-draft. It is a server Winnow would have to name and trust not to leave a transaction out, and
  Winnow's sync today asks only Bitcoin peers. These points come from a web search on 2026-11-14 of
  secondary sources (linked under References), not from the specifications themselves.
- **A notice from the payer.** The payer sends the recipient the transaction's tweak, or its txid, out of
  band; the recipient derives the output and finds it by filter like any other script. BIP352's
  out-of-band notifications appendix is this. It needs a channel back to the recipient for every payment,
  where a card needs one hand-over. A coin found this way would be recorded the way a card's coin is: the
  tweak data and an index.

A card is the fourth way, and the one built: the two sides fix the tweak beforehand, so there is nothing
to find.

## References

- [BIP352](https://bips.dev/352/), including its out-of-band notifications appendix
- On finding standard silent payments from a light wallet, read 2026-11-14 and not checked against the
  specifications: [Silent Payments, Bitcoin Wiki](https://en.bitcoin.it/wiki/Silent_Payments);
  [a wallet-support comparison](https://www.spark.money/tools/bitcoin-silent-payment-wallet-comparison);
  [an article on the light-client scanning feed](https://cryptoslate.com/bitcoins-newest-mobile-privacy-feature-could-make-your-incoming-money-completely-invisible/);
  [Bitcoin Core #35301, "Silent Payments: Implement bip352 (take 2)"](https://mirror.b10c.me/bitcoin-bitcoin/35301/);
  [Bitcoin Core #27827, "Silent Payments: send and receive"](https://mirror.b10c.me/bitcoin-bitcoin/27827/)
- [BIP32](https://bips.dev/32/), [BIP340](https://bips.dev/340/),
  [BIP341](https://bips.dev/341/#constructing-and-spending-taproot-outputs)
- [BIP157](https://bips.dev/157/), [BIP158](https://bips.dev/158/)
- `Lean/Winnow/Keys/SilentPaymentPairing.lean`, `Lean/CardKeysTest.lean`, `scripts/card-keys-vectors`
