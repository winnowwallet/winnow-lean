import Winnow
import Lean.Data.Json
import TestKit.Check
import TestKit.Fixtures
import TestKit.Regtest

/-! `multisig-differential`: the Lean port of upstream's `winnow-fixture multisig-differential`
(Tools/Fixture/MultisigDifferential.swift, run by scripts/check-multisig-core at d2ca878): Winnow's Taproot
script-path multisig (`MultisigAccount`) held to Bitcoin Core on a disposable regtest node.

The node is TestKit.Regtest's without P2P (temp datadir, random ports, `bitcoind -regtest`), stopped at
the end, also on failure. Seeded cases vary the threshold, the number of signers (two to six), which
signers are Bitcoin Core wallets (keys Core generated, signing through `walletprocesspsbt` with its own
libsecp256k1), the order the signers are listed in, and the recovery leaf (none, fewer of the same signers,
or separate keys, after a delay). A third of the cases with three or more signers are nested (#256): some
signers are grouped into one member of two or three keys, signing with all of them (a phone and its Ledger)
or with a threshold of them (a 2-of-3 account that is one member), the threshold counts members, and the
account has a leaf per group of members and per way the group meets its thresholds; a recovery path of
fewer members is a timelocked leaf per group. For every case Core must agree with Winnow on:

* the descriptor checksum and the first four receive and change addresses, and that listing the members,
  their keys, or a recovery leaf's separate keys, in another order builds the same descriptor; the members
  Winnow reads back from a nested account's leaves;
* which keys of every leaf a PSBT carries valid signatures from, Core's included;
* every subset of exactly k members, each meeting its threshold exactly and signing in a shuffled order:
  Winnow finalizes, Core's mempool accepts it, and Core's own finalizer produces the same bytes; with k + 1
  members, or a member signing with more keys than it needs, both finish and Core accepts Winnow's
  witness; with k − 1, or a member one key short, neither finishes; one spend is mined;
* every recovery leaf, for delays of one to four blocks: its keys (every subset of its threshold when there
  is one leaf), refused by Core (`non-BIP68-final`) and by Winnow's unlock rule one block before the lock
  opens and accepted by both in the block it opens; one key fewer finishing on neither side unless the same
  people also complete a signers' leaf; a signers' leaf finishing a spend that carries the recovery
  sequence (BIP326); one recovery spend is mined.

The case generator draws from the same SplitMix64 sequence in the same order as the Swift one, so a seed
names the same case shapes (Core's keys differ per node). Differences: the signers' spend uses the
locktime-at-tip draw and the change goes last (Swift draws both at random); a disagreement is recorded with
seed and case and the run continues. Usage: `multisig-differential [--seed HEX] [--cases N]`. Exit 1 on any
disagreement. -/

open Winnow Keys Lean
open MultisigAccount (OutputCoordinate SpendPath RecoveryPlan)
open TestKit

/-! ## The tally -/

initialize agreed : IO.Ref (Array (String × Nat)) ← IO.mkRef #[]

/-- One comparison with Core, a check of its kind: the agreements counted by kind (printed at the end), a
disagreement a failure with its seed and case. -/
def tally (agrees : Bool) (kind : String) (detail : String) : IO Unit := do
  if agrees then
    agreed.modify fun a => match a.findIdx? (·.1 == kind) with
      | some j => a.modify j fun (k, n) => (k, n + 1)
      | none => a.push (kind, 1)
  check kind agrees detail

/-! ## The node -/

open TestKit.Regtest (Node startNode)

initialize nodeRef : IO.Ref (Option Node) ← IO.mkRef none

def node : IO Node := do
  let some n ← nodeRef.get | throw (IO.userError "no node")
  return n

def cli (args : Array String) (wallet : Option String := none) : IO String := do
  let n ← node
  match wallet with
  | some w => n.wallet args w
  | none => n.cli args

def cliJson (args : Array String) (wallet : Option String := none) : IO Json := do
  match Json.parse (← cli args wallet) with
  | .ok j => return j
  | .error e => throw (IO.userError s!"json {args}: {e}")

def jstr (j : Json) (k : String) : IO String := match j.getObjValAs? String k with
  | .ok s => pure s | .error e => throw (IO.userError s!"{k}: {e}")

def height : IO UInt32 := do return (← cli #["getblockcount"]).toNat!.toUInt32

def bank := "bank"

def ensureWallet (name : String) : IO Unit := do
  if ((← cli #["listwallets"]).splitOn s!"\"{name}\"").length > 1 then return
  if (← (cli #["loadwallet", name]).toBaseIO).toOption.isSome then return
  discard <| cli #["-named", "createwallet", s!"wallet_name={name}"]

def newAddress (wallet : String) : IO String := cli #["getnewaddress", "", "bech32m"] wallet

def mine (blocks : Nat) : IO Unit := do
  if blocks == 0 then return
  discard <| cli #["generatetoaddress", toString blocks, ← newAddress bank]

def mineTo (target : UInt32) : IO Unit := do
  let current ← height
  if target > current then mine (target - current).toNat

/-- A BTC amount (8 decimals) as exact sats. -/
def sats (j : Json) : IO Int64 := do
  let .num n := j | throw (IO.userError "amount")
  unless n.exponent ≤ 8 do throw (IO.userError "amount precision")
  return Int64.ofInt (n.mantissa * 10 ^ (8 - n.exponent))

def hexOf (s : String) : IO ByteArray := match Wire.dataOfHex? s with
  | some b => pure b | none => throw (IO.userError s!"hex {s}")

def mam {α} (what : String) (r : MAM α) : IO α := match r with
  | .ok a => pure a
  | .error e => throw (IO.userError s!"{what}: {e.name}{match e with | .account a => " (" ++ a.description ++ ")" | _ => ""}")

/-! ## Seeded randomness (`Tests/Support/SeededRandom.swift`, SplitMix64) -/

initialize rngState : IO.Ref UInt64 ← IO.mkRef 0

def next : IO UInt64 := do
  let s := (← rngState.get) + 0x9E37_79B9_7F4A_7C15
  rngState.set s
  let mut v := s
  v := (v ^^^ (v >>> 30)) * 0xBF58_476D_1CE4_E5B9
  v := (v ^^^ (v >>> 27)) * 0x94D0_49BB_1331_11EB
  return v ^^^ (v >>> 31)

/-- A draw in `0 ..< max(upperBound, 1)`. -/
def count (upperBound : Nat) : IO Nat := do return ((← next) % (max upperBound 1).toUInt64).toNat

/-- A draw inside `lo … hi`. -/
def drawInt (lo hi : Nat) : IO Nat := do return lo + ((← next) % (hi - lo + 1).toUInt64).toNat

def shuffle {α} (xs : Array α) : IO (Array α) := do
  let mut v := xs
  if v.size ≤ 1 then return v
  let mut i := v.size - 1
  while i > 0 do
    let j ← count (i + 1)
    v := v.swapIfInBounds i j
    i := i - 1
  return v

def combinations : List Nat → Nat → List (List Nat)
  | _, 0 => [[]]
  | [], _ + 1 => []
  | x :: rest, k + 1 => (combinations rest k).map (x :: ·) ++ combinations rest (k + 1)

/-! ## Signers -/

def hex8 (n : UInt32) : String := Descriptor.hex8 n

/-- A Bitcoin Core signer: a Core wallet's own tr() account key; Core signs with `walletprocesspsbt`. -/
structure CoreSigner where
  wallet : String
  /-- `[fp/86'/1'/0']tpub…`, without a suffix. -/
  publicExpression : String
  privateExpression : String
  deriving Inhabited

/-- The key expression inside Core's `tr(KEY/0/*)`, through Winnow's parser and serializer. -/
def coreKeyExpression (text : String) : IO String := do
  let d ← match Descriptor.parse text with
    | .ok d => pure d.serialized | .error e => throw (IO.userError s!"Core descriptor: {e.name}")
  let some open_ := d.toList.idxOf? '(' | throw (IO.userError "unparsable Core descriptor")
  let close := d.length - 1 - (d.toList.reverse.idxOf ')')
  let inner := String.ofList ((d.toList.drop (open_ + 1)).take (close - open_ - 1))
  unless inner.endsWith "/0/*" do throw (IO.userError "unexpected Core key path")
  return String.ofList (inner.toList.take (inner.length - 4))

def CoreSigner.make (wallet : String) : IO CoreSigner := do
  if (← (cli #["loadwallet", wallet]).toBaseIO).toOption.isNone then
    discard <| (cli #["-named", "createwallet", s!"wallet_name={wallet}"]).toBaseIO
  let descriptor (isPrivate : Bool) : IO String := do
    let listed ← cliJson #["listdescriptors", if isPrivate then "true" else "false"] wallet
    let entries ← match listed.getObjValAs? (Array Json) "descriptors" with
      | .ok a => pure a | .error e => throw (IO.userError e)
    let some entry := entries.find? fun e =>
        ((e.getObjValAs? String "desc").toOption.getD "").startsWith "tr(" &&
          !((e.getObjValAs? Bool "internal").toOption.getD false)
      | throw (IO.userError s!"no external tr() descriptor in {wallet}")
    jstr entry "desc"
  return { wallet, publicExpression := ← coreKeyExpression (← descriptor false),
           privateExpression := ← coreKeyExpression (← descriptor true) }

def CoreSigner.signerExpression (c : CoreSigner) : String := c.publicExpression ++ "/<0;1>/*"

/-- Imports the account with Core's own key private, so Core can sign as one of its signers. -/
def CoreSigner.importAccount (c : CoreSigner) (a : MultisigAccount) : IO Unit := do
  let text := (a.descriptor.serialized.splitOn "#")[0]!
  let privateText := text.replace c.publicExpression c.privateExpression
  if privateText == text then throw (IO.userError "Core key absent from the account")
  let checksum ← jstr (← cliJson #["getdescriptorinfo", privateText]) "checksum"
  let request := s!"[\{\"desc\":\"{privateText}#{checksum}\",\"timestamp\":\"now\",\"active\":true,\"range\":[0,5]}]"
  let imported ← cliJson #["importdescriptors", request] c.wallet
  let ok := match imported with
    | .arr xs => (xs[0]?.bind fun x => (x.getObjValAs? Bool "success").toOption) == some true
    | _ => false
  unless ok do throw (IO.userError s!"Core refused the account descriptor: {imported.compress}")

def CoreSigner.process (c : CoreSigner) (p : PSBT) : IO PSBT := do
  let b64 ← match p.base64V0 with | .ok s => pure s | .error e => throw (IO.userError e.name)
  let result ← cliJson #["walletprocesspsbt", b64, "true", "DEFAULT", "true", "false"] c.wallet
  let theirs ← match PSBT.ofBase64 (← jstr result "psbt") with
    | .ok q => pure q | .error e => throw (IO.userError e.name)
  mam "combine" (MultisigAccount.lift (·.name) (p.combined #[theirs]))

inductive Signer where
  | winnow (master : HDKey)
  | core (c : CoreSigner)
  deriving Inhabited

def Signer.expression : Signer → IO String
  | .winnow m => keyExpression m
  | .core c => pure c.signerExpression

def Signer.label : Signer → String | .core _ => "Core" | .winnow _ => "Winnow"

/-- The xpub inside a key expression `[origin]xpub/…`. -/
def extendedKeyIn (expression : String) : String :=
  let afterOrigin := (expression.splitOn "]").getLast!
  (afterOrigin.splitOn "/")[0]!

def Signer.accountKey (s : Signer) : IO String := return extendedKeyIn (← s.expression)

structure Case where
  number : Nat
  /-- Of the groups. -/
  threshold : Nat
  signers : Array Signer
  /-- The signers as the policy counts them, by position in `signers`: one each for an ordinary account; a
  nested account's members, some of two or three signers. -/
  groups : Array (Array Nat)
  /-- How many of each group's signers sign for it. -/
  thresholds : Array Nat
  recovery : Option RecoveryPlan
  recoveryMasters : Array HDKey

/-- Whether the account has a leaf per group of members: a threshold of every member, each signing with
every key, is one leaf of every key, the ordinary account. -/
def Case.isNested (c : Case) : Bool :=
  c.groups.any (·.size > 1) &&
    (c.threshold < c.groups.size || (Array.range c.groups.size).any fun g => c.thresholds[g]! < c.groups[g]!.size)

/-- The groups that are a threshold over their signers. -/
def Case.thresholdGroups (c : Case) : Array Nat :=
  (Array.range c.groups.size).filter fun g => c.thresholds[g]! < c.groups[g]!.size

def Case.members (c : Case) : IO (Array MultisigAccount.Member) :=
  (Array.range c.groups.size).mapM fun g => do
    let keys ← c.groups[g]!.mapM (c.signers[·]!.expression)
    let threshold : Nat := c.thresholds[g]!
    return { keys, threshold := (threshold : Int) }

def Case.summary (c : Case) : String :=
  let who := ",".intercalate ((Array.range c.groups.size).toList.map fun g =>
    let names := "+".intercalate (c.groups[g]!.toList.map (c.signers[·]!.label))
    if c.thresholds[g]! < c.groups[g]!.size then s!"{c.thresholds[g]!}of({names})" else names)
  let leaf := match c.recovery with
    | none => "no recovery"
    | some (.fewerSigners m b) => s!"recovery {m} of the members after {b}"
    | some (.separateKeys m ks b) => s!"recovery {m} of {ks.size} other keys after {b}"
  s!"{c.threshold}-of-{c.groups.size} [{who}], {leaf}"

def spendableDelay : UInt32 := 4

def randomMaster : IO HDKey := do
  let mut seed := ByteArray.empty
  for _ in [0:32] do seed := seed.push (← next).toUInt8
  match HDKey.ofSeed seed with | .ok k => pure k | .error e => throw (IO.userError e.name)

/-- Groups of one to three signers in shuffled order: the first of two or three, leaving at least one
signer for a second member. -/
def nestedGroups (n : Nat) : IO (Array (Array Nat)) := do
  let order ← shuffle (Array.range n)
  let mut groups : Array (Array Nat) := #[]
  let mut cursor := 0
  for _ in [0:n] do
    if cursor ≥ order.size then break
    let room := order.size - cursor
    let size ← if groups.isEmpty then pure (2 + (← count (min (room - 1) 3 - 1))) else pure (1 + (← count (min room 3)))
    groups := groups.push (order.extract cursor (cursor + size))
    cursor := cursor + size
  return groups

def generate (number : Nat) : IO Case := do
  let n := 2 + (← count 5)
  let coreCount := min (← count 3) n
  let mut signers : Array Signer := #[]
  for i in [0:coreCount] do signers := signers.push (.core (← CoreSigner.make s!"case{number}-core{i}"))
  for _ in [coreCount:n] do signers := signers.push (.winnow (← randomMaster))
  signers ← shuffle signers
  let nested ← if n ≥ 3 then pure ((← count 3) == 0) else pure false
  let groups ← if nested then nestedGroups n else pure ((Array.range n).map (#[·]))
  -- A group of two or three signs with all of them, or half the time with fewer: one of a pair, one or
  -- two of three.
  let thresholds ← groups.mapM fun g => do
    if g.size > 1 && (← count 2) == 0 then pure (1 + (← count (g.size - 1))) else pure g.size
  let mut threshold := 1 + (← count groups.size)
  -- One member alone may spend only when every member needs two keys.
  if nested && threshold == 1 && thresholds.any (· < 2) then threshold := 2
  let blocks : UInt32 ← do
    if (← count 10) < 7 then pure (1 + (← count spendableDelay.toNat)).toUInt32
    else pure (#[16, 144, 4_032, 65_535] : Array UInt32)[← count 4]!
  let mut recoveryMasters : Array HDKey := #[]
  let recovery ← match ← count 3 with
    | 0 => pure none
    | 1 => pure (some (RecoveryPlan.fewerSigners (1 + (← count groups.size)) blocks))
    | _ =>
      let k := 1 + (← count 3)
      for _ in [0:k] do recoveryMasters := recoveryMasters.push (← randomMaster)
      let keys ← recoveryMasters.mapM keyExpression
      pure (some (RecoveryPlan.separateKeys (1 + (← count recoveryMasters.size)) keys blocks))
  return { number, threshold, signers, groups, thresholds, recovery, recoveryMasters }

/-! ## Signing and finalizing -/

def signAs (p : PSBT) (s : Signer) (a : MultisigAccount) (coins : Array WalletUTXO) (owned : Array OutputCoordinate)
    (tip : UInt32) : IO PSBT := do
  match s with
  | .winnow m => mam "sign" (a.sign p m coins owned tip (← IO.getRandomBytes 32))
  | .core c => c.process p

/-- `psbt` signed by each of `subset`: each signer signs `psbt` alone once (kept in `copies` for the next
trial) and the copies are combined, as a coordinator combines partial PSBTs. One signature per signer per
spend, however many subsets try it. -/
def signedBy (psbt : PSBT) (subset : Array Nat) (sign : Nat → IO PSBT) (copies : IO.Ref (Array (Option PSBT))) :
    IO PSBT := do
  let mut parts := #[]
  for member in subset do
    let part ← match (← copies.get)[member]?.join with
      | some part => pure part
      | none => do
        let part ← sign member
        copies.modify (·.set! member (some part))
        pure part
    parts := parts.push part
  match psbt.combined parts with
  | .ok p => pure p
  | .error e => throw (IO.userError s!"combine: {e.name}")

/-- Both finalizers on the same signed PSBT: raw transactions in hex, `none` where a side does not complete. -/
def finalizeBoth (a : MultisigAccount) (p : PSBT) (coins : Array WalletUTXO) (owned : Array OutputCoordinate)
    (tip : UInt32) : IO (Option String × Option String) := do
  let ours := (a.finalizeSpend p coins owned tip).toOption.map fun (_, tx) => hex (tx.serialized true)
  let b64 ← match p.base64V0 with | .ok s => pure s | .error e => throw (IO.userError e.name)
  let result ← cliJson #["finalizepsbt", b64]
  let theirs := if (result.getObjValAs? Bool "complete").toOption == some true then
    (result.getObjValAs? String "hex").toOption else none
  return (ours, theirs)

def mempoolVerdict (txHex : String) : IO (Bool × String) := do
  let results ← cliJson #["testmempoolaccept", s!"[\"{txHex}\"]"]
  let first := match results with | .arr xs => xs[0]?.getD Json.null | _ => Json.null
  return ((first.getObjValAs? Bool "allowed").toOption == some true, (first.getObjValAs? String "reject-reason").toOption.getD "")

def broadcastAndMine (txHex label : String) : IO Unit := do
  let txid ← cli #["sendrawtransaction", txHex]
  mine 1
  let block ← cliJson #["getblock", ← cli #["getbestblockhash"], "1"]
  let mined := match block.getObjValAs? (Array String) "tx" with
    | .ok txs => txs.contains txid | .error _ => false
  tally mined "mined" s!"{label}: {txid} is not in the next block"

def newScript : IO ByteArray := do
  let info ← cliJson #["getaddressinfo", ← newAddress bank] bank
  hexOf (← jstr info "scriptPubKey")

def satsText (v : Nat) : String :=
  let frac := toString (v % 100_000_000)
  s!"{v / 100_000_000}.{String.ofList (List.replicate (8 - frac.length) '0')}{frac}"

/-- Pays each receive index of `a` from the bank, mines the payments, returns them as account coins. -/
def fund (a : MultisigAccount) (indices : Array UInt32) : IO (Array WalletUTXO) := do
  for index in indices do
    let amount := 80_000 + (← drawInt 0 120_000)
    discard <| cli #["-named", "sendtoaddress", s!"address={← mam "address" (a.address index)}",
      s!"amount={satsText amount}", "fee_rate=2"] bank
  mine 1
  let mut coins := #[]
  for index in indices do
    let script ← mam "spk" (a.scriptPubKey index)
    let result ← cliJson #["scantxoutset", "start", s!"[\"raw({hex script})\"]"]
    let unspents ← match result.getObjValAs? (Array Json) "unspents" with
      | .ok u => pure u | .error e => throw (IO.userError e)
    for u in unspents do
      let txid ← hexOf (← jstr u "txid")
      let amount ← sats ((u.getObjVal? "amount").toOption.getD Json.null)
      let vout := ((u.getObjValAs? Nat "vout").toOption.getD 0).toUInt32
      let h := ((u.getObjValAs? Nat "height").toOption.getD 0).toUInt32
      let coin : WalletUTXO := { txid := ByteArray.reverse txid, vout, amount, scriptPubKey := script,
                                 chain := .receive, index, height := h }
      coins := coins.push coin
  return coins

def sortedNat (xs : Array Nat) : Array Nat := (xs.toList.mergeSort (· ≤ ·)).toArray

/-- The positions in `keys` held by `signers`, those on the leaf only, ascending. -/
def positions (keys : Array Descriptor.SingleKey) (signers : Array Signer) : IO (Array Nat) := do
  let listed ← keys.mapM fun k => match k.base with
    | .extended x _ => pure (x.serialized .testnet) | _ => throw (IO.userError "a signer is not an xpub")
  let held ← signers.filterMapM fun s => do return listed.findIdx? (· == (← s.accountKey))
  return sortedNat (held.foldl (fun acc p => if acc.contains p then acc else acc.push p) #[])

/-- Who holds each key of the recovery leaf at `path`, in the leaf's order. -/
def recoveryHolders (a : MultisigAccount) (path : SpendPath) (c : Case) : IO (Array Signer) := do
  let holders : Array Signer := if c.recoveryMasters.isEmpty then c.signers else c.recoveryMasters.map .winnow
  let keys ← holders.mapM (·.accountKey)
  (a.keysOn path).mapM fun k => do
    let .extended x _ := k.base | throw (IO.userError "a recovery key is not an xpub")
    let some p := keys.findIdx? (· == x.serialized .testnet) | throw (IO.userError "a recovery key has no holder")
    return holders[p]!

/-- Whether some signers' leaf has its threshold of verified signatures. -/
def signersLeafCanFinish (a : MultisigAccount) (p : PSBT) (coins : Array WalletUTXO) : IO Bool :=
  a.signersPaths.anyM fun path => do
    return ((← mam "approvals" (a.approvals p coins path)).size : Int) ≥ a.thresholdOn path

/-! ## The checks -/

/-- The members Winnow reads back from the leaves it wrote: the threshold members by threshold and size,
and, unless every member is in every leaf, the member count and threshold. -/
def checkMembersReadBack (a : MultisigAccount) (c : Case) (tag : String) : IO Unit := do
  let some members := a.members
    | tally false "members read back" s!"{tag}: Winnow reads no members from {a.signersLeaves.size} leaves"
  let policies (ts : Array Nat) (sizes : Array Nat) (gs : Array Nat) : List String :=
    (gs.toList.map fun g => s!"{ts[g]!} of {sizes[g]!}").mergeSort (fun x y => decide (x ≤ y))
  let read := policies members.thresholds (members.groups.map (·.size)) members.thresholdGroups
  let built := policies c.thresholds (c.groups.map (·.size)) c.thresholdGroups
  tally (read == built) "members read back" s!"{tag}: Winnow reads threshold members {read}, built {built}"
  unless c.threshold < c.groups.size do return
  tally (members.threshold == c.threshold && members.groups.size == c.groups.size) "members read back"
    s!"{tag}: Winnow reads {members.threshold} of {members.groups.size}"
  if let (some recoveryMembers, some (.fewerSigners m _)) := (a.recoveryMembers, c.recovery) then
    tally (recoveryMembers.threshold == m.toNat && recoveryMembers.groups.size == c.groups.size) "recovery members read back"
      s!"{tag}: Winnow reads {recoveryMembers.threshold} of {recoveryMembers.groups.size} for recovery"

def checkAddresses (a : MultisigAccount) (c : Case) (members : Array MultisigAccount.Member) (tag : String) : IO Unit := do
  let text := a.descriptor.serialized
  let body := (text.splitOn "#")[0]!
  let coreChecksum ← jstr (← cliJson #["getdescriptorinfo", body]) "checksum"
  tally (coreChecksum == a.id) "descriptor checksum" s!"{tag}: Core {coreChecksum}, Winnow {a.id}"
  let derived ← cliJson #["deriveaddresses", text, "[0,3]"]
  let lists : Array (Array String) := match derived with
    | .arr xs => if xs.all (fun x => match x with | .arr _ => true | _ => false) then
        xs.map fun x => match x with | .arr ys => ys.filterMap (·.getStr?.toOption) | _ => #[]
      else #[xs.filterMap (·.getStr?.toOption)]
    | _ => #[]
  for choice in [0:2] do
    for index in [0:4] do
      let ours ← mam "address" (a.address index.toUInt32 choice)
      let theirs := ((lists[choice]?).bind (·[index]?)).getD "none"
      tally (ours == theirs) "address" s!"{tag} {choice}/{index}: Core {theirs}, Winnow {ours}"
  -- The builder writes keys in one canonical order, so listing the members, their keys, or a recovery
  -- leaf's separate keys in another order must give the very same descriptor, internal key included.
  let reversedRecovery := c.recovery.map fun
    | .separateKeys m ks b => .separateKeys m ks.reverse b
    | plan => plan
  let reordered ← mam "reordered" (MultisigAccount.makeNestedDescriptor
    (members.reverse.map fun m => { m with keys := m.keys.reverse }) c.threshold reversedRecovery .regtest)
  tally (reordered.serialized == text) "signer order"
    s!"{tag}: listing the keys in reverse gives {reordered.serialized}, not {a.id}"

/-- Signer subsets to try: every k members, each with exactly the keys it needs; k − 1 and k + 1 members; a
member one key short of its threshold among k; and a threshold member signing with every key. -/
def signerTrials (c : Case) : Array (Array Nat) := Id.run do
  let groups := c.groups
  let k := c.threshold
  let keys (g count : Nat) : Array Nat := groups[g]!.extract 0 count
  let meeting (chosen : Array Nat) : Array Nat := chosen.flatMap fun g => keys g c.thresholds[g]!
  let indices := Array.range groups.size
  let mut trials := ((combinations indices.toList k).map fun chosen => meeting chosen.toArray).toArray
  if k > 1 then trials := trials.push (meeting (indices.extract 0 (k - 1)))
  if k < groups.size then trials := trials.push (meeting (indices.extract 0 (k + 1)))
  if let some short := indices.find? (groups[·]!.size > 1) then
    let others := (indices.filter (· != short)).extract 0 (k - 1)
    trials := trials.push (keys short (c.thresholds[short]! - 1) ++ meeting others)
  if let some generous := c.thresholdGroups[0]? then
    let others := (indices.filter (· != generous)).extract 0 (k - 1)
    trials := trials.push (groups[generous]! ++ meeting others)
  return trials

def checkSignersPath (a : MultisigAccount) (c : Case) (tag : String) : IO Unit := do
  let coins ← fund a #[0, 1]
  let tip ← height
  let destination ← newScript
  let psbt ← mam "create" (a.createSpend coins #[{ amount := 60_000, scriptPubKey := destination }] 0 2 tip .signers (0.5, 0.5))
  let owned : Array OutputCoordinate := #[{ choice := 1, index := 0 }]
  let k := c.threshold
  let mut first : Option (String × String) := none
  let copies ← IO.mkRef (Array.replicate c.signers.size (none : Option PSBT))
  let mut sequential := true
  for trial in signerTrials c do
    let subset ← shuffle trial
    let label := s!"{tag} signers {subset.toList.map fun i => c.signers[i]!.label ++ toString i}"
    -- The first subset signs one after another, each on top of the signatures before it; the rest combine
    -- each signer's own copy.
    let signed ← if sequential then subset.foldlM (fun p m => signAs p c.signers[m]! a coins owned tip) psbt
      else signedBy psbt subset (fun m => signAs psbt c.signers[m]! a coins owned tip) copies
    sequential := false
    -- Every leaf must verify exactly the subset's keys that sit on it.
    for path in a.signersPaths do
      let approved ← mam "approvals" (a.approvals signed coins path)
      let expected ← positions (a.keysOn path) (subset.map (c.signers[·]!))
      tally (approved == expected) "verified signers" s!"{label} {path}: Winnow verifies {approved}, signed by {expected}"
    -- Members that met their threshold, and whether exactly k did with exactly the keys they need, so that
    -- one leaf can finish.
    let held (g : Nat) := (c.groups[g]!.filter subset.contains).size
    let met := (Array.range c.groups.size).filter fun g => held g ≥ c.thresholds[g]!
    let exact := met.size == k && met.all fun g => held g == c.thresholds[g]!
    let (ours, theirs) ← finalizeBoth a signed coins owned tip
    if met.size < k then
      tally (ours.isNone && theirs.isNone) "below threshold refused"
        s!"{label}: Winnow finished {ours.isSome}, Core finished {theirs.isSome}"
      continue
    let some ours := ours | tally false "threshold finalizes" s!"{label}: Winnow refused {k} complete groups"; continue
    tally theirs.isSome "threshold finalizes" s!"{label}: Core's finalizer did not complete"
    -- With exactly k members each meeting its threshold exactly, one leaf can finish, so the finalizers
    -- must produce the same witness; with more, each may pick a leaf.
    if exact then
      if let some t := theirs then tally (ours == t) "finalizers agree" s!"{label}: Winnow {ours}, Core {t}"
    let (allowed, reason) ← mempoolVerdict ours
    tally allowed "Core accepts" s!"{label}: {reason}"
    if allowed && first.isNone then first := some (label, ours)
  -- Mined only after every subset was tried against the unspent coins.
  if let some (label, txHex) := first then broadcastAndMine txHex label

def checkRecoveryPath (a : MultisigAccount) (c : Case) (tag : String) : IO Unit := do
  let some recovery := a.recovery | return
  let coin := (← fund a #[2])[0]!
  let unlock := coin.height + recovery.blocks
  let openTip := unlock - 1
  let destination ← newScript
  -- Core's 50-block anti-fee-sniping lookback, so only BIP68 can refuse the spend a block early.
  let psbt ← mam "create recovery" (a.createSpend #[coin] #[{ amount := 40_000, scriptPubKey := destination }] 1 2 openTip
    .recovery (0, 0.5))
  let owned : Array OutputCoordinate := #[{ choice := 1, index := 1 }]
  let mut ready : Array (String × String) := #[]
  for path in a.recoveryPaths do
    let holders ← recoveryHolders a path c
    let m := (a.thresholdOn path).toNat
    let all := List.range holders.size
    -- One recovery leaf: every subset of its threshold; a leaf per group of members: each leaf's keys. One
    -- key fewer on the first.
    let mut trials := if a.recoveryPaths.size == 1 then ((combinations all m).map List.toArray).toArray else #[all.toArray]
    if m > 1 && path == .recovery then trials := trials.push (all.take (m - 1)).toArray
    let copies ← IO.mkRef (Array.replicate holders.size (none : Option PSBT))
    let mut sequential := true
    for trial in trials do
      let subset ← shuffle trial
      let label := s!"{tag} {path} keys {subset}"
      -- As on the signers' path: the first subset signs in turn, the rest combine each holder's copy.
      let signed ← if sequential then subset.foldlM (fun p m => signAs p holders[m]! a #[coin] owned openTip) psbt
        else signedBy psbt subset (fun m => signAs psbt holders[m]! a #[coin] owned openTip) copies
      sequential := false
      let approved ← mam "approvals" (a.approvals signed #[coin] path)
      tally (approved == sortedNat subset) "verified recovery signers"
        s!"{label}: Winnow verifies {approved}, signed by {sortedNat subset}"
      let (ours, theirs) ← finalizeBoth a signed #[coin] owned openTip
      -- A signer reused for recovery signs both leaves, so when its signatures meet a signers' threshold
      -- that leaf can finish.
      let signersCanFinish ← signersLeafCanFinish a signed #[coin]
      if subset.size < m then
        tally (ours.isSome == signersCanFinish && theirs.isSome == signersCanFinish) "below recovery threshold"
          s!"{label}: Winnow finished {ours.isSome}, Core finished {theirs.isSome}, signers' leaf complete {signersCanFinish}"
        continue
      let some ours := ours | tally false "recovery finalizes" s!"{label}: Winnow refused {m} recovery signatures"; continue
      tally theirs.isSome "recovery finalizes" s!"{label}: Core's finalizer did not complete"
      -- When a signers' leaf can finish too, each finalizer may pick either leaf, so only a recovery-only
      -- spend must match byte for byte.
      if let some t := theirs then
        if !signersCanFinish then tally (ours == t) "recovery finalizers agree" s!"{label}: Winnow {ours}, Core {t}"
      ready := ready.push (label, ours)
  -- BIP326: a signers' leaf may finish a spend that carries the recovery sequence.
  let mut bySigners := psbt
  for member in (c.groups.extract 0 c.threshold).flatten do
    bySigners ← signAs bySigners c.signers[member]! a #[coin] owned openTip
  match (← finalizeBoth a bySigners #[coin] owned openTip).1 with
  | some ours => ready := ready.push (s!"{tag} signers' leaf with the recovery sequence", ours)
  | none => tally false "signers' leaf under the recovery sequence" s!"{tag}: Winnow refused it"
  -- One block before the lock opens: Core and Winnow both refuse.
  if openTip ≥ 1 && openTip - 1 ≥ (← height) then
    mineTo (openTip - 1)
    tally (!a.isUnlockedForRecovery coin (openTip - 1)) "locked a block early"
      s!"{tag}: Winnow calls the coin unlocked at tip {openTip - 1}, coin at {coin.height}"
    for (label, txHex) in ready do
      let (allowed, reason) ← mempoolVerdict txHex
      tally (!allowed && (reason.splitOn "non-BIP68-final").length > 1) "Core refuses a block early"
        s!"{label}: allowed {allowed} {reason}"
  -- The block the lock opens in: both accept.
  mineTo openTip
  tally (a.isUnlockedForRecovery coin openTip) "unlocked on time"
    s!"{tag}: Winnow calls the coin locked at tip {openTip}, coin at {coin.height}"
  tally (a.recoveryUnlockHeight coin == some unlock) "unlock height"
    s!"{tag}: Winnow {a.recoveryUnlockHeight coin}, expected {unlock}"
  for (label, txHex) in ready do
    let (allowed, reason) ← mempoolVerdict txHex
    tally allowed "Core accepts on time" s!"{label}: {reason}"
  if let some (label, txHex) := ready[0]? then
    if (← mempoolVerdict txHex).1 then broadcastAndMine txHex label

def checkCase (c : Case) (tag : String) : IO Unit := do
  let members ← c.members
  let d ← mam "descriptor" (MultisigAccount.makeNestedDescriptor members c.threshold c.recovery .regtest)
  let a ← mam "account" (MultisigAccount.make d .regtest)
  tally (a.isNested == c.isNested) "nesting" s!"{tag}: Winnow built {a.signersLeaves.size} signers' leaves"
  if c.isNested then checkMembersReadBack a c tag
  checkAddresses a c members tag
  for s in c.signers do
    if let .core core := s then core.importAccount a
  checkSignersPath a c tag
  if let some r := a.recovery then
    if r.blocks ≤ spendableDelay then checkRecoveryPath a c tag

def parseHex64 (s : String) : Option UInt64 :=
  s.toList.foldlM (fun acc ch =>
    let d := if '0' ≤ ch && ch ≤ '9' then some (ch.toNat - 48)
      else if 'a' ≤ ch && ch ≤ 'f' then some (ch.toNat - 87)
      else if 'A' ≤ ch && ch ≤ 'F' then some (ch.toNat - 55) else none
    d.map fun d => acc * 16 + d.toUInt64) 0

def main (args : List String) : IO UInt32 := do
  let mut seed : UInt64 := 0x5441_5052_4F4F_5453
  let mut cases := 24
  let mut rest := args
  while !rest.isEmpty do
    match rest with
    | "--seed" :: v :: r => seed := (parseHex64 v).getD seed; rest := r
    | "--cases" :: v :: r => cases := v.toNat!; rest := r
    | x :: _ => IO.eprintln s!"unknown argument {x}"; return 2
    | [] => pure ()
  runMain "multisig-differential" do
    let dir := s!"/tmp/winnow-multisig-core-{← IO.monoNanosNow}"
    IO.FS.createDirAll dir
    let n ← startNode dir (filters := false)
    nodeRef.set (some n)
    try
      let chain ← jstr (← cliJson #["getblockchaininfo"]) "chain"
      unless chain == "regtest" do throw (IO.userError s!"the node reports {chain}")
      ensureWallet bank
      mine 110
      for number in [0:cases] do
        rngState.set (seed + number.toUInt64 * 0x9E37_79B9)
        let tag := s!"seed {String.ofList (Nat.toDigits 16 seed.toNat)} case {number}"
        let start ← IO.monoMsNow
        try
          let c ← generate number
          say s!"case {number}: {c.summary}"
          checkCase c tag
        catch e => tally false "case completed" s!"{tag}: {e}"
        say s!"  ({(← IO.monoMsNow) - start} ms)"
    finally
      n.stop
      discard <| IO.Process.output { cmd := "rm", args := #["-rf", dir] }
    for (kind, k) in ← agreed.get do say s!"  {kind}: {k}"
