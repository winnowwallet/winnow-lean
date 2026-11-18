import Winnow.Wallet.MultisigAccount
import Winnow.Wallet.SignerRecord

/-! # Accounts and signers that follow a person between devices: the rules

Every device's iCloud backup already lists its multisig accounts and its signers (`ImportBundle.vaults`,
`ImportBundle.signers`). A device keeps in step with the person's others by reading their backups and taking
what they have that it lacks; its own next backup then carries the result. This file is the rules alone, with
no file, clock or network in it: what one device does with what it reads.

Each thing that can change carries a `Stamp`: when it changed and on which device. A device never writes a
stamp behind one it has seen (`Stamp.after`), so "later" survives two clocks that disagree.

* **Being there.** An account or signer has the stamp it was last added with and the stamp it was last removed
  with; it is there while the removal is not the later one. Both only grow (`Stamp.max`), so devices that have
  read each other agree. A removal that reaches a device which still sees coins or a payment in the account
  is not followed there: that device adds the account again, later than the removal, and the others take it
  back (`Existence.reassert`).
* **A name, a Ledger's registration.** The later change wins.
* **Address counters.** The highest: two devices never hand out one address.
* **A payment awaiting signatures.** The later change wins, a discard included; two copies of the same
  payment are combined, so signatures made on two devices add up.

A backup written before this existed carries no stamps (`Replica.sync` is none): its accounts and signers are
taken as added at the beginning of time, so a removal made since beats them, and its names and drafts never
replace a device's own.

What a device has done with what it read is its `AccountSeen` and `SignerSeen` (the stamps, and the values
they were written for): a value that differs from the one seen was changed on this device, and gets a stamp
then (`stampAccount`, `stampSigner`). Removals are the exception: only the app's own Remove writes one, never
an absence found by comparing, so a wallet replaced or a file set aside removes nothing anywhere. -/

namespace Winnow.DeviceSync
open SwiftJSON

/-! ## Stamps -/

/-- When something changed (milliseconds since 1970, never behind a stamp the device had seen) and on which
device (a random number the device drew once). The beginning of time is `{}`. -/
structure Stamp where
  time : Nat := 0
  device : Nat := 0
  deriving DecidableEq, Inhabited

/-- Printed as `time@device`. By hand, as is the JSON key `deviceID` below: a derived `Repr` and a key
named for the field would each put the field's name in the app's C as a string, and the iOS build reads
that string as a call to the shell's capability of the same name. -/
instance : Repr Stamp := ⟨fun s _ => .text s!"{s.time}@{s.device}"⟩

namespace Stamp

instance : LT Stamp := ⟨fun a b => a.time < b.time ∨ (a.time = b.time ∧ a.device < b.device)⟩

instance (a b : Stamp) : Decidable (a < b) :=
  inferInstanceAs (Decidable (a.time < b.time ∨ (a.time = b.time ∧ a.device < b.device)))

/-- The later of two. -/
def max (a b : Stamp) : Stamp := if a < b then b else a

theorem lt_def (a b : Stamp) : a < b ↔ a.time < b.time ∨ (a.time = b.time ∧ a.device < b.device) := Iff.rfl

theorem max_idem (a : Stamp) : max a a = a := by
  simp [max]

theorem max_comm (a b : Stamp) : max a b = max b a := by
  obtain ⟨at_, ad⟩ := a
  obtain ⟨bt, bd⟩ := b
  simp only [max, lt_def]
  split <;> split <;> first | rfl | (simp only [Stamp.mk.injEq]; omega)

theorem max_assoc (a b c : Stamp) : max (max a b) c = max a (max b c) := by
  obtain ⟨at_, ad⟩ := a
  obtain ⟨bt, bd⟩ := b
  obtain ⟨ct, cd⟩ := c
  by_cases h1 : at_ < bt ∨ (at_ = bt ∧ ad < bd) <;> by_cases h2 : bt < ct ∨ (bt = ct ∧ bd < cd) <;>
    by_cases h3 : at_ < ct ∨ (at_ = ct ∧ ad < cd) <;> simp [max, lt_def, h1, h2, h3] <;> omega

/-- A stamp for a change made now on `device`, later than every stamp up to `clock`. -/
def after (clock now device : Nat) : Stamp := { time := Nat.max now (clock + 1), device }

theorem after_later (clock now device : Nat) (s : Stamp) (h : s.time ≤ clock) : s < after clock now device := by
  simp only [lt_def, after]
  left
  have : clock + 1 ≤ Nat.max now (clock + 1) := Nat.le_max_right _ _
  omega

def toJV (s : Stamp) : JV := .arr #[ofInt s.time, ofInt s.device]

/-- Two whole numbers a `Double` holds exactly. -/
def ofJV (v : JV) : D Stamp := do
  match ← asArray (intIn 0 (2 ^ 53)) v with
  | #[t, d] => return { time := t.toNat, device := d.toNat }
  | _ => dataCorrupted

end Stamp

/-! ## What a backup says of when things changed -/

/-- The stamps of one account, by its id (the descriptor's checksum). -/
structure AccountMeta where
  id : String
  added : Stamp := {}
  removed : Stamp := {}
  name : Stamp := {}
  ledger : Stamp := {}
  draft : Stamp := {}
  deriving DecidableEq, Inhabited, Repr

/-- Removed later than it was added. -/
def AccountMeta.isRemoved (m : AccountMeta) : Bool := m.added < m.removed

/-- The stamps of one signer, by its keys (`signerKey`). -/
structure SignerMeta where
  key : String
  added : Stamp := {}
  removed : Stamp := {}
  name : Stamp := {}
  deriving DecidableEq, Inhabited, Repr

def SignerMeta.isRemoved (m : SignerMeta) : Bool := m.added < m.removed

/-- What a backup carries beside its accounts and signers (`CloudAppState.sync`): which device wrote it, and
the stamps of everything it has or has removed. -/
structure SyncMeta where
  version : Int := 1
  device : Nat
  accounts : Array AccountMeta := #[]
  signers : Array SignerMeta := #[]
  deriving DecidableEq, Inhabited

/-- By hand, for the reason `Stamp`'s is. -/
instance : Repr SyncMeta := ⟨fun m _ =>
  .text s!"version {m.version}, from {m.device}, accounts {reprStr m.accounts}, signers {reprStr m.signers}"⟩

/-- A backup remembers at most this many accounts, and this many signers, present or removed. -/
def maximumEntries : Nat := 1_000

namespace AccountMeta

private def stampIfSet (s : Stamp) : Option JV := if s = {} then none else some s.toJV

def toJV (m : AccountMeta) : JV :=
  obj [("id", some (.str m.id)), ("added", stampIfSet m.added), ("removed", stampIfSet m.removed),
       ("name", stampIfSet m.name), ("ledger", stampIfSet m.ledger), ("draft", stampIfSet m.draft)]

def ofJV (v : JV) : D AccountMeta := do
  let kvs ← asObject v
  let stamp (k : String) : D Stamp := do return (← keyIfPresent kvs k Stamp.ofJV).getD {}
  return { id := ← key kvs "id" asString, added := ← stamp "added", removed := ← stamp "removed", name := ← stamp "name",
           ledger := ← stamp "ledger", draft := ← stamp "draft" }

end AccountMeta

namespace SignerMeta

def toJV (m : SignerMeta) : JV :=
  let stampIfSet (s : Stamp) : Option JV := if s = {} then none else some s.toJV
  obj [("key", some (.str m.key)), ("added", stampIfSet m.added), ("removed", stampIfSet m.removed),
       ("name", stampIfSet m.name)]

def ofJV (v : JV) : D SignerMeta := do
  let kvs ← asObject v
  let stamp (k : String) : D Stamp := do return (← keyIfPresent kvs k Stamp.ofJV).getD {}
  return { key := ← SwiftJSON.key kvs "key" asString, added := ← stamp "added", removed := ← stamp "removed", name := ← stamp "name" }

end SignerMeta

namespace SyncMeta

def toJV (m : SyncMeta) : JV :=
  obj [("version", some (ofInt m.version)), ("deviceID", some (ofInt m.device)),
       ("accounts", some (.arr (m.accounts.map AccountMeta.toJV))), ("signers", some (.arr (m.signers.map SignerMeta.toJV)))]

/-- Bounded: a version this build reads, and at most `maximumEntries` of each. -/
def ofJV (v : JV) : D SyncMeta := do
  let kvs ← asObject v
  let version ← key kvs "version" asInt
  unless version == 1 do dataCorrupted
  let device := (← key kvs "deviceID" (intIn 0 (2 ^ 53))).toNat
  let accounts ← key kvs "accounts" (asArray AccountMeta.ofJV)
  let signers ← key kvs "signers" (asArray SignerMeta.ofJV)
  unless accounts.size ≤ maximumEntries && signers.size ≤ maximumEntries do dataCorrupted
  return { version, device, accounts, signers }

def account? (m : SyncMeta) (id : String) : Option AccountMeta := m.accounts.find? (·.id == id)
def signer? (m : SyncMeta) (key : String) : Option SignerMeta := m.signers.find? (·.key == key)

/-- The latest time any of its stamps carries. -/
def latest (m : SyncMeta) : Nat :=
  let a := m.accounts.foldl (fun t x => [x.added, x.removed, x.name, x.ledger, x.draft].foldl (fun t s => Nat.max t s.time) t) 0
  m.signers.foldl (fun t x => [x.added, x.removed, x.name].foldl (fun t s => Nat.max t s.time) t) a

end SyncMeta

/-! ## What a device has seen -/

/-- A registration as one line, to tell a changed one from the one seen ("" for none). -/
def ledgerMark (l : Option LedgerRegistration) : String :=
  match l with
  | none => ""
  | some l => s!"{hex l.policyID}:{hex l.hmac}:{l.masterFingerprint}"

/-- A draft as one line, to tell a changed one from the one seen ("" for none). -/
def draftMark (d : Option MultisigSpendDraft) : String :=
  match d with
  | none => ""
  | some d => hex (sha256 d.psbtBase64.toUTF8)

/-- An account's stamps on this device, and the values they were written for. -/
structure AccountSeen where
  stamps : AccountMeta
  name : String := ""
  ledger : String := ""
  draft : String := ""
  deriving DecidableEq, Inhabited, Repr

/-- A signer's stamps on this device, and the name they were written for. -/
structure SignerSeen where
  stamps : SignerMeta
  name : String := ""
  deriving DecidableEq, Inhabited, Repr

namespace AccountSeen

def toJV (s : AccountSeen) : JV :=
  obj [("stamps", some s.stamps.toJV), ("name", some (.str s.name)), ("ledger", some (.str s.ledger)), ("draft", some (.str s.draft))]

def ofJV (v : JV) : D AccountSeen := do
  let kvs ← asObject v
  return { stamps := ← key kvs "stamps" AccountMeta.ofJV, name := ← key kvs "name" asString, ledger := ← key kvs "ledger" asString,
           draft := ← key kvs "draft" asString }

end AccountSeen

namespace SignerSeen

def toJV (s : SignerSeen) : JV := obj [("stamps", some s.stamps.toJV), ("name", some (.str s.name))]

def ofJV (v : JV) : D SignerSeen := do
  let kvs ← asObject v
  return { stamps := ← key kvs "stamps" SignerMeta.ofJV, name := ← key kvs "name" asString }

end SignerSeen

/-- The stamps of an account this device has, after whatever the person did to it since it was last looked at.
`fresh` is a stamp for now. `initial`: nothing has been looked at before (the first run of a build that keeps
in step), when an account is as old as time rather than new, so that a removal already made on another
device still removes it; a draft or a registration it has is stamped all the same, since those should
travel. -/
def stampAccount (fresh : Stamp) (initial : Bool) (seen : Option AccountSeen) (r : MultisigAccountRecord) : AccountSeen :=
  let ledger := ledgerMark r.ledger
  let draft := draftMark r.draft
  match seen with
  | none =>
    let stampIf (present : Bool) : Stamp := if present then fresh else {}
    let base : AccountMeta := if initial then { id := r.id } else { id := r.id, added := fresh, name := fresh }
    { stamps := { base with ledger := stampIf r.ledger.isSome, draft := stampIf r.draft.isSome }, name := r.name, ledger, draft }
  | some s =>
    let m := s.stamps
    -- removed, and here again: the person joined it again
    let m := if m.isRemoved then { m with added := fresh } else m
    let m := if r.name != s.name then { m with name := fresh } else m
    let m := if ledger != s.ledger then { m with ledger := fresh } else m
    let m := if draft != s.draft then { m with draft := fresh } else m
    { stamps := m, name := r.name, ledger, draft }

/-- `stampAccount` for a signer. -/
def stampSigner (fresh : Stamp) (initial : Bool) (seen : Option SignerSeen) (key : String) (r : SignerRecord) : SignerSeen :=
  match seen with
  | none => { stamps := if initial then { key } else { key, added := fresh, name := fresh }, name := r.name }
  | some s =>
    let m := s.stamps
    let m := if m.isRemoved then { m with added := fresh } else m
    let m := if r.name != s.name then { m with name := fresh } else m
    { stamps := m, name := r.name }

/-! ## Another device's backup, and this device -/

/-- What another device's backup says. -/
structure Replica where
  /-- The backup's id. -/
  id : String
  /-- The block its accounts' coins and history are current to (`ImportBundle.lastKnownHeight`). -/
  height : UInt32
  accounts : Array MultisigAccountRecord := #[]
  /-- Each signer under its key (`signerKey`). -/
  signers : Array (String × SignerRecord) := #[]
  /-- None for a backup written before devices kept in step. -/
  sync : Option SyncMeta := none
  deriving Inhabited

namespace Replica

def accountMeta (r : Replica) (id : String) : AccountMeta := ((r.sync.bind (·.account? id))).getD { id }
def signerMeta (r : Replica) (key : String) : SignerMeta := ((r.sync.bind (·.signer? key))).getD { key }
def account? (r : Replica) (id : String) : Option MultisigAccountRecord := r.accounts.find? (·.id == id)
def signer? (r : Replica) (key : String) : Option SignerRecord := (r.signers.find? (·.1 == key)).map (·.2)

end Replica

/-- An account this device has. -/
structure LocalAccount where
  record : MultisigAccountRecord
  seen : AccountSeen
  /-- Every coin spent in a block, no payment awaiting signatures and none in flight: what the app's own
  Remove asks before it removes. -/
  removable : Bool
  deriving Inhabited

/-- A signer this device has. -/
structure LocalSigner where
  key : String
  record : SignerRecord
  seen : SignerSeen
  deriving Inhabited

/-- What becomes of an account's being here. -/
inductive Existence where
  | unchanged
  /-- Not here, there on another device: take that device's record, current to `height`, with the stamps its
  name and its Ledger's registration were given. -/
  | adopt (record : MultisigAccountRecord) (height : UInt32) (name ledger : Stamp)
  /-- Here, and removed on another device since it was added. -/
  | remove
  /-- Here, removed on another device, and this device still sees coins or a payment in it: it stays, added
  again later than the removal. -/
  | reassert
  deriving Inhabited

/-- One thing another device has later than this one. Applying it gives the account that stamp. -/
inductive Change where
  | rename (name : String) (stamp : Stamp)
  /-- Address counters never go back. -/
  | raise (receive change : UInt32)
  | ledger (registration : LedgerRegistration) (stamp : Stamp)
  /-- The payment awaiting signatures replaced, or (none) discarded. -/
  | draft (value : Option MultisigSpendDraft) (stamp : Stamp)
  /-- Other copies of the same payment, whose signatures join this device's. -/
  | combine (others : Array MultisigSpendDraft) (stamp : Stamp)
  deriving Inhabited

/-- What a device does about one account. -/
structure AccountDecision where
  id : String
  /-- The stamps of its being here, as now known (the later of this device's and every backup's). -/
  added : Stamp
  removed : Stamp
  existence : Existence := .unchanged
  changes : Array Change := #[]
  deriving Inhabited

def AccountDecision.isQuiet (d : AccountDecision) (known : Option AccountMeta) : Bool :=
  (d.existence matches .unchanged) && d.changes.isEmpty &&
    (match known with | some m => m.added = d.added ∧ m.removed = d.removed | none => d.added = {} ∧ d.removed = {})

private def latest {α} (stamp : α → Stamp) (xs : Array α) : Option α :=
  xs.foldl (fun best x => match best with
    | none => some x
    | some b => if stamp b < stamp x then some x else some b) none

/-- The decision for one account: `here` is this device's, `known` the stamps it remembers of one it does not
have (a removal), `fresh` a stamp for now, `txidOf` a draft's payment. -/
def decideAccount (fresh : Stamp) (txidOf : MultisigSpendDraft → Option ByteArray) (id : String)
    (here : Option LocalAccount) (known : Option AccountMeta) (replicas : Array Replica) : AccountDecision :=
  let mine : AccountMeta := match here with
    | some l => l.seen.stamps
    | none => known.getD { id }
  let added := replicas.foldl (fun s r => Stamp.max s (r.accountMeta id).added) mine.added
  let removed := replicas.foldl (fun s r => Stamp.max s (r.accountMeta id).removed) mine.removed
  -- the backups that have the account, each with its record and stamps
  let holders : Array (Replica × MultisigAccountRecord × AccountMeta) :=
    replicas.filterMap fun r => (r.account? id).map fun record => (r, record, r.accountMeta id)
  let named := latest (fun (h : Replica × MultisigAccountRecord × AccountMeta) => h.2.2.name) holders
  let registered := latest (fun (h : Replica × MultisigAccountRecord × AccountMeta) => h.2.2.ledger)
    (holders.filter (·.2.1.ledger.isSome))
  let receive := holders.foldl (fun n h => Max.max n h.2.1.nextReceiveIndex) 0
  let change := holders.foldl (fun n h => Max.max n h.2.1.nextChangeIndex) 0
  match here with
  | none =>
    if added < removed then { id, added, removed } else
    match latest (fun (h : Replica × MultisigAccountRecord × AccountMeta) => ({ time := h.1.height.toNat } : Stamp)) holders with
    | none => { id, added, removed }
    | some (replica, record, _) =>
      -- the payment awaiting signatures comes afterwards, once this device sees the coins it spends
      let record := { record with draft := none, nextReceiveIndex := Max.max record.nextReceiveIndex receive,
                                  nextChangeIndex := Max.max record.nextChangeIndex change }
      let record := match named with | some (_, r, _) => { record with name := r.name } | none => record
      let record := match registered with | some (_, r, _) => { record with ledger := r.ledger } | none => record
      { id, added, removed, existence := .adopt record replica.height ((named.map (·.2.2.name)).getD {})
                                             ((registered.map (·.2.2.ledger)).getD {}) }
  | some l =>
    if added < removed then
      if l.removable then { id, added, removed, existence := .remove }
      else { id, added := fresh, removed, existence := .reassert }
    else Id.run do
      let mut changes : Array Change := #[]
      if let some (_, r, m) := named then
        if mine.name < m.name then changes := changes.push (.rename r.name m.name)
      if receive > l.record.nextReceiveIndex || change > l.record.nextChangeIndex then
        changes := changes.push (.raise (Max.max receive l.record.nextReceiveIndex) (Max.max change l.record.nextChangeIndex))
      if let some (_, r, m) := registered then
        if let some registration := r.ledger then
          if mine.ledger < m.ledger then changes := changes.push (.ledger registration m.ledger)
      -- the same payment on another device: its signatures join ours, whichever copy is later
      let payment := l.record.draft.bind txidOf
      let same : Array (MultisigSpendDraft × Stamp) := holders.filterMap fun (_, r, m) =>
        match r.draft with
        | some d => if payment.isSome && txidOf d == payment && some d != l.record.draft then some (d, m.draft) else none
        | none => none
      let newest := latest (fun (h : Replica × MultisigAccountRecord × AccountMeta) => h.2.2.draft) holders
      let replaced := match newest with
        | some (_, r, m) =>
          let samePayment := payment.isSome && (r.draft.bind txidOf) == payment
          if mine.draft < m.draft && !samePayment then some (r.draft, m.draft) else none
        | none => none
      match replaced with
      | some (value, stamp) => changes := changes.push (.draft value stamp)
      | none =>
        unless same.isEmpty do
          changes := changes.push (.combine (same.map (·.1)) (same.foldl (fun s x => Stamp.max s x.2) mine.draft))
      return { id, added, removed, changes }

/-- Every account this device, what it remembers or any backup names, each decided. -/
def decideAccounts (fresh : Stamp) (txidOf : MultisigSpendDraft → Option ByteArray) (here : Array LocalAccount)
    (known : Array AccountMeta) (replicas : Array Replica) : Array AccountDecision := Id.run do
  let mut ids : Array String := here.map (·.record.id)
  let add (ids : Array String) (id : String) : Array String := if ids.contains id then ids else ids.push id
  for m in known do ids := add ids m.id
  for r in replicas do
    for a in r.accounts do ids := add ids a.id
    if let some s := r.sync then
      for m in s.accounts do ids := add ids m.id
  return ids.map fun id =>
    decideAccount fresh txidOf id (here.find? (·.record.id == id)) (known.find? (·.id == id)) replicas

/-- What becomes of a signer's being here. -/
inductive SignerExistence where
  | unchanged
  /-- Not here, there on another device: take its record, with the stamp its name was given. -/
  | adopt (record : SignerRecord) (name : Stamp)
  | remove
  deriving Inhabited

structure SignerDecision where
  key : String
  added : Stamp
  removed : Stamp
  existence : SignerExistence := .unchanged
  /-- A later name from another device. -/
  rename : Option (String × Stamp) := none
  deriving Inhabited

def SignerDecision.isQuiet (d : SignerDecision) (known : Option SignerMeta) : Bool :=
  (d.existence matches .unchanged) && d.rename.isNone &&
    (match known with | some m => m.added = d.added ∧ m.removed = d.removed | none => d.added = {} ∧ d.removed = {})

def decideSigner (key : String) (here : Option LocalSigner) (known : Option SignerMeta) (replicas : Array Replica) :
    SignerDecision :=
  let mine : SignerMeta := match here with
    | some l => l.seen.stamps
    | none => known.getD { key }
  let added := replicas.foldl (fun s r => Stamp.max s (r.signerMeta key).added) mine.added
  let removed := replicas.foldl (fun s r => Stamp.max s (r.signerMeta key).removed) mine.removed
  let holders : Array (SignerRecord × SignerMeta) := replicas.filterMap fun r => (r.signer? key).map fun record => (record, r.signerMeta key)
  let named := latest (fun (h : SignerRecord × SignerMeta) => h.2.name) holders
  match here with
  | none =>
    if added < removed then { key, added, removed } else
    match named with
    | none => { key, added, removed }
    | some (record, stamps) => { key, added, removed, existence := .adopt record stamps.name }
  | some _ =>
    if added < removed then { key, added, removed, existence := .remove } else
    let rename := named.bind fun (r, m) => if mine.name < m.name then some (r.name, m.name) else none
    { key, added, removed, rename }

def decideSigners (here : Array LocalSigner) (known : Array SignerMeta) (replicas : Array Replica) : Array SignerDecision := Id.run do
  let mut keys : Array String := here.map (·.key)
  let add (keys : Array String) (key : String) : Array String := if keys.contains key then keys else keys.push key
  for m in known do keys := add keys m.key
  for r in replicas do
    for (k, _) in r.signers do keys := add keys k
    if let some s := r.sync then
      for m in s.signers do keys := add keys m.key
  return keys.map fun key => decideSigner key (here.find? (·.key == key)) (known.find? (·.key == key)) replicas

end Winnow.DeviceSync
