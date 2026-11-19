import Winnow.Wallet.DeviceSync

/-! # What a device does with what it reads of the others (`Winnow.DeviceSync`)

`DeviceSync.lean` is not a merge of two states. `decideAccount` and `decideSigner` take this device's state
and the other devices' backups and return a decision. What is proved of them is what a person relies on:

- **Being there.** An account that is removed, as far as this device and every backup know, does not come
  back to a device that lacks it (`decideAccount_absent_removed`); a device that has it removes it once it
  holds nothing (`decideAccount_removes`); and a device that still sees coins or a payment in it keeps it and
  adds it again, later than the removal (`decideAccount_reasserts`). One that is not removed is kept
  (`decideAccount_keeps`). The same for signers, which hold nothing.
- **Stamps.** The stamps a decision goes by are the latest this device and every backup know
  (`decideAccount_removed`); they do not depend on the order the backups are read in (`addedOf_perm`,
  `removedOf_perm`); they are never behind what the device knew or what any backup says
  (`addedOf_not_behind`, `removedOf_not_behind`); and reading the same backups again changes nothing in them
  (`addedOf_again`, `removedOf_again`).
- **Address counters never go back** (`accountChanges_raise`).

Not proved: that the rest of a decision (which name, which registration, which copy of a payment) is the
same whatever the order of the backups. It is not true as stated: two backups written before stamps existed
both carry the stamp of the beginning of time, and between such a tie the first one read wins. Nor that
applying a decision and deciding again is quiet as a whole: applying is the app's
(`LeanApp/WinnowApp/Real/DeviceSync.lean`), not a function here; `device-sync-test` holds it. -/

namespace Winnow.Proofs.DeviceSync
open Winnow.DeviceSync

theorem Stamp.lt_def (a b : Stamp) : a < b ↔ a.time < b.time ∨ (a.time = b.time ∧ a.device < b.device) := Iff.rfl

theorem Stamp.max_idem (a : Stamp) : Stamp.max a a = a := by
  simp [Stamp.max]

theorem Stamp.max_comm (a b : Stamp) : Stamp.max a b = Stamp.max b a := by
  obtain ⟨at_, ad⟩ := a
  obtain ⟨bt, bd⟩ := b
  simp only [Stamp.max, Stamp.lt_def]
  split <;> split <;> first | rfl | (simp only [Stamp.mk.injEq]; omega)

theorem Stamp.max_assoc (a b c : Stamp) : Stamp.max (Stamp.max a b) c = Stamp.max a (Stamp.max b c) := by
  obtain ⟨at_, ad⟩ := a
  obtain ⟨bt, bd⟩ := b
  obtain ⟨ct, cd⟩ := c
  by_cases h1 : at_ < bt ∨ (at_ = bt ∧ ad < bd) <;> by_cases h2 : bt < ct ∨ (bt = ct ∧ bd < cd) <;>
    by_cases h3 : at_ < ct ∨ (at_ = ct ∧ ad < cd) <;> simp [Stamp.max, Stamp.lt_def, h1, h2, h3] <;> omega

theorem Stamp.after_later (clock now device : Nat) (s : Stamp) (h : s.time ≤ clock) :
    s < Stamp.after clock now device := by
  simp only [Stamp.lt_def, Stamp.after]
  left
  have : clock + 1 ≤ Nat.max now (clock + 1) := Nat.le_max_right _ _
  omega

/-! ## Later, and the later of two -/

theorem Stamp.lt_irrefl (a : Stamp) : ¬ a < a := by
  rw [Stamp.lt_def]; omega

theorem Stamp.lt_asymm {a b : Stamp} (h : a < b) : ¬ b < a := by
  rw [Stamp.lt_def] at h ⊢; omega

theorem Stamp.lt_trans {a b c : Stamp} (h1 : a < b) (h2 : b < c) : a < c := by
  rw [Stamp.lt_def] at h1 h2 ⊢; omega

/-- The later of two is behind neither. -/
theorem Stamp.not_max_lt_left (a b : Stamp) : ¬ Stamp.max a b < a := by
  unfold Stamp.max
  split
  · rename_i h; exact Stamp.lt_asymm h
  · exact Stamp.lt_irrefl a

theorem Stamp.not_max_lt_right (a b : Stamp) : ¬ Stamp.max a b < b := by
  unfold Stamp.max
  split
  · exact Stamp.lt_irrefl b
  · rename_i h; exact h

/-- The later of two is one of them. -/
theorem Stamp.max_eq (a b : Stamp) : Stamp.max a b = a ∨ Stamp.max a b = b := by
  unfold Stamp.max
  split
  · exact Or.inr rfl
  · exact Or.inl rfl

/-- Taking the later of a stamp and each of several, one after another. -/
def latestOf {α : Type} (g : α → Stamp) (start : Stamp) (xs : List α) : Stamp :=
  xs.foldl (fun s x => Stamp.max s (g x)) start

theorem latestOf_perm {α : Type} (g : α → Stamp) (start : Stamp) {xs ys : List α} (h : List.Perm xs ys) :
    latestOf g start xs = latestOf g start ys := by
  unfold latestOf
  induction h generalizing start with
  | nil => rfl
  | cons x _ ih => exact ih _
  | swap x y l =>
    simp only [List.foldl_cons]
    rw [Stamp.max_assoc, Stamp.max_comm (g y) (g x), ← Stamp.max_assoc]
  | trans _ _ ih1 ih2 => rw [ih1, ih2]

theorem latestOf_not_lt_start {α : Type} (g : α → Stamp) : ∀ (xs : List α) (start : Stamp),
    ¬ latestOf g start xs < start
  | [], start => Stamp.lt_irrefl start
  | x :: xs, start => by
    intro h
    have h1 := latestOf_not_lt_start g xs (Stamp.max start (g x))
    by_cases hm : Stamp.max start (g x) = start
    · unfold latestOf at h h1; rw [List.foldl_cons, hm] at h; rw [hm] at h1; exact h1 h
    · have hlt : start < Stamp.max start (g x) := by
        by_cases hsx : start < g x
        · simp only [Stamp.max, hsx, ↓reduceIte]
        · simp only [Stamp.max, hsx, ↓reduceIte] at hm
          exact absurd trivial hm
      unfold latestOf at h h1
      rw [List.foldl_cons] at h
      exact h1 (Stamp.lt_trans h hlt)

theorem latestOf_not_lt_mem {α : Type} (g : α → Stamp) : ∀ (xs : List α) (start : Stamp) (x : α),
    x ∈ xs → ¬ latestOf g start xs < g x
  | y :: ys, start, x, hx => by
    intro h
    rw [List.mem_cons] at hx
    have hstep : latestOf g start (y :: ys) = latestOf g (Stamp.max start (g y)) ys := rfl
    rw [hstep] at h
    rcases hx with rfl | hx
    · have h1 := latestOf_not_lt_start g ys (Stamp.max start (g x))
      by_cases hm : Stamp.max start (g x) = g x
      · rw [hm] at h h1; exact h1 h
      · have hlt : g x < Stamp.max start (g x) := by
          by_cases hsx : start < g x
          · simp only [Stamp.max, hsx, ↓reduceIte] at hm
            exact absurd trivial hm
          · simp only [Stamp.max, hsx, ↓reduceIte] at hm ⊢
            rw [Stamp.lt_def] at hsx ⊢
            have hne : g x ≠ start := fun e => hm e.symm
            have hne' : ¬ ((g x).time = start.time ∧ (g x).device = start.device) := by
              intro ⟨h1, h2⟩; apply hne; cases hgx : g x; cases start; simp_all
            omega
        exact h1 (Stamp.lt_trans h hlt)
    · exact latestOf_not_lt_mem g ys _ x hx h

/-- Going over the same backups again changes nothing. -/
theorem latestOf_absorb {α : Type} (g : α → Stamp) (xs : List α) (start : Stamp) :
    latestOf g (latestOf g start xs) xs = latestOf g start xs := by
  suffices h : ∀ (ys : List α) (s : Stamp), (∀ y ∈ ys, ¬ s < g y) → latestOf g s ys = s from
    h xs _ (fun y hy => latestOf_not_lt_mem g xs start y hy)
  intro ys
  induction ys with
  | nil => intro s _; rfl
  | cons y ys ih =>
    intro s hs
    have hy : Stamp.max s (g y) = s := by
      simp only [Stamp.max, hs y List.mem_cons_self, ↓reduceIte]
    show latestOf g (Stamp.max s (g y)) ys = s
    rw [hy]
    exact ih s (fun z hz => hs z (List.mem_cons_of_mem _ hz))

/-! ## What a device decides about an account -/

/-- The stamps a device starts from: its own for an account it has, what it remembers of one it does not,
or the beginning of time. -/
def startOf (id : String) (here : Option LocalAccount) (known : Option AccountMeta) : AccountMeta :=
  match here with
  | some l => l.seen.stamps
  | none => known.getD { id }

/-- When the account was last added, as far as this device and every backup know. -/
def addedOf (id : String) (here : Option LocalAccount) (known : Option AccountMeta) (replicas : Array Replica) :
    Stamp :=
  latestOf (fun r => (r.accountMeta id).added) (startOf id here known).added replicas.toList

/-- When it was last removed, likewise. -/
def removedOf (id : String) (here : Option LocalAccount) (known : Option AccountMeta) (replicas : Array Replica) :
    Stamp :=
  latestOf (fun r => (r.accountMeta id).removed) (startOf id here known).removed replicas.toList

/-- Whether the account is, as far as is known, removed: removed later than it was last added. -/
def knownRemoved (id : String) (here : Option LocalAccount) (known : Option AccountMeta) (replicas : Array Replica) :
    Prop :=
  addedOf id here known replicas < removedOf id here known replicas

private theorem added_fold (id : String) (start : Stamp) (replicas : Array Replica) :
    Array.foldl (fun s r => Stamp.max s (r.accountMeta id).added) start replicas =
      latestOf (fun r => (r.accountMeta id).added) start replicas.toList := by
  unfold latestOf; rw [Array.foldl_toList]

private theorem removed_fold (id : String) (start : Stamp) (replicas : Array Replica) :
    Array.foldl (fun s r => Stamp.max s (r.accountMeta id).removed) start replicas =
      latestOf (fun r => (r.accountMeta id).removed) start replicas.toList := by
  unfold latestOf; rw [Array.foldl_toList]

/-- **The removal stamp a decision carries** is the latest removal this device or any backup knows of. -/
theorem decideAccount_removed (fresh : Stamp) (txidOf : MultisigSpendDraft → Option ByteArray) (id : String)
    (here : Option LocalAccount) (known : Option AccountMeta) (replicas : Array Replica) :
    (decideAccount fresh txidOf id here known replicas).removed = removedOf id here known replicas := by
  unfold decideAccount removedOf startOf
  simp only [added_fold, removed_fold]
  cases here with
  | none => simp only []; repeat (first | rfl | split)
  | some l => simp only []; repeat (first | rfl | split)

/-- **A removed account does not come back to a device that does not have it.** If the account is removed,
as far as this device and the backups know, a device without it takes nothing: no backup's copy is adopted. -/
theorem decideAccount_absent_removed (fresh : Stamp) (txidOf : MultisigSpendDraft → Option ByteArray)
    (id : String) (known : Option AccountMeta) (replicas : Array Replica)
    (h : knownRemoved id none known replicas) :
    (decideAccount fresh txidOf id none known replicas).existence = .unchanged := by
  unfold knownRemoved addedOf removedOf startOf at h
  unfold decideAccount
  simp only [added_fold, removed_fold, h, ↓reduceIte]

/-- **A removal is followed where the account holds nothing.** A device that has the account, with every
coin spent in a block and no payment under way, removes it once it is removed as far as is known. -/
theorem decideAccount_removes (fresh : Stamp) (txidOf : MultisigSpendDraft → Option ByteArray)
    (id : String) (l : LocalAccount) (known : Option AccountMeta) (replicas : Array Replica)
    (h : knownRemoved id (some l) known replicas) (hremovable : l.removable = true) :
    (decideAccount fresh txidOf id (some l) known replicas).existence = .remove := by
  unfold knownRemoved addedOf removedOf startOf at h
  unfold decideAccount
  simp only [added_fold, removed_fold, h, hremovable, ↓reduceIte]

/-- **A removal is not followed where the account still holds coins or a payment** (`Existence.reassert`).
That device keeps the account and adds it again now, and if now is later than the removal, the account is
there again as far as anyone who reads this device's backup knows. -/
theorem decideAccount_reasserts (fresh : Stamp) (txidOf : MultisigSpendDraft → Option ByteArray)
    (id : String) (l : LocalAccount) (known : Option AccountMeta) (replicas : Array Replica)
    (h : knownRemoved id (some l) known replicas) (hheld : l.removable = false) :
    let d := decideAccount fresh txidOf id (some l) known replicas
    d.existence = .reassert ∧ d.added = fresh ∧
      (removedOf id (some l) known replicas < fresh → ¬ d.added < d.removed) := by
  have hrem := decideAccount_removed fresh txidOf id (some l) known replicas
  unfold knownRemoved addedOf removedOf startOf at h
  have hd : decideAccount fresh txidOf id (some l) known replicas =
      { id, added := fresh, removed := removedOf id (some l) known replicas, existence := .reassert } := by
    unfold decideAccount removedOf startOf
    simp only [added_fold, removed_fold, h, hheld, Bool.false_eq_true, ↓reduceIte]
  intro d
  refine ⟨by rw [show d = _ from hd], by rw [show d = _ from hd], fun hlater => ?_⟩
  rw [show d = _ from hd]
  exact Stamp.lt_asymm hlater

/-- **An account that is not removed is never removed by a decision.** Where it is there as far as is known,
a device that has it keeps it; only names, counters, a registration or a payment change. -/
theorem decideAccount_keeps (fresh : Stamp) (txidOf : MultisigSpendDraft → Option ByteArray)
    (id : String) (l : LocalAccount) (known : Option AccountMeta) (replicas : Array Replica)
    (h : ¬ knownRemoved id (some l) known replicas) :
    (decideAccount fresh txidOf id (some l) known replicas).existence = .unchanged := by
  unfold knownRemoved addedOf removedOf startOf at h
  unfold decideAccount
  simp only [added_fold, removed_fold, h, ↓reduceIte]

/-- **The stamps do not depend on the order the backups are read in.** -/
theorem removedOf_perm (id : String) (here : Option LocalAccount) (known : Option AccountMeta)
    {replicas replicas' : Array Replica} (h : List.Perm replicas.toList replicas'.toList) :
    removedOf id here known replicas = removedOf id here known replicas' :=
  latestOf_perm _ _ h

theorem addedOf_perm (id : String) (here : Option LocalAccount) (known : Option AccountMeta)
    {replicas replicas' : Array Replica} (h : List.Perm replicas.toList replicas'.toList) :
    addedOf id here known replicas = addedOf id here known replicas' :=
  latestOf_perm _ _ h

/-- **Stamps only move forward**: what a decision knows of the removal is never behind what the device knew,
nor behind any backup. -/
theorem removedOf_not_behind (id : String) (here : Option LocalAccount) (known : Option AccountMeta)
    (replicas : Array Replica) :
    ¬ removedOf id here known replicas < (startOf id here known).removed ∧
    ∀ r ∈ replicas, ¬ removedOf id here known replicas < (r.accountMeta id).removed :=
  ⟨latestOf_not_lt_start _ _ _, fun r hr => latestOf_not_lt_mem _ _ _ r (Array.mem_toList_iff.mpr hr)⟩

theorem addedOf_not_behind (id : String) (here : Option LocalAccount) (known : Option AccountMeta)
    (replicas : Array Replica) :
    ¬ addedOf id here known replicas < (startOf id here known).added ∧
    ∀ r ∈ replicas, ¬ addedOf id here known replicas < (r.accountMeta id).added :=
  ⟨latestOf_not_lt_start _ _ _, fun r hr => latestOf_not_lt_mem _ _ _ r (Array.mem_toList_iff.mpr hr)⟩

/-- **Reading the same backups again changes nothing in the stamps**: once a device holds the stamps a
decision gave it, deciding again over the same backups gives the same stamps. -/
theorem removedOf_again (id : String) (here : Option LocalAccount) (known : Option AccountMeta)
    (replicas : Array Replica) :
    latestOf (fun r => (r.accountMeta id).removed) (removedOf id here known replicas) replicas.toList =
      removedOf id here known replicas :=
  latestOf_absorb _ _ _

theorem addedOf_again (id : String) (here : Option LocalAccount) (known : Option AccountMeta)
    (replicas : Array Replica) :
    latestOf (fun r => (r.accountMeta id).added) (addedOf id here known replicas) replicas.toList =
      addedOf id here known replicas :=
  latestOf_absorb _ _ _

private theorem u32_le_max_right (a b : UInt32) : b ≤ max a b := by
  show b ≤ if a ≤ b then b else a
  split
  · exact UInt32.le_refl b
  · rename_i h
    rw [UInt32.le_iff_toNat_le] at h ⊢
    omega

/-- **Address counters never go back.** Whatever a decision changes for an account a device has, a change to
its counters sets each to at least what the device had. -/
theorem accountChanges_raise (txidOf : MultisigSpendDraft → Option ByteArray) (l : LocalAccount)
    (mine : AccountMeta) (holders : Array Holder) (named registered : Option Holder) (receive change r c : UInt32)
    (h : Change.raise r c ∈ accountChanges txidOf l mine holders named registered receive change) :
    l.record.nextReceiveIndex ≤ r ∧ l.record.nextChangeIndex ≤ c := by
  unfold accountChanges at h
  simp only [Array.mem_append, Option.mem_toArray] at h
  rcases h with ((h | h) | h) | h
  · unfold renameChange at h
    split at h
    · split at h
      · injection h with h; cases h
      · cases h
    · cases h
  · unfold raiseChange at h
    split at h
    · injection h with h
      injection h with h1 h2
      rw [← h1, ← h2]
      exact ⟨u32_le_max_right _ _, u32_le_max_right _ _⟩
    · cases h
  · unfold ledgerChange at h
    split at h
    · split at h
      · split at h
        · injection h with h; cases h
        · cases h
      · cases h
    · cases h
  · unfold draftChange at h
    simp only [] at h
    split at h
    · injection h with h; cases h
    · split at h
      · cases h
      · injection h with h; cases h

/-! ## What a device decides about a signer -/

/-- A signer's stamps, as `addedOf` and `removedOf` are an account's. -/
def signerStart (key : String) (here : Option LocalSigner) (known : Option SignerMeta) : SignerMeta :=
  match here with
  | some l => l.seen.stamps
  | none => known.getD { key }

def signerRemoved (key : String) (here : Option LocalSigner) (known : Option SignerMeta)
    (replicas : Array Replica) : Prop :=
  latestOf (fun r => (r.signerMeta key).added) (signerStart key here known).added replicas.toList <
    latestOf (fun r => (r.signerMeta key).removed) (signerStart key here known).removed replicas.toList

private theorem signer_added_fold (key : String) (start : Stamp) (replicas : Array Replica) :
    Array.foldl (fun s r => Stamp.max s (r.signerMeta key).added) start replicas =
      latestOf (fun r => (r.signerMeta key).added) start replicas.toList := by
  unfold latestOf; rw [Array.foldl_toList]

private theorem signer_removed_fold (key : String) (start : Stamp) (replicas : Array Replica) :
    Array.foldl (fun s r => Stamp.max s (r.signerMeta key).removed) start replicas =
      latestOf (fun r => (r.signerMeta key).removed) start replicas.toList := by
  unfold latestOf; rw [Array.foldl_toList]

/-- **A removed signer does not come back** to a device that does not have it. -/
theorem decideSigner_absent_removed (key : String) (known : Option SignerMeta) (replicas : Array Replica)
    (h : signerRemoved key none known replicas) :
    (decideSigner key none known replicas).existence = .unchanged := by
  unfold signerRemoved signerStart at h
  unfold decideSigner
  simp only [signer_added_fold, signer_removed_fold, h, ↓reduceIte]

/-- **A removal of a signer is followed** by a device that has it. -/
theorem decideSigner_removes (key : String) (l : LocalSigner) (known : Option SignerMeta)
    (replicas : Array Replica) (h : signerRemoved key (some l) known replicas) :
    (decideSigner key (some l) known replicas).existence = .remove := by
  unfold signerRemoved signerStart at h
  unfold decideSigner
  simp only [signer_added_fold, signer_removed_fold, h, ↓reduceIte]

/-- **A signer that is not removed is kept.** -/
theorem decideSigner_keeps (key : String) (l : LocalSigner) (known : Option SignerMeta)
    (replicas : Array Replica) (h : ¬ signerRemoved key (some l) known replicas) :
    (decideSigner key (some l) known replicas).existence = .unchanged := by
  unfold signerRemoved signerStart at h
  unfold decideSigner
  simp only [signer_added_fold, signer_removed_fold, h, ↓reduceIte]

end Winnow.Proofs.DeviceSync
