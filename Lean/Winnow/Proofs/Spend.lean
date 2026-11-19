import Winnow.Proofs.Tools
import Winnow.Wallet.SegwitSpendReview
import Winnow.Wallet.SendAuthorization

/-! # What a spend is held to (#125, phase 3)

**A SegWit v0 account's addresses.** `SegwitMultisigAccount.usable` is what every address of such an account
goes through. It answers `none` where two of the account's keys are the same key (SEC-061) and never refuses
the account for that: `usable_error` says the only way it fails is that a key could not be derived or the
address could not be written, which are other modules' errors. So an index where two keys collide cannot
stop the scripts being listed, which is what it did before. -/

namespace Winnow.Proofs.Spend

open Winnow Winnow.Keys

/-- When a list of steps fails, one of the steps failed with that error. -/
theorem List.mapM_error {α β ε : Type} {f : α → Except ε β} :
    ∀ {l : List α} {e : ε}, l.mapM f = .error e → ∃ x, x ∈ l ∧ f x = .error e
  | [], e, h => by rw [List.mapM_nil] at h; cases h
  | a :: l, e, h => by
    rw [List.mapM_cons] at h
    cases ha : f a with
    | error e' =>
      rw [ha, error_bind] at h
      injection h with h
      exact ⟨a, List.mem_cons_self, by rw [ha, h]⟩
    | ok b =>
      rw [ha, ok_bind] at h
      cases hl : l.mapM f with
      | error e' =>
        rw [hl, error_bind] at h
        injection h with h
        obtain ⟨x, hx, hfx⟩ := List.mapM_error hl
        exact ⟨x, List.mem_cons_of_mem _ hx, by rw [hfx, h]⟩
      | ok bs => rw [hl, ok_bind] at h; cases h

theorem Array.mapM_error {α β ε : Type} {f : α → Except ε β} {xs : Array α} {e : ε}
    (h : xs.mapM f = .error e) : ∃ x, x ∈ xs ∧ f x = .error e := by
  rw [Array.mapM_eq_mapM_toList] at h
  cases hl : xs.toList.mapM f with
  | error e' =>
    rw [hl] at h
    injection h with h
    obtain ⟨x, hx, hfx⟩ := List.mapM_error hl
    exact ⟨x, Array.mem_toList_iff.mp hx, by rw [hfx, h]⟩
  | ok bs => rw [hl] at h; cases h

/-- An error `lift` passes on is another module's, by name. -/
theorem lift_error {ε α : Type} {name : ε → String} {r : Except ε α} {e : MultisigFailure}
    (h : MultisigAccount.lift name r = .error e) : ∃ n, e = .named n := by
  unfold MultisigAccount.lift at h
  cases r with
  | error e' => injection h with h; exact ⟨name e', h.symm⟩
  | ok a => cases h

private theorem usable_model {pk : type_of% @Descriptor.publicKey} {enc : type_of% @SegwitAddress.encode}
    {ad : type_of% @SegwitMultisigAccount.allDifferent} {ws : type_of% @SegwitMultisigAccount.witnessScript}
    {sh : type_of% @sha256} {spk : type_of% @SegwitMultisigAccount.scriptPubKeyOf}
    {a : SegwitMultisigAccount} {choice : Nat} {index : UInt32} {e : MultisigFailure}
    (h : (body% SegwitMultisigAccount.usable
      [Descriptor.publicKey, SegwitAddress.encode, SegwitMultisigAccount.allDifferent,
        SegwitMultisigAccount.witnessScript, sha256, SegwitMultisigAccount.scriptPubKeyOf]
      [@pk, @enc, @ad, @ws, @sh, @spk]) a choice index = .error e) :
    ∃ n, e = .named n := by
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · cases hk : Array.mapM (fun key => MultisigAccount.lift (fun x => x.name) (pk key index choice)) a.keys with
    | error err =>
      rw [hk] at h
      injection h with h
      obtain ⟨key, _, hkey⟩ := Array.mapM_error hk
      rw [← h]
      exact lift_error hkey
    | ok v =>
      rw [hk] at h
      simp only [] at h
      split at h
      · cases henc : MultisigAccount.lift (fun x => x.name)
            (enc (AddressDecoder.hrp a.network) 0 (sh (ws a.threshold v))) with
        | error err =>
          rw [henc] at h
          injection h with h
          rw [← h]
          exact lift_error henc
        | ok addr => rw [henc] at h; cases h
      · cases h
  · simp only [throw, throwThe, MonadExceptOf.throw] at h
    injection h with h
    exact ⟨_, h.symm⟩

theorem usable_def : SegwitMultisigAccount.usable = body% SegwitMultisigAccount.usable [] [] := rfl

/-- **An index where two keys collide cannot stop a SegWit v0 account** (SEC-061). When `usable` fails it is
with another module's error, by name: a key that could not be derived at that index, an address that could
not be written, or a choice that is neither receive nor change. It never refuses the account as a bad
descriptor; where two of the keys are the same key it answers `none`. -/
theorem usable_error {a : SegwitMultisigAccount} {choice : Nat} {index : UInt32} {e : MultisigFailure}
    (h : a.usable choice index = .error e) : ∃ n, e = .named n := by
  rw [usable_def] at h
  exact usable_model (pk := @Descriptor.publicKey) (enc := @SegwitAddress.encode)
    (ad := @SegwitMultisigAccount.allDifferent) (ws := @SegwitMultisigAccount.witnessScript)
    (sh := @sha256) (spk := @SegwitMultisigAccount.scriptPubKeyOf) h

/-- And `resolved`, which signing and the review of a coin go through, refuses exactly there: it fails with
the account's own error only where `usable` answered `none`. -/
theorem resolved_of_usable {a : SegwitMultisigAccount} {choice : Nat} {index : UInt32}
    {r : SegwitMultisigAccount.Resolved} (h : a.usable choice index = .ok (some r)) :
    a.resolved choice index = .ok r := by
  unfold SegwitMultisigAccount.resolved
  rw [h]
  rfl

/-! ## The send that is signed is the send that was reviewed (SEC-007, SEC-018) -/

section authorization
open ReviewedSend

/-- The wallet's test of two byte strings being the same is that they are the same. -/
theorem bytes_beq_iff (a b : ByteArray) : (a == b) = true ↔ a = b := by
  show (a.data == b.data) = true ↔ a = b
  rw [beq_iff_eq]
  constructor
  · intro h; cases a; cases b; simp only at h; rw [h]
  · intro h; rw [h]

/-- An output and a payment, as what a transaction commits to: the amount and the script. -/
def outputKey (o : Transaction.Output) : Int64 × ByteArray := (o.value, o.scriptPubKey)
def paymentKey (p : Payment) : Int64 × ByteArray := (p.amount, p.scriptPubKey)

theorem pays_iff (o : Transaction.Output) (p : Payment) : pays o p = true ↔ outputKey o = paymentKey p := by
  unfold pays outputKey paymentKey
  rw [Bool.and_eq_true, beq_iff_eq, bytes_beq_iff, Prod.mk.injEq]

/-- Taking the output that pays `p` leaves the others, whatever the order. -/
theorem takeOutput_perm : ∀ {outputs rest : List Transaction.Output} {p : Payment},
    takeOutput outputs p = some rest →
    List.Perm (outputs.map outputKey) (paymentKey p :: rest.map outputKey)
  | [], _, _, h => by cases h
  | o :: os, rest, p, h => by
    unfold takeOutput at h
    by_cases hp : pays o p = true
    · simp only [hp, ↓reduceIte] at h
      injection h with h
      rw [← h, List.map_cons, (pays_iff o p).mp hp]
    · simp only [hp, Bool.false_eq_true, ↓reduceIte] at h
      cases ht : takeOutput os p with
      | none => rw [ht] at h; cases h
      | some rest' =>
        rw [ht] at h
        injection h with h
        rw [← h, List.map_cons, List.map_cons]
        exact ((List.perm_cons _).mpr (takeOutput_perm ht)).trans (List.Perm.swap _ _ _)

/-- **Outputs that are accepted are the expected payments**, each once, in some order, and nothing else. -/
theorem outputsAre_perm : ∀ {expected : List Payment} {outputs : List Transaction.Output},
    outputsAre outputs expected = true → List.Perm (outputs.map outputKey) (expected.map paymentKey)
  | [], outputs, h => by
    unfold outputsAre at h
    cases outputs with
    | nil => exact List.Perm.refl _
    | cons o os => cases h
  | p :: ps, outputs, h => by
    unfold outputsAre at h
    cases ht : takeOutput outputs p with
    | none => rw [ht] at h; cases h
    | some rest =>
      rw [ht] at h
      exact (takeOutput_perm ht).trans ((List.perm_cons _).mpr (outputsAre_perm h))

/-- If some output pays `p`, one is taken. -/
theorem takeOutput_of_mem : ∀ {outputs : List Transaction.Output} {p : Payment},
    paymentKey p ∈ outputs.map outputKey → ∃ rest, takeOutput outputs p = some rest
  | [], _, h => by cases h
  | o :: os, p, h => by
    unfold takeOutput
    by_cases hp : pays o p = true
    · exact ⟨os, by simp only [hp, ↓reduceIte]⟩
    · simp only [hp, Bool.false_eq_true, ↓reduceIte]
      rw [List.map_cons, List.mem_cons] at h
      rcases h with h | h
      · exact absurd ((pays_iff o p).mpr h.symm) hp
      · obtain ⟨rest, hr⟩ := takeOutput_of_mem h
        exact ⟨o :: rest, by rw [hr]; rfl⟩

/-- And the other way: outputs that are the expected payments in some order are accepted. -/
theorem outputsAre_of_perm : ∀ {expected : List Payment} {outputs : List Transaction.Output},
    List.Perm (outputs.map outputKey) (expected.map paymentKey) → outputsAre outputs expected = true
  | [], outputs, h => by
    unfold outputsAre
    cases outputs with
    | nil => rfl
    | cons o os => exact absurd h.length_eq (by simp)
  | p :: ps, outputs, h => by
    unfold outputsAre
    have hmem : paymentKey p ∈ outputs.map outputKey := h.symm.subset List.mem_cons_self
    obtain ⟨rest, hr⟩ := takeOutput_of_mem hmem
    rw [hr]
    exact outputsAre_of_perm ((List.perm_cons _).mp ((takeOutput_perm hr).symm.trans h))

/-- A coin as a transaction names it: the transaction it came from and which output. -/
def outpointKey (o : Transaction.Outpoint) : ByteArray × UInt32 := (o.txid, o.vout)

/-- The wallet's test of two lists of coins being the same is that they are the same coins in the same
order. -/
theorem outpoints_beq_iff (xs ys : Array Transaction.Outpoint) :
    (xs == ys) = true ↔ xs.toList.map outpointKey = ys.toList.map outpointKey := by
  show Array.isEqv xs ys (· == ·) = true ↔ _
  rw [Array.isEqv_iff_rel]
  have hrel : ∀ a b : Transaction.Outpoint, (a == b) = true ↔ outpointKey a = outpointKey b := by
    intro a b
    show (a.txid == b.txid && a.vout == b.vout) = true ↔ _
    unfold outpointKey
    rw [Bool.and_eq_true, bytes_beq_iff, beq_iff_eq, Prod.mk.injEq]
  constructor
  · rintro ⟨hsz, hall⟩
    apply List.ext_getElem
    · rw [List.length_map, List.length_map, Array.length_toList, Array.length_toList, hsz]
    · intro i h1 h2
      rw [List.getElem_map, List.getElem_map, Array.getElem_toList, Array.getElem_toList]
      rw [List.length_map, Array.length_toList] at h1
      exact (hrel _ _).mp (hall i h1)
  · intro h
    have hsz : xs.size = ys.size := by
      have := congrArg List.length h
      rw [List.length_map, List.length_map, Array.length_toList, Array.length_toList] at this
      exact this
    refine ⟨hsz, fun i hi => (hrel _ _).mpr ?_⟩
    have h1 : i < (xs.toList.map outpointKey).length := by rw [List.length_map, Array.length_toList]; exact hi
    have h2 : i < (ys.toList.map outpointKey).length := by
      rw [List.length_map, Array.length_toList, ← hsz]; exact hi
    have := List.getElem_of_eq h h1
    rw [List.getElem_map, List.getElem_map, Array.getElem_toList, Array.getElem_toList] at this
    exact this

/-- **The send that is signed is the send that was reviewed, exactly** (SEC-007, SEC-018).
`authorizesTransaction` accepts a transaction, with the fee and change it was built with, if and only if:
the fee and the change amount are the reviewed ones; it spends the reviewed coins, the same ones in the same
order; each silent payment the wallet resolved has its reviewed amount, in order; its outputs are, as a
multiset of (amount, script), exactly the reviewed payments, the resolved silent payments and the reviewed
change, with nothing added, dropped, split or redirected; and there is a change payment just when there is a
change amount. -/
theorem authorizesTransaction_iff (r : ReviewedSend) (tx : Transaction) (fee : Int64)
    (changeAmount : Option Int64) (resolved : Array Payment) :
    r.authorizesTransaction tx fee changeAmount resolved = true ↔
      fee = r.fee ∧ changeAmount = r.changeAmount ∧
      tx.inputs.toList.map (fun i => outpointKey i.previousOutput) = r.selected.toList.map outpointKey ∧
      resolved.map (·.amount) = r.silentAmounts ∧
      List.Perm (tx.outputs.toList.map outputKey) ((r.expected resolved).map paymentKey) ∧
      r.change.isNone = r.changeAmount.isNone := by
  unfold authorizesTransaction
  have hin : (tx.inputs.map (·.previousOutput) == r.selected) = true ↔
      tx.inputs.toList.map (fun i => outpointKey i.previousOutput) = r.selected.toList.map outpointKey := by
    rw [outpoints_beq_iff, Array.toList_map, List.map_map]
    rfl
  have hout : outputsAre tx.outputs.toList (r.expected resolved) = true ↔
      List.Perm (tx.outputs.toList.map outputKey) ((r.expected resolved).map paymentKey) :=
    ⟨outputsAre_perm, outputsAre_of_perm⟩
  simp only [Bool.and_eq_true, beq_iff_eq, hin, hout, and_assoc]

end authorization

end Winnow.Proofs.Spend
