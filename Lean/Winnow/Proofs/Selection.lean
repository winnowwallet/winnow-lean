import Winnow.Proofs.Tools
import Winnow.Wallet.CoinSelection

/-! # Coin selection adds up (#125, phase 3; SEC-047)

`CoinSelection.select` chooses which coins a send spends, what fee it pays and what change comes back. A
mistake there is money made or lost on paper: a fee that is not the rate's, change that is dust, or selected
coins that do not come to what is paid. `select_conserves` says none of that can happen, for every list of
coins, payments, change script, rate and witness size.

What makes it provable is in the code: the fee is whole-number arithmetic (`feeAt`), the candidates are gone
through by a recursion (`take`), and the payments are added up by one (`paymentTargetFrom`). The one `Float`
left is the rate at the door (`satPerKvB`); nothing is proved about that conversion, and the theorem holds
for whatever whole number it gives.

Not proved: that the coins are taken largest first, that no fewer coins would do, or anything about
`Wallet.feeBumpCandidate`, whose arithmetic is still `Float`. -/

namespace Winnow.Proofs.Selection
open Winnow Winnow.CoinSelection
open Winnow.Proofs (throw_eq pure_eq ok_bind error_bind)

/-- What some coins come to. -/
def coinTotal (coins : List WalletUTXO) : Int := (coins.map (·.amount.toInt)).sum

/-- What some payments come to. -/
def paymentTotal (payments : List Payment) : Int := (payments.map (·.amount.toInt)).sum

theorem checkedAdd_ok {a b s : Int} (h : checkedAdd a b = .ok s) : s = a + b ∧ s ≤ maxI := by
  unfold checkedAdd at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · simp only [throw, throwThe, MonadExceptOf.throw] at h; cases h
  · rename_i hle
    injection h with h
    exact ⟨h.symm, by rw [← h]; exact Int.not_lt.mp hle⟩

/-- A payment that passes is of more than nothing. -/
theorem checkPayment_ok {p : Payment} {u : Unit} (h : checkPayment p = .ok u) : 0 < p.amount.toInt := by
  unfold checkPayment at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · rename_i hb
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hb
    have := Int64.lt_iff_toInt_lt.mp hb.1
    simpa using this
  · simp only [throw, throwThe, MonadExceptOf.throw] at h; cases h

/-- The payments' target is what the payments come to, on top of where it started, and no less than
where it started. -/
theorem paymentTargetFrom_ok : ∀ {payments : List Payment} {start target : Int},
    paymentTargetFrom payments start = .ok target →
    target = start + paymentTotal payments ∧ start ≤ target
  | [], start, target, h => by
    unfold paymentTargetFrom at h
    rw [pure_eq] at h
    injection h with h
    rw [← h]; simp [paymentTotal]
  | p :: rest, start, target, h => by
    unfold paymentTargetFrom at h
    cases hc : checkPayment p with
    | error e => rw [hc, error_bind] at h; cases h
    | ok u =>
      rw [hc, ok_bind] at h
      have hpos := checkPayment_ok hc
      cases ha : checkedAdd start p.amount.toInt with
      | error e => rw [ha, error_bind] at h; cases h
      | ok s =>
        rw [ha, ok_bind] at h
        obtain ⟨h1, h2⟩ := paymentTargetFrom_ok h
        have h3 := (checkedAdd_ok ha).1
        refine ⟨?_, by omega⟩
        rw [h1, h3]
        simp only [paymentTotal, List.map_cons, List.sum_cons]
        omega

/-- A fee that `fee` returns is the rate's, from 0 to Bitcoin's supply. -/
theorem fee_ok {inputCount : Nat} {outputs : Array Transaction.Output} {witness : Int} {rate : Nat} {f : Int}
    (h : fee inputCount outputs witness rate = .ok f) :
    f = feeAt (TransactionBuilder.signedVSize inputCount outputs witness) rate ∧ 0 ≤ f ∧ f ≤ maxI := by
  unfold fee at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · rename_i hb
    injection h with h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hb
    exact ⟨h.symm, by rw [← h]; exact hb.1, by rw [← h]; exact hb.2⟩
  · simp only [throw, throwThe, MonadExceptOf.throw] at h; cases h

/-- **Taking coins keeps the books.** What `take` returns is the coins it had plus a run of the candidates,
and the total it returns is the total it had plus what that run comes to; and the total is within Bitcoin's
supply whenever it started there. -/
theorem take_ok {feeWithChange : Nat → M Int} {target : Int} :
    ∀ {candidates : List WalletUTXO} {selected selected' : Array WalletUTXO} {total total' : Int},
    take feeWithChange target candidates selected total = .ok (selected', total') →
    ∃ taken, selected'.toList = selected.toList ++ taken ∧ total' = total + coinTotal taken ∧
      (total ≤ maxI → total' ≤ maxI) ∧ (∀ u, u ∈ taken → u ∈ candidates)
  | [], selected, selected', total, total', h => by
    unfold take at h
    rw [pure_eq] at h
    injection h with h
    injection h with h1 h2
    exact ⟨[], by rw [← h1]; simp, by rw [← h2]; simp [coinTotal], fun hle => by rw [← h2]; exact hle,
      fun u hu => by cases hu⟩
  | u :: rest, selected, selected', total, total', h => by
    unfold take at h
    simp only [bind, Except.bind, pure, Except.pure] at h
    split at h
    · simp only [throw, throwThe, MonadExceptOf.throw] at h; cases h
    · rename_i hsum
      cases hf : feeWithChange (selected.size + 1) with
      | error e => rw [hf] at h; cases h
      | ok f =>
        rw [hf] at h
        simp only [] at h
        cases ha : checkedAdd target f with
        | error e => rw [ha] at h; cases h
        | ok required =>
          rw [ha] at h
          simp only [] at h
          split at h
          · injection h with h
            injection h with h1 h2
            refine ⟨[u], by rw [← h1]; simp, by rw [← h2]; simp [coinTotal], fun _ => ?_, fun v hv => ?_⟩
            · rw [← h2]; exact Int.not_lt.mp hsum
            · simp only [List.mem_singleton] at hv; rw [hv]; exact List.mem_cons_self
          · obtain ⟨taken, ht1, ht2, ht3, ht4⟩ := take_ok h
            refine ⟨u :: taken, by rw [ht1]; simp, by rw [ht2]; simp [coinTotal]; omega,
              fun _ => ht3 (Int.not_lt.mp hsum), fun v hv => ?_⟩
            rw [List.mem_cons] at hv
            rcases hv with rfl | hv
            · exact List.mem_cons_self
            · exact List.mem_cons_of_mem _ (ht4 v hv)

/-- The outputs a selection is sized with: the payments, and the change when there is one. -/
def paymentOutputs (payments : Array Payment) : Array Transaction.Output :=
  payments.map fun p => { value := p.amount, scriptPubKey := p.scriptPubKey }

def changeOutput (changeScript : ByteArray) : Transaction.Output := { value := 0, scriptPubKey := changeScript }

private theorem select_model {ca : type_of% @checkArguments} {spk : type_of% @satPerKvB}
    {pt : type_of% @paymentTarget} {css : type_of% @checkSpendableSet} {feeF : type_of% @fee}
    {takeF : type_of% @take} {cad : type_of% @checkedAdd} {cst : type_of% @checkStandardSize}
    {dt : type_of% @dustThreshold}
    {utxos : Array WalletUTXO} {payments : Array Payment} {changeScript : ByteArray} {rate : Float} {w : Int}
    {s : Selection}
    (h : (body% CoinSelection.select
      [CoinSelection.checkArguments, CoinSelection.satPerKvB, CoinSelection.paymentTarget,
        CoinSelection.checkSpendableSet, CoinSelection.fee, CoinSelection.take, CoinSelection.checkedAdd,
        CoinSelection.checkStandardSize, CoinSelection.dustThreshold]
      [@ca, @spk, @pt, @css, @feeF, @takeF, @cad, @cst, @dt]) utxos payments changeScript rate w = .ok s) :
    ∃ (target : Int) (selected : Array WalletUTXO) (total fWith fNo required : Int),
      pt payments = .ok target ∧
      takeF (fun count => feeF count ((paymentOutputs payments).push (changeOutput changeScript)) w (spk rate))
        target (utxos.toList.mergeSort fun a b => !decide (a.amount < b.amount)) #[] 0 = .ok (selected, total) ∧
      feeF selected.size ((paymentOutputs payments).push (changeOutput changeScript)) w (spk rate) = .ok fWith ∧
      feeF selected.size (paymentOutputs payments) w (spk rate) = .ok fNo ∧
      cad target fNo = .ok required ∧ required ≤ total ∧
      ((dt changeScript ≤ total - target - fWith ∧
          s = { selected, fee := Int64.ofInt fWith, changeAmount := some (Int64.ofInt (total - target - fWith)) }) ∨
        (¬ dt changeScript ≤ total - target - fWith ∧
          s = { selected, fee := Int64.ofInt (total - target), changeAmount := none })) := by
  simp only [bind, Except.bind, pure, Except.pure] at h
  cases h1 : ca utxos changeScript rate w with
  | error e => rw [h1] at h; cases h
  | ok u1 =>
  rw [h1] at h; simp only [] at h
  cases h2 : pt payments with
  | error e => rw [h2] at h; cases h
  | ok target =>
  rw [h2] at h; simp only [] at h
  cases h3 : css utxos with
  | error e => rw [h3] at h; cases h
  | ok u3 =>
  rw [h3] at h; simp only [] at h
  cases h4 : takeF (fun count => feeF count ((paymentOutputs payments).push (changeOutput changeScript)) w (spk rate))
      target (utxos.toList.mergeSort fun a b => !decide (a.amount < b.amount)) #[] 0 with
  | error e => rw [paymentOutputs, changeOutput] at h4; rw [h4] at h; cases h
  | ok taken =>
  obtain ⟨selected, total⟩ := taken
  rw [paymentOutputs, changeOutput] at h4; rw [h4] at h; simp only [] at h
  cases h5 : feeF selected.size ((paymentOutputs payments).push (changeOutput changeScript)) w (spk rate) with
  | error e => rw [paymentOutputs, changeOutput] at h5; rw [h5] at h; cases h
  | ok fWith =>
  rw [paymentOutputs, changeOutput] at h5; rw [h5] at h; simp only [] at h
  cases h6 : feeF selected.size (paymentOutputs payments) w (spk rate) with
  | error e => rw [paymentOutputs] at h6; rw [h6] at h; cases h
  | ok fNo =>
  rw [paymentOutputs] at h6; rw [h6] at h; simp only [] at h
  cases h7 : cad target fNo with
  | error e => rw [h7] at h; cases h
  | ok required =>
  rw [h7] at h; simp only [] at h
  by_cases h8 : total ≥ required
  · simp only [h8, ↓reduceIte] at h
    refine ⟨target, selected, total, fWith, fNo, required, rfl, ?_, ?_, ?_, h7, h8, ?_⟩
    · rw [paymentOutputs, changeOutput]; exact h4
    · rw [paymentOutputs, changeOutput]; exact h5
    · rw [paymentOutputs]; exact h6
    · by_cases h9 : total - target - fWith ≥ dt changeScript
      · simp only [h9, ↓reduceIte] at h
        split at h
        · cases h
        · injection h with h; exact Or.inl ⟨h9, h.symm⟩
      · simp only [h9, ↓reduceIte] at h
        split at h
        · cases h
        · injection h with h; exact Or.inr ⟨h9, h.symm⟩
  · simp only [h8, ↓reduceIte, throw, throwThe, MonadExceptOf.throw] at h
    cases h

theorem select_def : @CoinSelection.select = body% CoinSelection.select [] [] := rfl

theorem maxI_lt : maxI < 2 ^ 63 := by decide

/-- The dust threshold is not negative. -/
theorem dustThreshold_nonneg (script : ByteArray) : 0 ≤ dustThreshold script := by
  unfold dustThreshold
  apply Int.tdiv_nonneg
  · apply Int.mul_nonneg
    · exact Int.natCast_nonneg _
    · decide
  · decide

/-- **Coin selection adds up** (SEC-047). Whatever `select` returns, for any coins, payments, change script,
rate and witness size:

- the coins selected come to exactly the payments, the fee and the change (nothing is made or lost);
- the fee is not negative, and with a change output it is exactly `⌈vsize · rate / 1000⌉` for the
  transaction's size at the rate asked for; with none it is at least that for the smaller transaction, the
  rest being change too small to be worth an output;
- a change output is never dust;
- every coin selected is one of the coins offered. -/
theorem select_conserves {utxos : Array WalletUTXO} {payments : Array Payment} {changeScript : ByteArray}
    {rate : Float} {w : Int} {s : Selection}
    (h : CoinSelection.select utxos payments changeScript rate w = .ok s) :
    coinTotal s.selected.toList =
        paymentTotal payments.toList + s.fee.toInt + ((s.changeAmount.map (·.toInt)).getD 0) ∧
      0 ≤ s.fee.toInt ∧
      (∀ c, s.changeAmount = some c → dustThreshold changeScript ≤ c.toInt ∧
        s.fee.toInt = feeAt (TransactionBuilder.signedVSize s.selected.size
          ((paymentOutputs payments).push (changeOutput changeScript)) w) (satPerKvB rate)) ∧
      (s.changeAmount = none →
        feeAt (TransactionBuilder.signedVSize s.selected.size (paymentOutputs payments) w) (satPerKvB rate)
          ≤ s.fee.toInt) ∧
      (∀ u, u ∈ s.selected → u ∈ utxos) := by
  rw [select_def] at h
  obtain ⟨target, selected, total, fWith, fNo, required, h2, h4, h5, h6, h7, h8, hs⟩ :=
    select_model (ca := @checkArguments) (spk := @satPerKvB) (pt := @paymentTarget) (css := @checkSpendableSet)
      (feeF := @fee) (takeF := @take) (cad := @checkedAdd) (cst := @checkStandardSize) (dt := @dustThreshold) h
  obtain ⟨htarget0, htarget_nonneg⟩ := paymentTargetFrom_ok h2
  have htarget : target = paymentTotal payments.toList := by omega
  obtain ⟨taken, htaken, htotal, hmax, hmem⟩ := take_ok h4
  have hsel : selected.toList = taken := by rw [htaken]; rfl
  have htot : total = coinTotal selected.toList := by rw [hsel, htotal]; omega
  have htotal_le : total ≤ maxI := hmax (by decide)
  obtain ⟨hfW, hfW0, hfWmax⟩ := fee_ok h5
  obtain ⟨hfN, hfN0, _⟩ := fee_ok h6
  obtain ⟨hreq, _⟩ := checkedAdd_ok h7
  have hmaxI := maxI_lt
  have hdust := dustThreshold_nonneg changeScript
  have hmember : ∀ u, u ∈ selected → u ∈ utxos := by
    intro u hu
    have h1 := hmem u (by rw [← hsel]; exact Array.mem_toList_iff.mpr hu)
    exact Array.mem_toList_iff.mp (List.mem_mergeSort.mp h1)
  rcases hs with ⟨hd, rfl⟩ | ⟨hd, rfl⟩
  · have hfee : (Int64.ofInt fWith).toInt = fWith := Int64.toInt_ofInt_of_le (by omega) (by omega)
    have hchange : (Int64.ofInt (total - target - fWith)).toInt = total - target - fWith :=
      Int64.toInt_ofInt_of_le (by omega) (by omega)
    refine ⟨?_, ?_, ?_, ?_, hmember⟩
    · simp only [Option.map_some, Option.getD_some]
      rw [hfee, hchange, ← htot, ← htarget]; omega
    · simp only []; rw [hfee]; exact hfW0
    · intro c hc
      simp only [Option.some.injEq] at hc
      rw [← hc, hchange]
      exact ⟨hd, by simp only []; rw [hfee, hfW]⟩
    · intro hnone; simp only [reduceCtorEq] at hnone
  · have hfee : (Int64.ofInt (total - target)).toInt = total - target :=
      Int64.toInt_ofInt_of_le (by omega) (by omega)
    refine ⟨?_, ?_, ?_, ?_, hmember⟩
    · simp only [Option.map_none, Option.getD_none]
      rw [hfee, ← htot, ← htarget]; omega
    · simp only []; rw [hfee]; omega
    · intro c hc; simp only [reduceCtorEq] at hc
    · intro _; simp only []; rw [hfee, ← hfN]; omega

end Winnow.Proofs.Selection
