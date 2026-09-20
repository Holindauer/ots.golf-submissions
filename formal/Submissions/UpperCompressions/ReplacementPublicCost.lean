import Submissions.UpperCompressions.ReplacementHybridPrefix

/-! Public query accounting in the original shared-cache execution. Queries
are charged even when the implementation cache already contains their answers. -/

open OracleSpec OracleComp OracleComp.EvalDist ENNReal
open OptimalOTS
namespace WeightedReplacement
noncomputable section
open scoped Classical BigOperators
local instance (priority := 100000) stagedLocal_ReplacementPublicCost_1 {α : Type*} : DecidableEq α := Classical.decEq α
attribute [local irreducible] hashBits blockBits msgBits signBudget

def expectedCharge {α : Type} (charge : Spec.Domain → ℝ≥0∞) (oa : OracleComp Spec α) : Cache → ℝ≥0∞ :=
  OracleComp.construct (fun _ _ => 0)
    (fun t _ rec c => charge t + E ((oracleImpl t).run c) (fun p => rec p.1 p.2)) oa

@[simp] theorem expectedCharge_pure {α : Type} (charge : Spec.Domain → ℝ≥0∞) (a : α) (c : Cache) :
    expectedCharge charge (pure a) c = 0 := by simp [expectedCharge]

theorem expectedCharge_query {α : Type} (charge : Spec.Domain → ℝ≥0∞) (t : Spec.Domain)
    (k : Spec.Range t → OracleComp Spec α) (c : Cache) :
    expectedCharge charge (liftM (Spec.query t) >>= k) c =
      charge t + E ((oracleImpl t).run c) (fun p => expectedCharge charge (k p.1) p.2) := by
  simp [expectedCharge]

theorem expectedCharge_add {α : Type} (a b : Spec.Domain → ℝ≥0∞) (oa : OracleComp Spec α) (c : Cache) :
    expectedCharge (fun t => a t+b t) oa c = expectedCharge a oa c + expectedCharge b oa c := by
  induction oa using OracleComp.inductionOn generalizing c with
  | pure x => simp
  | query_bind t k ih =>
    simp only [expectedCharge_query]
    simp_rw [ih]
    simp only [E, expectedValue_def, mul_add, ENNReal.tsum_add]
    ring

theorem expectedCharge_mono {α : Type} (a b : Spec.Domain → ℝ≥0∞)
    (hab : ∀ t, a t ≤ b t) (oa : OracleComp Spec α) (c : Cache) :
    expectedCharge a oa c ≤ expectedCharge b oa c := by
  induction oa using OracleComp.inductionOn generalizing c with
  | pure x => simp
  | query_bind t k ih =>
    rw [expectedCharge_query, expectedCharge_query]
    exact add_le_add (hab t) (E_mono _ (fun p => ih p.1 p.2))

theorem expectedCharge_budget {α : Type} (charge : Spec.Domain → ℝ≥0∞) (rate : ℝ≥0∞)
    (hc : ∀ t, charge t ≤ rate * queryCost t) (oa : OracleComp Spec α)
    (b : ℕ) (hB : CostAtMost oa b) (c : Cache) : expectedCharge charge oa c ≤ rate*b := by
  induction oa using OracleComp.inductionOn generalizing b c with
  | pure x => simp
  | query_bind t k ih =>
    unfold CostAtMost at hB
    rw [isQueryBound_query_bind_iff] at hB
    rw [expectedCharge_query]
    calc
      _ ≤ rate*queryCost t + E ((oracleImpl t).run c) (fun _ => rate*((b-queryCost t:ℕ):ℝ≥0∞)) :=
        add_le_add (hc t) (E_mono _ (fun p => ih p.1 _ (hB.2 p.1) p.2))
      _ ≤ rate*queryCost t + rate*((b-queryCost t:ℕ):ℝ≥0∞) := add_le_add le_rfl (E_const_le _ _)
      _ = rate*b := by rw [← mul_add, ← Nat.cast_add, Nat.add_sub_of_le hB.1]

def publicHit {α : Type} (u : Query) (oa : OracleComp Spec α) : Cache → ℝ≥0∞ :=
  OracleComp.construct (fun _ _ => 0)
    (fun t _ rec c => match t with
      | .inl n => E ((oracleImpl (.inl n)).run c) (fun p => rec p.1 p.2)
      | .inr q => if q = u then 1 else E ((oracleImpl (.inr q)).run c) (fun p => rec p.1 p.2)) oa

@[simp] theorem publicHit_pure {α : Type} (u : Query) (a : α) (c : Cache) :
    publicHit u (pure a) c = 0 := by simp [publicHit]

theorem publicHit_query {α : Type} (u : Query) (t : Spec.Domain)
    (k : Spec.Range t → OracleComp Spec α) (c : Cache) :
    publicHit u (liftM (Spec.query t) >>= k) c =
      if t = .inr u then 1 else E ((oracleImpl t).run c) (fun p => publicHit u (k p.1) p.2) := by
  cases t <;> simp [publicHit]

theorem publicHit_query_le {α : Type} (u : Query) (t : Spec.Domain)
    (k : Spec.Range t → OracleComp Spec α) (c : Cache) :
    publicHit u (liftM (Spec.query t) >>= k) c ≤
      (if t = .inr u then 1 else 0) + E ((oracleImpl t).run c) (fun p => publicHit u (k p.1) p.2) := by
  cases t with
  | inl n => simp [publicHit]
  | inr q =>
    by_cases hqu : q = u
    · simp [publicHit, hqu]
    · simp [publicHit, hqu]

/-- publicHit is exactly the probability that the actual mixed-oracle prefix
stops before answering u. Trace initialization does not affect this event. -/
theorem publicHit_eq_prefix {α : Type} (u : Query) (oa : OracleComp Spec α) (c : Cache) (tr : PublicTrace) :
    publicHit u oa c = E (hybridPrefix u oa c tr) (fun p => if p.1 = none then 1 else 0) := by
  induction oa using OracleComp.inductionOn generalizing c tr with
  | pure a => simp [publicHit, hybridPrefix_pure, E_pure]
  | query_bind t k ih =>
    cases t with
    | inl n =>
      rw [hybridPrefix_unif, publicHit_query]
      simp only [reduceCtorEq, if_false, oracleImpl_run_inl, E_bind, E_pure]
      apply congrArg
      funext a
      exact ih a c _
    | inr q =>
      by_cases hqu : q = u
      · subst q
        rw [publicHit_query u (.inr u) k c, hybridPrefix_target]
        simp [E_pure]
      · rw [hybridPrefix_hash u q hqu, E_bind]
        simp only [publicHit_query, Sum.inr.injEq, if_neg hqu]
        apply congrArg
        funext p
        exact ih p.1 p.2 _

def exposureCharge {D : Type} [Fintype D] (e : D → Query) (t : Spec.Domain) : ℝ≥0∞ :=
  ∑ d, if t = .inr (e d) then 1 else 0

/-- Sum of first-public-hit probabilities is bounded by the expected number of
paid queries to those inputs. Repeated queries only increase the upper bound. -/
theorem publicHit_sum_le {D α : Type} [Fintype D] (e : D → Query)
    (oa : OracleComp Spec α) (c : Cache) :
    (∑ d, publicHit (e d) oa c) ≤ expectedCharge (exposureCharge e) oa c := by
  induction oa using OracleComp.inductionOn generalizing c with
  | pure a => simp
  | query_bind t k ih =>
    rw [expectedCharge_query]
    calc
      _ ≤ ∑ d, ((if t = .inr (e d) then 1 else 0) +
          E ((oracleImpl t).run c) (fun p => publicHit (e d) (k p.1) p.2)) :=
        Finset.sum_le_sum (fun d _ => publicHit_query_le (e d) t k c)
      _ = exposureCharge e t + E ((oracleImpl t).run c) (fun p => ∑ d, publicHit (e d) (k p.1) p.2) := by
        rw [Finset.sum_add_distrib]
        apply congrArg (exposureCharge e t + ·)
        exact (expectedValue_finsetSum ((oracleImpl t).run c) Finset.univ
          (fun d p => publicHit (e d) (k p.1) p.2)).symm
      _ ≤ _ := add_le_add le_rfl (E_mono _ (fun p : Spec.Range t × Cache => ih p.1 p.2))

theorem exposureCharge_eq {D : Type} [Fintype D] (e : D → Query) (he : Function.Injective e)
    (t : Spec.Domain) : exposureCharge e t = if ∃ d, t = .inr (e d) then 1 else 0 := by
  by_cases ht : ∃ d, t = .inr (e d)
  · obtain ⟨d, hd⟩ := ht
    have hh (d' : D) : t = .inr (e d') ↔ d' = d := by
      constructor
      · intro h
        exact (he (Sum.inr.inj (hd.symm.trans h))).symm
      · rintro rfl
        exact hd
    simp [exposureCharge, hh]
  · have hh : ∀ d, t ≠ .inr (e d) := by simpa using ht
    simp [exposureCharge, hh]

def indexPaid (isIndex : Spec.Domain → Prop) (t : Spec.Domain) : ℝ≥0∞ :=
  if isIndex t then queryCost t else 0

def otherPaid (isIndex : Spec.Domain → Prop) (t : Spec.Domain) : ℝ≥0∞ :=
  if isIndex t then 0 else queryCost t

theorem exposureCharge_le_indexPaid {D : Type} [Fintype D] (e : D → Query)
    (he : Function.Injective e) (isIndex : Spec.Domain → Prop)
    (hi : ∀ d, isIndex (.inr (e d))) (hpaid : ∀ d, 1 ≤ queryCost (.inr (e d))) :
    ∀ t, exposureCharge e t ≤ indexPaid isIndex t := by
  intro t
  rw [exposureCharge_eq e he]
  split_ifs with ht
  · obtain ⟨d,rfl⟩ := ht
    rw [indexPaid, if_pos (hi d)]
    exact_mod_cast hpaid d
  · exact bot_le

theorem publicHit_sum_le_indexPaid {D α : Type} [Fintype D] (e : D → Query)
    (he : Function.Injective e) (isIndex : Spec.Domain → Prop)
    (hi : ∀ d, isIndex (.inr (e d))) (hpaid : ∀ d, 1 ≤ queryCost (.inr (e d)))
    (oa : OracleComp Spec α) (c : Cache) :
    (∑ d, publicHit (e d) oa c) ≤ expectedCharge (indexPaid isIndex) oa c :=
  (publicHit_sum_le e oa c).trans (expectedCharge_mono _ _
    (exposureCharge_le_indexPaid e he isIndex hi hpaid) oa c)

theorem paid_split {α : Type} (isIndex : Spec.Domain → Prop) (oa : OracleComp Spec α) (c : Cache) :
    expectedCharge (indexPaid isIndex) oa c + expectedCharge (otherPaid isIndex) oa c =
      expectedCharge (fun t => queryCost t) oa c := by
  rw [← expectedCharge_add]
  congr 1
  funext t
  simp [indexPaid, otherPaid]
  split_ifs <;> simp

/-- Index and graph exposure costs share one pathwise budget. Neither term
receives a separate copy of the full budget. -/
theorem paid_shared_budget {α : Type} (isIndex : Spec.Domain → Prop) (a b : ℝ≥0∞)
    (oa : OracleComp Spec α) (c : Cache) (B : ℕ) (hB : CostAtMost oa B) :
    a*expectedCharge (indexPaid isIndex) oa c + b*expectedCharge (otherPaid isIndex) oa c ≤
      max a b * B := by
  calc
    _ ≤ max a b * expectedCharge (indexPaid isIndex) oa c +
        max a b * expectedCharge (otherPaid isIndex) oa c :=
      add_le_add (mul_le_mul' (le_max_left _ _) le_rfl) (mul_le_mul' (le_max_right _ _) le_rfl)
    _ = max a b * expectedCharge (fun t => queryCost t) oa c := by rw [← mul_add, paid_split]
    _ ≤ _ := mul_le_mul' le_rfl (by
      simpa using expectedCharge_budget (fun t => queryCost t) 1 (fun _ => by simp) oa B hB c)

#print axioms publicHit_eq_prefix
#print axioms publicHit_sum_le
#print axioms publicHit_sum_le_indexPaid
#print axioms paid_shared_budget

end
end WeightedReplacement
