import Submissions.UpperCompressions.AuthExpectedAssembly
import Submissions.UpperCompressions.WideAuthWitness

/-! Authentication before signing and after signing failure, with only actual
expected non-index paid queries charged in either stage. -/
open OracleSpec OracleComp OracleComp.EvalDist ENNReal
noncomputable section
open scoped Classical
set_option maxRecDepth 10000
namespace OptimalOTS.WeightedConstruction.WideForest
open OptimalOTS.Dag Name WeightedReplacement
set_option maxHeartbeats 800000
attribute [local irreducible] hashBits blockBits msgBits Finset.univ Finset.filter

theorem authPotential_charge_none (pk : BitVec 128)
    {T : Finset Rec} (hT : T ⊆ fiberA pk) (c : Cache) (q : Query) (hq : c q = none) :
    (∑ u, (Fintype.card (BitVec hashBits) : ℝ≥0∞)⁻¹ *
      authPotential T none (c.cacheQuery q u)) ≤
      authPotential T none c + authRate * sumW (fiberA pk) * queryCost (.inr q) := by
  simp only [authPotential_eq, fHid_none, mul_add, Finset.sum_add_distrib]
  have hh := (hits_avg_le T kc c q).trans
    (add_le_add_right (hits_charge_A' pk hT q) _)
  have hs := (spr_avg_le T c q hq).trans
    (add_le_add_right (mul_le_mul_right (sumW_mono hT) (ε * blockCost q.1)) _)
  have hc := mul_le_mul_right (authentication_charge_budget q) (sumW (fiberA pk))
  calc
    _ ≤ ((∑ ξ ∈ T, w * ind (Cache.Hits c (kc ξ))) + ε * sumW (fiberA pk)) +
        ((∑ ξ ∈ T, w * ind (Spr c ξ)) + (ε * blockCost q.1) * sumW (fiberA pk)) :=
      add_le_add hh hs
    _ = ((∑ ξ ∈ T, w * ind (Cache.Hits c (kc ξ))) +
        (∑ ξ ∈ T, w * ind (Spr c ξ))) +
        (ε + ε * blockCost q.1) * sumW (fiberA pk) := by ring
    _ ≤ _ := by
      apply add_le_add_right
      simpa only [authRate, queryCost, mul_assoc, mul_comm, mul_left_comm] using hc

theorem presign_auth_query_expected (pk : BitVec 128)
    {T : Finset Rec} (hT : T ⊆ fiberA pk)
    (isIndex : Spec.Domain → Prop)
    (hindex : ∀ q, isIndex (.inr q) → ∃ u : EncInput, q = encQuery u)
    (t : Spec.Domain) (c : Cache) :
    E ((oracleImpl t).run c) (fun p => authPotential T none p.2) ≤
      authPotential T none c +(authRate*sumW (fiberA pk))*otherPaid isIndex t := by
  cases t with
  | inl n =>
    rw [oracleImpl_run_inl, E_bind]
    simp only [E_pure, otherPaid, queryCost]
    split_ifs <;> simpa using E_const_le (liftM (unifSpec.query n) : ProbComp (unifSpec.Range n))
      (authPotential T none c)
  | inr q =>
    cases hc : c q with
    | some u =>
      rw [oracleImpl_run_inr_some hc, E_pure]
      exact le_self_add
    | none =>
      rw [oracleImpl_run_inr_none hc, E_bind, E_uniform]
      simp only [E_pure]
      by_cases hi : isIndex (.inr q)
      · obtain ⟨u,rfl⟩ := hindex q hi
        rw [authPotential_index, otherPaid, if_pos hi, mul_zero, add_zero]
      · rw [otherPaid, if_neg hi]
        exact authPotential_charge_none pk hT c q hc

theorem presign_auth_expected {α : Type} (pk : BitVec 128)
    {T : Finset Rec} (hT : T ⊆ fiberA pk)
    (isIndex : Spec.Domain → Prop)
    (hindex : ∀ q, isIndex (.inr q) → ∃ u : EncInput, q = encQuery u)
    (oa : OracleComp Spec α) (c : Cache) :
    E (run oa c) (fun p => authPotential T none p.2) ≤
      authPotential T none c +
        (authRate*sumW (fiberA pk))*expectedCharge (otherPaid isIndex) oa c :=
  WeightedExpectedCharge.master_expected (authPotential T none) (otherPaid isIndex)
    (authRate*sumW (fiberA pk)) (presign_auth_query_expected pk hT isIndex hindex) oa c

theorem authPotential_empty (T : Finset Rec) (A? : Option (Finset Name)) :
    authPotential T A? ∅ = 0 := by
  simp [authPotential, ind, Cache.not_hits_empty, not_spr_empty]

/-- This is the actual attacker's choose program, on the reduced initially empty
cache. Hidden keygen cache removal is a separate identical-until-bad step. -/
theorem stageA_auth_expected (A : forestScheme.toAlgorithm.Adversary)
    (pk : BitVec 128) (isIndex : Spec.Domain → Prop)
    (hindex : ∀ q, isIndex (.inr q) → ∃ u : EncInput, q = encQuery u) :
    E (run (A.choose pk) ∅) (fun p => authPotential (fiberA pk) none p.2) ≤
      (authRate*sumW (fiberA pk))*expectedCharge (otherPaid isIndex) (A.choose pk) ∅ := by
  simpa only [authPotential_empty, zero_add] using
    presign_auth_expected pk (Finset.Subset.refl _) isIndex hindex (A.choose pk) ∅

/-- No-signature continuation: index-only private signing work preserves all
graph events, and public continuation charges only its expected non-index cost. -/
theorem no_sign_auth_expected {α : Type} (pk : BitVec 128)
    (T : Finset Rec) (hT : T ⊆ fiberA pk)
    (d d' : Cache) (hd' : IndexExtension d d')
    (hTd : ∀ ξ ∈ T, ¬ Cache.Hits d (kc ξ))
    (isIndex : Spec.Domain → Prop)
    (hindex : ∀ q, isIndex (.inr q) → ∃ u : EncInput, q = encQuery u)
    (oa : OracleComp Spec α) :
    (∑ ξ ∈ T, w*E (run oa d')
      (fun p => ind (Cache.Hits p.2 (kc ξ))+ind (Spr p.2 ξ))) ≤
      (∑ ξ ∈ T, w*ind (Spr d ξ)) +
        (authRate*sumW (fiberA pk))*expectedCharge (otherPaid isIndex) oa d' := by
  have hinit := authPotential_after_sign hd' T none hTd ∅ (fun ξ _ => fExp_none ξ)
  rw [Cache.extend_empty] at hinit
  have hsum : (∑ ξ ∈ T, w*E (run oa d')
      (fun p => ind (Cache.Hits p.2 (kc ξ))+ind (Spr p.2 ξ))) =
      E (run oa d') (fun p => authPotential T none p.2) := by
    simp only [authPotential, fHid_none]
    rw [E_finsetSum]
    exact Finset.sum_congr rfl fun ξ _ => E_const_mul _ _ _
  rw [hsum]
  exact (presign_auth_expected pk hT isIndex hindex oa d').trans_eq (by rw [hinit])

/-- Actual strong forgery after a failed signature has only graph badness after
the hidden cache is removed; no index-forgery event is introduced. -/
theorem stB_iub_none (A : forestScheme.toAlgorithm.Adversary)
    (ξ : Rec) (m₁ : Message) (st : A.State) (d d' : Cache)
    (hd' : IndexExtension d d') (hξ : ¬ Cache.Hits d (kc ξ)) :
    E (run (stB A (pkOf ξ) m₁ st none) (Cache.extend d' (kc ξ))) successValue ≤
      E (run (stB A (pkOf ξ) m₁ st none) d')
        (fun p => ind (Cache.Hits p.2 (kc ξ))+ind (Spr p.2 ξ)) := by
  have h := graph_iub (stB A (pkOf ξ) m₁ st none) ξ none d d' hd' hξ
  simp only [fExp_none, Cache.extend_empty, fHid_none] at h
  refine h.trans ?_
  apply expectedValue_mono_of_support
  intro p hp
  by_cases hh : Cache.Hits p.2 (kc ξ)
  · rw [if_pos hh, ind_of hh]
    exact le_self_add
  · rw [if_neg hh, ind_not hh, zero_add]
    by_cases hok : p.1 = true
    · rw [successValue, if_pos hok]
      rcases stB_events_none A ξ m₁ st d' p hp hok with hs | hh'
      · rw [ind_of hs]
      · exact absurd hh' hh
    · rw [successValue, if_neg hok]
      exact zero_le

/-- The actual failed-signature success branch on a fixed public-key record
fiber is now reduced to pre-sign spurious mass and its own expected graph cost. -/
theorem failed_sign_success_expected (A : forestScheme.toAlgorithm.Adversary)
    (pk : BitVec 128) (T : Finset Rec) (hT : T ⊆ fiberA pk)
    (m₁ : Message) (st : A.State) (d d' : Cache)
    (hd' : IndexExtension d d') (hTd : ∀ ξ ∈ T, ¬ Cache.Hits d (kc ξ))
    (isIndex : Spec.Domain → Prop)
    (hindex : ∀ q, isIndex (.inr q) → ∃ u : EncInput, q = encQuery u) :
    (∑ ξ ∈ T, w*E (run (stB A (pkOf ξ) m₁ st none)
      (Cache.extend d' (kc ξ))) successValue) ≤
      (∑ ξ ∈ T, w*ind (Spr d ξ)) +
        (authRate*sumW (fiberA pk))*
          expectedCharge (otherPaid isIndex) (stB A pk m₁ st none) d' := by
  have hpks := pkOf_of_subset_fiberA hT
  calc
    _ ≤ ∑ ξ ∈ T, w*E (run (stB A (pkOf ξ) m₁ st none) d')
        (fun p => ind (Cache.Hits p.2 (kc ξ))+ind (Spr p.2 ξ)) :=
      Finset.sum_le_sum fun ξ hξ =>
        mul_le_mul_right (stB_iub_none A ξ m₁ st d d' hd' (hTd ξ hξ)) w
    _ = ∑ ξ ∈ T, w*E (run (stB A pk m₁ st none) d')
        (fun p => ind (Cache.Hits p.2 (kc ξ))+ind (Spr p.2 ξ)) := by
      apply Finset.sum_congr rfl
      intro ξ hξ
      rw [hpks ξ hξ]
    _ ≤ _ := no_sign_auth_expected pk T hT d d' hd' hTd isIndex hindex _

#print axioms stageA_auth_expected
#print axioms no_sign_auth_expected
#print axioms stB_iub_none
#print axioms failed_sign_success_expected
end OptimalOTS.WeightedConstruction.WideForest
