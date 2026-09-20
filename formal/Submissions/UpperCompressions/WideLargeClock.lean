import Submissions.UpperCompressions.ActualPayoffExpansion
import Submissions.UpperCompressions.WideHazardTerminal
import Submissions.UpperCompressions.WideDistinctCharge

/-! The actual large-budget good event and the same public spent/remaining clock. -/
open OracleSpec OracleComp OracleComp.EvalDist ENNReal
noncomputable section
open scoped Classical BigOperators
set_option maxRecDepth 10000
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace OptimalOTS.WeightedConstruction.WideForest
open OptimalOTS.Dag Name WeightedReplacement WeightedSampling WideInitialGame
open WideDomains WeightedReference WeightedBudgetClosure
attribute [local irreducible] Finset.univ Finset.filter

def largeGood (A : forestScheme.toAlgorithm.Adversary) (B : ℕ)
    (_pk : PublicKey) (r : (Message × A.State) × Cache × ℕ) : Prop :=
  WideEmpirical.Good r.2.1 ∧ ¬WideHazard.LargeBad B r.2.1

def countClock (A : forestScheme.toAlgorithm.Adversary)
    (_pk : PublicKey) (r : (Message × A.State) × Cache × ℕ) : ℝ≥0∞ :=
  WideHazard.globalCount r.2.1

def preOther (A : forestScheme.toAlgorithm.Adversary) : ℝ≥0∞ :=
  ∑ pk : PublicKey, sumW (fiberA pk)*
    expectedCharge (otherPaid (isIndexLength (msgBits+86))) (A.choose pk) ∅

theorem preAuth_eq (A : forestScheme.toAlgorithm.Adversary) :
    preAuth A = ENNReal.ofReal (kappa/2)*preOther A := by
  unfold preAuth preOther
  rw [authRate_ofReal,Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem choose_count_other_post_le (A : forestScheme.toAlgorithm.Adversary) {B : ℕ}
    (hB : CostAtMost (forestScheme.toAlgorithm.experiment A) B) (pk : PublicKey) :
    E (runRemaining (A.choose pk) ∅ (B-995)) (countClock A pk)+
      expectedCharge (otherPaid (isIndexLength (msgBits+86))) (A.choose pk) ∅+
      E (runRemaining (A.choose pk) ∅ (B-995)) (postRemaining A pk) ≤ B := by
  have hd := distinct_other_le_expected_paid (A.choose pk) ∅ (fun _ _ => rfl)
  rw [← runRemaining_project (A.choose pk) ∅ (B-995),E_map] at hd
  have hh := (add_le_add hd (le_refl
    (E (runRemaining (A.choose pk) ∅ (B-995)) (postRemaining A pk)))).trans
      (choose_spent_post_remaining_le A hB pk)
  exact hh.trans (by exact_mod_cast (Nat.sub_le (B-995) signBudget).trans (Nat.sub_le B 995))

theorem global_count_other_post_le (A : forestScheme.toAlgorithm.Adversary) {B : ℕ}
    (hB : CostAtMost (forestScheme.toAlgorithm.experiment A) B) :
    weightedClock A B (countClock A)+preOther A+
      weightedClock A B (postRemaining A) ≤ B := by
  unfold weightedClock preOther
  rw [← Finset.sum_add_distrib,← Finset.sum_add_distrib]
  calc
    _ ≤ ∑ pk : PublicKey, sumW (fiberA pk)*(B:ℝ≥0∞) := by
      apply Finset.sum_le_sum
      intro pk _
      simpa only [mul_add] using mul_le_mul' (le_refl (sumW (fiberA pk)))
        (choose_count_other_post_le A hB pk)
    _ = _ := by rw [← Finset.sum_mul,sum_fiber_weights,one_mul]

theorem large_bad_clock_le (A : forestScheme.toAlgorithm.Adversary) {B : ℕ}
    (hB : CostAtMost (forestScheme.toAlgorithm.experiment A) B)
    (hBN : WideHazard.N/10 ≤ (B:ℝ)) :
    weightedClock A B (badGate A (largeGood A B)) ≤
      ENNReal.ofReal (((2:ℝ)^1792)⁻¹)+ENNReal.ofReal (((2:ℝ)^512)⁻¹) := by
  have htail (pk : PublicKey) :
      E (runRemaining (A.choose pk) ∅ (B-995)) (badGate A (largeGood A B) pk) ≤
        ENNReal.ofReal (((2:ℝ)^1792)⁻¹)+ENNReal.ofReal (((2:ℝ)^512)⁻¹) := by
    have hb := AlgorithmCosts.CostAtMost.mono (choose_reserved_budget A hB pk).2
      ((Nat.sub_le (B-995) signBudget).trans (Nat.sub_le B 995))
    have h := WideHazard.actual_large_good_hazard_bound B hBN (A.choose pk) hb ∅ (fun _ _ => rfl)
    have he : E (run (A.choose pk) ∅)
        (fun p => if ¬WideEmpirical.Good p.2 ∨ WideHazard.LargeBad B p.2 then 1 else 0) =
        Pr[fun p => ¬WideEmpirical.Good p.2 ∨ WideHazard.LargeBad B p.2 | run (A.choose pk) ∅] :=
      expectedValue_ite_one _ _
    rw [← he,← runRemaining_project (A.choose pk) ∅ (B-995),E_map] at h
    convert h using 1
    congr 1
    funext r
    simp only [badGate,largeGood]
    split_ifs <;> simp_all
  calc
    _ ≤ ∑ pk : PublicKey, sumW (fiberA pk)*
        (ENNReal.ofReal (((2:ℝ)^1792)⁻¹)+ENNReal.ofReal (((2:ℝ)^512)⁻¹)) :=
      Finset.sum_le_sum fun pk _ => mul_le_mul' le_rfl (htail pk)
    _ = _ := by rw [← Finset.sum_mul,sum_fiber_weights,one_mul]

theorem large_hazard_clock_le (A : forestScheme.toAlgorithm.Adversary) (B : ℕ) :
    weightedClock A B (gatedHazard A (largeGood A B)) ≤
      ENNReal.ofReal (C*(91/100)*kappa)*weightedClock A B (countClock A)+
        ENNReal.ofReal (C*(7/100)*kappa*(B:ℝ)) := by
  have hpoint (pk : PublicKey) (r : (Message × A.State) × Cache × ℕ) :
      gatedHazard A (largeGood A B) pk r ≤
        ENNReal.ofReal (C*(91/100)*kappa)*countClock A pk r+
          ENNReal.ofReal (C*(7/100)*kappa*(B:ℝ)) := by
    by_cases hg : largeGood A B pk r
    · rw [gatedHazard,if_pos hg]
      have hh : WideHazard.hazard r.1.1 r.2.1 <
          WideHazard.alpha*(WideHazard.globalCount r.2.1:ℝ)+(7/100)*kappa*(B:ℝ) :=
        lt_of_not_ge (fun h => hg.2 ⟨r.1.1,h⟩)
      have hc : 0 ≤ C := by norm_num [C]
      have hk : 0 ≤ kappa := by norm_num [kappa]
      have h := ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hh.le hc)
      change ENNReal.ofReal (C*cacheHazard r.1.1 r.2.1) ≤ _ at h
      apply h.trans_eq
      unfold WideHazard.alpha countClock
      rw [show C*((91/100)*kappa*(WideHazard.globalCount r.2.1:ℝ)+(7/100)*kappa*(B:ℝ)) =
        (C*(91/100)*kappa)*(WideHazard.globalCount r.2.1:ℝ)+C*(7/100)*kappa*(B:ℝ) by ring,
        ENNReal.ofReal_add (by positivity) (by positivity),
        ENNReal.ofReal_mul (by positivity),ENNReal.ofReal_natCast]
    · rw [gatedHazard,if_neg hg]
      exact zero_le
  calc
    _ ≤ weightedClock A B (fun pk r =>
        ENNReal.ofReal (C*(91/100)*kappa)*countClock A pk r+
          ENNReal.ofReal (C*(7/100)*kappa*(B:ℝ))) :=
      Finset.sum_le_sum fun pk _ => mul_le_mul' le_rfl (E_mono _ (hpoint pk))
    _ = ENNReal.ofReal (C*(91/100)*kappa)*weightedClock A B (countClock A)+
        weightedClock A B (fun _ _ => ENNReal.ofReal (C*(7/100)*kappa*(B:ℝ))) := by
      rw [weightedClock_add,weightedClock_const_mul]
    _ ≤ _ := by
      apply add_le_add le_rfl
      calc
        _ ≤ ∑ pk : PublicKey, sumW (fiberA pk)*ENNReal.ofReal (C*(7/100)*kappa*(B:ℝ)) :=
          Finset.sum_le_sum fun pk _ => mul_le_mul' le_rfl (E_const_le _ _)
        _ = _ := by rw [← Finset.sum_mul,sum_fiber_weights,one_mul]

#print axioms global_count_other_post_le
#print axioms large_bad_clock_le
#print axioms large_hazard_clock_le
end OptimalOTS.WeightedConstruction.WideForest
