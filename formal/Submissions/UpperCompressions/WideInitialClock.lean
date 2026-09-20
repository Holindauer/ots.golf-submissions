import Submissions.UpperCompressions.WideInitialReserve
import Submissions.UpperCompressions.ReplacementReservedClock

/-! The actual first-stage spent budget and actual supported post-sign reserve
share the public experiment budget after995 keygen and all-L signing. -/
open OracleSpec OracleComp OracleComp.EvalDist ENNReal
noncomputable section
open scoped Classical BigOperators
set_option maxRecDepth 10000
set_option maxHeartbeats 800000
namespace OptimalOTS.WeightedConstruction.WideInitialGame
open OptimalOTS.Dag WideForest WideForest.Name WeightedReplacement WeightedSampling
attribute [local irreducible] Finset.univ Finset.filter WeightedResearch92.classes
variable (A : forestScheme.toAlgorithm.Adversary)

theorem choose_spent_post_remaining_le {B : ℕ}
    (hB : CostAtMost (forestScheme.toAlgorithm.experiment A) B) (pk : PublicKey) :
    expectedCharge (fun t => queryCost t) (A.choose pk) ∅ +
      E (runRemaining (A.choose pk) ∅ (B-995))
        (fun r => ((r.2.2-signBudget:ℕ):ℝ≥0∞)) ≤ (B-995-signBudget:ℕ) := by
  obtain ⟨ξ,hξ⟩ := fiber_nonempty pk
  have hpk := pkOf_of_subset_fiberA (Finset.Subset.refl _) ξ hξ
  have h := (keygen_remaining A hB).2 ξ
  have hh : CostAtMost (A.choose pk >>= afterChoose A pk (graph.evalRec ξ)) (B-995) := by
    simpa only [afterKeygen,hpk] using h
  exact expected_spent_reserved_remaining_le (A.choose pk) (afterChoose A pk (graph.evalRec ξ)) signBudget
    (fun x b hb => afterChoose_reserve A pk ξ x b hb) ∅ (B-995) hh

theorem sum_fiber_weights : (∑ pk : PublicKey, sumW (fiberA pk)) = 1 := by
  unfold sumW fiberA
  exact (Finset.sum_fiberwise Finset.univ pkOf (fun _ => w)).trans sum_w

/-- The same public clock after averaging over the actual public-key record
fibers. Uniform record weights total one. -/
theorem global_public_clock_le {B : ℕ}
    (hB : CostAtMost (forestScheme.toAlgorithm.experiment A) B) :
    (∑ pk : PublicKey, sumW (fiberA pk) *
      (expectedCharge (fun t => queryCost t) (A.choose pk) ∅ +
        E (runRemaining (A.choose pk) ∅ (B-995))
          (fun r => ((r.2.2-signBudget:ℕ):ℝ≥0∞)))) ≤ (B-995-signBudget:ℕ) := by
  calc
    _ ≤ ∑ pk : PublicKey, sumW (fiberA pk)*(B-995-signBudget:ℕ) :=
      Finset.sum_le_sum fun pk _ => mul_le_mul' le_rfl (choose_spent_post_remaining_le A hB pk)
    _ = _ := by rw [← Finset.sum_mul,sum_fiber_weights,one_mul]

#print axioms choose_spent_post_remaining_le
#print axioms global_public_clock_le
end OptimalOTS.WeightedConstruction.WideInitialGame
