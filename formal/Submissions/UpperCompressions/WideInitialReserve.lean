import Submissions.UpperCompressions.WideInitialBudget
import Submissions.UpperCompressions.ReplacementPrefixReserve

/-! The actual adaptive choose program cannot spend the995 keygen cost or any
of the all-L signing reserve, even on a raw oracle-answer path. -/
open OracleSpec OracleComp OracleComp.EvalDist ENNReal
noncomputable section
open scoped Classical
set_option maxRecDepth 10000
set_option maxHeartbeats 800000
namespace OptimalOTS.WeightedConstruction.WideInitialGame
open OptimalOTS.Dag WideForest WideForest.Name WeightedReplacement WeightedSampling
attribute [local irreducible] Finset.univ Finset.filter WeightedResearch92.classes
variable (A : forestScheme.toAlgorithm.Adversary)

theorem afterChoose_reserve (pk : PublicKey) (ξ : Rec) (x : Message × A.State)
    (b : ℕ) (hB : CostAtMost (afterChoose A pk (graph.evalRec ξ) x) b) : signBudget ≤ b := by
  rw [afterChoose_loop] at hB
  exact (loop_reserve 86 WeightedSchedule.decode WeightedSchedule.tier x.1 index86_cost signBudget
    (fun s => stB A pk x.1 x.2 (signatureFromWinner ξ s)) b hB).1

theorem choose_reserved_budget {B : ℕ}
    (hB : CostAtMost (forestScheme.toAlgorithm.experiment A) B) (pk : PublicKey) :
    signBudget ≤ B-995 ∧ CostAtMost (A.choose pk) (B-995-signBudget) := by
  obtain ⟨ξ,hξ⟩ := fiber_nonempty pk
  have hpk := pkOf_of_subset_fiberA (Finset.Subset.refl _) ξ hξ
  have h := (keygen_remaining A hB).2 ξ
  have hh : CostAtMost (A.choose pk >>= afterChoose A pk (graph.evalRec ξ)) (B-995) := by
    simpa only [afterKeygen,hpk] using h
  exact costAtMost_prefix_reserved (A.choose pk) (afterChoose A pk (graph.evalRec ξ)) signBudget
    (fun x b hb => afterChoose_reserve A pk ξ x b hb) (B-995) hh

theorem experiment_full_reserve {B : ℕ}
    (hB : CostAtMost (forestScheme.toAlgorithm.experiment A) B) : 995+signBudget ≤ B := by
  have hk := (keygen_remaining A hB).1
  have hs := (choose_reserved_budget A hB 0).1
  omega

#print axioms choose_reserved_budget
#print axioms experiment_full_reserve
end OptimalOTS.WeightedConstruction.WideInitialGame
