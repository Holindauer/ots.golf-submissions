import Submissions.UpperCompressions.ActualGamePayoff

/-! Preserve the actual conditional success cap before expanding empirical
payoffs. A combined Good/large-deviation exception is therefore paid once. -/
open OracleSpec OracleComp OracleComp.EvalDist ENNReal
noncomputable section
open scoped Classical
set_option maxRecDepth 10000
namespace OptimalOTS.WeightedConstruction.WideForest
open OptimalOTS.Dag Name WeightedReplacement WeightedSampling WideInitialGame
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Finset.univ Finset.filter

theorem conditional_le_fiber (A : forestScheme.toAlgorithm.Adversary) (pk : PublicKey)
    (x : Message × A.State) (c : Cache) : conditional A pk x c ≤ sumW (fiberA pk) := by
  unfold conditional sumW
  apply Finset.sum_le_sum
  intro ξ _
  calc
    _ ≤ w*1 := by
      apply mul_le_mul_right
      split_ifs
      · exact zero_le
      · exact E_le_one _ successValue_le_one
    _ = _ := mul_one _

def gatedContinuationPayoff (A : forestScheme.toAlgorithm.Adversary)
    (good : PublicKey → ((Message × A.State) × Cache × ℕ) → Prop)
    (pk : PublicKey) (r : (Message × A.State) × Cache × ℕ) : ℝ≥0∞ :=
  sumW (fiberA pk) * (if good pk r then
    signerAverage r.1.1 r.2.1 signBudget (winnerReplay r.2.1 r.1.1) +
      (r.2.2-signBudget : ℕ)*(authRate+signerAverage r.1.1 r.2.1 signBudget winnerExcess)
    else 1)

theorem conditional_supported_gated (A : forestScheme.toAlgorithm.Adversary) {B : ℕ}
    (hB : CostAtMost (forestScheme.toAlgorithm.experiment A) B)
    (good : PublicKey → ((Message × A.State) × Cache × ℕ) → Prop)
    (pk : PublicKey) (r : (Message × A.State) × Cache × ℕ)
    (hr : r ∈ support (runRemaining (A.choose pk) ∅ (B-995))) :
    conditional A pk r.1 r.2.1 ≤ survivingSpr pk r.2.1 + gatedContinuationPayoff A good pk r := by
  by_cases hg : good pk r
  · rw [gatedContinuationPayoff,if_pos hg]
    exact conditional_actual_master A pk r.1.1 r.1.2 r.2.1 (r.2.2-signBudget)
      (supportedPostBudget_of_experiment A hB pk r hr)
  · rw [gatedContinuationPayoff,if_neg hg,mul_one]
    exact (conditional_le_fiber A pk r.1 r.2.1).trans le_add_self

/-- Full actual strong-success probability with the empirical/large-deviation
split made at the conditional success cap. An arbitrary conjunction of bad
conditions may be represented by `¬good`, without multiplying it by a budget. -/
theorem global_actual_game_payoff_gated (A : forestScheme.toAlgorithm.Adversary) {B : ℕ}
    (hB : CostAtMost (forestScheme.toAlgorithm.experiment A) B)
    (good : PublicKey → ((Message × A.State) × Cache × ℕ) → Prop) :
    E (run (forestScheme.toAlgorithm.experiment A) ∅) successValue ≤
      (∑ pk : PublicKey, (authRate*sumW (fiberA pk))*
        expectedCharge (otherPaid (isIndexLength (msgBits+86))) (A.choose pk) ∅) +
      ∑ pk : PublicKey, E (runRemaining (A.choose pk) ∅ (B-995))
        (gatedContinuationPayoff A good pk) := by
  apply global_payoff_clock A (B-995) (isIndexLength (msgBits+86))
    (fun q hq => exists_encQuery_of_length q hq) (gatedContinuationPayoff A good)
  exact conditional_supported_gated A hB good

#print axioms conditional_le_fiber
#print axioms global_actual_game_payoff_gated
end OptimalOTS.WeightedConstruction.WideForest
