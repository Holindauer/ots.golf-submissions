import Submissions.UpperCompressions.WideLargeClock
import Submissions.UpperCompressions.WideLargeScalar

/-! Final large-budget strong-success bound for the actual typed experiment. -/
open OracleSpec OracleComp OracleComp.EvalDist ENNReal
noncomputable section
open scoped Classical BigOperators
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace OptimalOTS.WeightedConstruction.WideForest
open OptimalOTS.Dag Name WeightedReplacement WeightedSampling WideInitialGame
open WeightedReference WeightedBudgetClosure
attribute [local irreducible] Finset.univ Finset.filter

/-- All probabilistic premises are discharged for the original strong-success
experiment. The remaining hypotheses are its protected pathwise budget and the
large-budget numerical interval. -/
theorem actual_large_security (A : forestScheme.toAlgorithm.Adversary) {B : ℕ}
    (hB : CostAtMost (forestScheme.toAlgorithm.experiment A) B)
    (hBN : (2:ℝ)^86/10 ≤ (B:ℝ)) (hcap : (B:ℝ) ≤ (2:ℝ)^127) :
    E (run (forestScheme.toAlgorithm.experiment A) ∅) successValue ≤
      ENNReal.ofReal ((991:ℝ)/1000*kappa*(B:ℝ)) := by
  have hex := global_actual_payoff_expanded A hB (largeGood A B) (fun _ _ h => h.1)
  have hbad := large_bad_clock_le A hB hBN
  have hh := large_hazard_clock_le A B
  have he := all_exception_margin_ennreal B (keygen_remaining A hB).1 hcap
  have herr : weightedClock A B (badGate A (largeGood A B))+
      (1+(B:ℝ≥0∞))*(2:ℝ≥0∞)⁻¹^761 ≤ ENNReal.ofReal (kappa*(B:ℝ)/1000) :=
    (add_le_add hbad le_rfl).trans he
  rw [preAuth_eq] at hex
  have hn := large_shared_ennreal B (weightedClock A B (countClock A)) (preOther A)
    (weightedClock A B (postRemaining A))
    (weightedClock A B (gatedHazard A (largeGood A B)))
    (weightedClock A B (badGate A (largeGood A B))+(1+(B:ℝ≥0∞))*(2:ℝ≥0∞)⁻¹^761)
    (global_count_other_post_le A hB) hh herr
  exact hex.trans (by simpa only [add_assoc] using hn)

theorem actual_large_security_strict (A : forestScheme.toAlgorithm.Adversary) {B : ℕ}
    (hB : CostAtMost (forestScheme.toAlgorithm.experiment A) B)
    (hBN : (2:ℝ)^86/10 ≤ (B:ℝ)) (hcap : (B:ℝ) ≤ (2:ℝ)^127) :
    E (run (forestScheme.toAlgorithm.experiment A) ∅) successValue <
      ENNReal.ofReal (kappa*(B:ℝ)) := by
  have hpos : 0 < kappa*(B:ℝ) := by
    have hk : 0 < kappa := by norm_num [kappa]
    have hb : 0 < (B:ℝ) := lt_of_lt_of_le (by norm_num) hBN
    exact mul_pos hk hb
  apply (actual_large_security A hB hBN hcap).trans_lt
  apply (ENNReal.ofReal_lt_ofReal_iff hpos).mpr
  nlinarith

#print axioms actual_large_security
#print axioms actual_large_security_strict
end OptimalOTS.WeightedConstruction.WideForest
