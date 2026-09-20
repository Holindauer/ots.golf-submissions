import Submissions.UpperCompressions.WideBudgetEndpoints
import Submissions.UpperCompressions.WideAuthGame

/-! The exact protected security conclusion from two explicit actual-game
branch bounds. This module is conditional until those bounds are supplied. -/
noncomputable section
open OracleSpec OracleComp OracleComp.EvalDist ENNReal
open scoped Classical
namespace OptimalOTS.WeightedConstruction.WideSecurityClosure
open WideForest WideBudgetEndpoints WeightedReference
set_option maxRecDepth 10000
set_option maxHeartbeats 800000

theorem probTrue_eq_success (oa : OracleComp Spec Bool) :
    probTrue oa = E (run oa ∅) successValue := by
  unfold probTrue
  rw [run'_eq,probOutput_map_eq_tsum_ite,E,expectedValue_def]
  refine tsum_congr fun x => ?_
  rcases x with ⟨b,c⟩
  cases b <;> simp [successValue]

theorem security_rate (B : ℕ) :
    ENNReal.ofReal (kappa*(B:ℝ)) = (B:ℝ≥0∞)/2^securityBits := by
  rw [ENNReal.ofReal_mul (by norm_num [kappa])]
  norm_num [kappa,securityBits,ENNReal.ofReal_div_of_pos]
  simp only [div_eq_mul_inv,mul_comm]

/-- Strict security for every natural budget, including the exact endpoints
at the row threshold and at2^127. Budgets above2^127 need only success≤1. -/
theorem typed_secure_of_bounds
    (small : ∀ (A : forestScheme.toAlgorithm.Adversary) (B : ℕ),
      CostAtMost (forestScheme.toAlgorithm.experiment A) B →
      (B:ℝ)≤(2:ℝ)^86/10 → B≤2^127 →
      E (run (forestScheme.toAlgorithm.experiment A) ∅) successValue ≤
        ENNReal.ofReal ((243337:ℝ)/245000*kappa*(B:ℝ)))
    (large : ∀ (A : forestScheme.toAlgorithm.Adversary) (B : ℕ),
      CostAtMost (forestScheme.toAlgorithm.experiment A) B →
      (2:ℝ)^86/10≤(B:ℝ) → B≤2^127 →
      E (run (forestScheme.toAlgorithm.experiment A) ∅) successValue ≤
        ENNReal.ofReal ((991:ℝ)/1000*kappa*(B:ℝ))) :
    forestScheme.toAlgorithm.Secure := by
  intro A B hB
  have hbudget : 995≤B := experiment_budget A B hB
  have hpos : 0<(B:ℝ) := by exact_mod_cast (show 0<B by omega)
  have hrate : 0<kappa*(B:ℝ) := mul_pos (by norm_num [kappa]) hpos
  rw [probTrue_eq_success,← security_rate]
  by_cases hcap : B≤2^127
  · by_cases hsmall : (B:ℝ)≤(2:ℝ)^86/10
    · exact (small A B hB hsmall hcap).trans_lt
        ((ENNReal.ofReal_lt_ofReal_iff hrate).mpr (small_strict B hpos))
    · exact (large A B hB (le_of_not_ge hsmall) hcap).trans_lt
        ((ENNReal.ofReal_lt_ofReal_iff hrate).mpr (large_strict B hpos))
  · have ht : (1:ℝ)<kappa*(B:ℝ) :=
      above_trivial_budget 1 le_rfl B (lt_of_not_ge hcap)
    have he : (1:ℝ≥0∞)<ENNReal.ofReal (kappa*(B:ℝ)) := by
      simpa only [ENNReal.ofReal_one] using (ENNReal.ofReal_lt_ofReal_iff hrate).mpr ht
    exact (E_le_one _ successValue_le_one).trans_lt he

#print axioms probTrue_eq_success
#print axioms security_rate
#print axioms typed_secure_of_bounds
end OptimalOTS.WeightedConstruction.WideSecurityClosure
