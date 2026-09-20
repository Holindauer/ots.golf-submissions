import Submissions.UpperCompressions.WideWire
import Submissions.UpperCompressions.WeightedBudgetClosure

/-! Positive budget and strict scalar endpoints for the protected experiment.
No probability bound or security premise is silently introduced here. -/
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
namespace OptimalOTS.WeightedConstruction.WideBudgetEndpoints
open OracleComp ENNReal
open WideForest WideWire WeightedReference

theorem experiment_budget (A : typed.Adversary) (B : ℕ)
    (hB : CostAtMost (typed.experiment A) B) : 995 ≤ B := by
  have h := GraphKeygenBridge.costAtMost_keygen_bind
    forestScheme.graph forestScheme.publicKey _ hB
  rw [forestScheme_keygenCost] at h
  exact h.1

theorem raw_experiment_budget (A : OracleAlgorithm.Adversary) (B : ℕ)
    (hB : CostAtMost (OracleAlgorithm.experiment scheme A) B) : 995 ≤ B := by
  change CostAtMost (OracleAlgorithm.experiment (WireAdapter.scheme typed decode) A) B at hB
  rw [WireAdapter.experiment_eq typed decode decode_encode canonical A] at hB
  exact experiment_budget _ B hB

theorem small_strict (K : ℝ) (hK : 0 < K) :
    (243337:ℝ)/245000*kappa*K < kappa*K := by
  have hk : 0 < kappa*K := mul_pos (by norm_num [kappa]) hK
  nlinarith

theorem large_strict (K : ℝ) (hK : 0 < K) :
    (991:ℝ)/1000*kappa*K < kappa*K := by
  have hk : 0 < kappa*K := mul_pos (by norm_num [kappa]) hK
  nlinarith

theorem above_trivial_budget (p : ℝ) (hp : p ≤ 1) (B : ℕ) (hB : 2^127 < B) :
    p < kappa*(B:ℝ) := by
  have hBr : (2:ℝ)^127 < B := by exact_mod_cast hB
  have hk := mul_lt_mul_of_pos_left hBr (show 0 < kappa by norm_num [kappa])
  have he : kappa*(2:ℝ)^127=1 := by norm_num [kappa]
  rw [he] at hk
  exact hp.trans_lt hk

/-- Canonical raw encoding transfers the eventual typed theorem exactly. -/
theorem raw_secure_of_typed (h : typed.Secure) : scheme.Secure :=
  WireAdapter.secure typed decode decode_encode canonical h

#print axioms experiment_budget
#print axioms raw_experiment_budget
#print axioms raw_secure_of_typed
end OptimalOTS.WeightedConstruction.WideBudgetEndpoints
