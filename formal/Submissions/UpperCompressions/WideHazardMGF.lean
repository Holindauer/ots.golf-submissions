import Submissions.UpperCompressions.WideHazardGood
import Submissions.UpperCompressions.WeightedScoreMGF

/-! Compensated exponential drift under the concrete common Good event. -/
noncomputable section
open OracleSpec OracleComp
open scoped Classical
namespace OptimalOTS.WeightedConstruction.WideHazard
open WeightedSchedule WeightedRow.Weights WeightedRealExecution WeightedDualCache
open WeightedReference WeightedConstants WeightedEmpirical
attribute [local irreducible] Finset.univ Finset.filter queryPhase

theorem good_delta_mgf (B : ℝ) (m : Message) (t : Spec.Domain) (c : hashSpec.QueryCache)
    (hc : WideEmpirical.Good c) (hB : N/10 ≤ B) (hq : (globalCount c : ℝ) ≤ B)
    (θ : ℝ) (hθ : 0≤θ) (hθJ : θ*jumpBound<3) :
    securityWeights.expect (fun x => Real.exp
      (θ*(delta (queryPhase m t c) m c x-alpha*(globalStep (queryPhase m t c):ℝ))-
        θ^2*(jumpBound*gainRate B (queryPhase m t c))/(2*(1-θ*jumpBound/3)))) ≤ 1 := by
  let X : Option (Fin M) → ℝ := fun x => delta (queryPhase m t c) m c x-
    securityWeights.expect (delta (queryPhase m t c) m c)
  have hX (x : Option (Fin M)) : X x = gain (queryPhase m t c) m c x-
      securityWeights.expect (gain (queryPhase m t c) m c) := by
    dsimp only [X]
    rw [←drift_eq]
    exact centered_delta m t c x
  have hb (x : Option (Fin M)) : |X x|≤jumpBound := by
    rw [hX]
    exact securityWeights.centered_abs_le _ _ (gain_bounds m t c) x
  have hm : expectLinear securityWeights X=0 := by
    change securityWeights.expect X=0
    dsimp only [X]
    rw [expect_sub,expect_const,sub_self]
  have hJ : 0≤jumpBound := by norm_num [jumpBound,L,kappa,N]
  have hv : expectLinear securityWeights (fun x => (X x)^2) ≤
      jumpBound*gainRate B (queryPhase m t c) := by
    change securityWeights.expect (fun x => (X x)^2) ≤ _
    simp only [hX]
    exact (securityWeights.centered_variance_le _ _ (gain_bounds m t c)).trans
      (mul_le_mul_of_nonneg_left (good_gain_mean B m t c hc hB hq) hJ)
  have hmgf := WeightedMGF.compensated_mgf (expectLinear securityWeights)
    securityWeights.expect_mono (securityWeights.expect_const 1) X θ jumpBound
    (jumpBound*gainRate B (queryPhase m t c)) hθ hJ hθJ hb hm hv
  change securityWeights.expect (fun x => Real.exp (θ*X x-
    θ^2*(jumpBound*gainRate B (queryPhase m t c))/(2*(1-θ*jumpBound/3)))) ≤ 1 at hmgf
  have hd := good_delta_drift m t c hc
  apply (securityWeights.expect_mono _ _ (fun x => ?_)).trans hmgf
  apply Real.exp_le_exp.mpr
  dsimp only [X]
  exact sub_le_sub_right (mul_le_mul_of_nonneg_left (sub_le_sub_left hd _) hθ) _

theorem actual_good_delta_mgf (B : ℝ) (m : Message) (t : Spec.Domain)
    (c : hashSpec.QueryCache) (hc : WideEmpirical.Good c)
    (hB : N/10 ≤ B) (hq : (globalCount c : ℝ) ≤ B)
    (θ : ℝ) (hθ : 0≤θ) (hθJ : θ*jumpBound<3) :
    realEval ((oracleImpl t).run c) (fun out => Real.exp
      (θ*(hazard m out.2-hazard m c-alpha*(globalStep (queryPhase m t c):ℝ))-
        θ^2*(jumpBound*gainRate B (queryPhase m t c))/(2*(1-θ*jumpBound/3)))) ≤ 1 :=
  (primitive_delta_law m t c (fun z => Real.exp
    (θ*(z-alpha*(globalStep (queryPhase m t c):ℝ))-
      θ^2*(jumpBound*gainRate B (queryPhase m t c))/(2*(1-θ*jumpBound/3))))).trans_le
        (good_delta_mgf B m t c hc hB hq θ hθ hθJ)

#print axioms good_delta_mgf
#print axioms actual_good_delta_mgf
end OptimalOTS.WeightedConstruction.WideHazard
