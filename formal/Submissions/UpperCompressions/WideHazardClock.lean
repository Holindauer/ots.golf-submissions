import Submissions.UpperCompressions.WideHazardMGF

/-! The variance clock counts actual fresh global inputs and actual nonce-row
positions. Private draws, repeated cache hits, and nonindex hashes do not move it. -/
noncomputable section
open OracleSpec OracleComp OracleComp.EvalDist
open scoped Classical
namespace OptimalOTS.WeightedConstruction.WideHazard
open WeightedSchedule WideDomains WeightedRow.Weights WeightedRealExecution WeightedDualCache
open WeightedReference WeightedConstants WeightedOracleExecution
attribute [local irreducible] Finset.univ Finset.filter

def Z (m : Message) (c : hashSpec.QueryCache) : ℝ := hazard m c-alpha*(globalCount c:ℝ)
def cap (c : hashSpec.QueryCache) : ℝ := max (globalCount c:ℝ) (N/10)
def W (m : Message) (c : hashSpec.QueryCache) : ℝ :=
  jumpBound*alpha*((globalCount c:ℝ)+cap c*(rowCount m c:ℝ)/N)

theorem clock_growth (q r u v : ℝ) (hr : 0≤r) (hu : 0≤u) (hv : 0≤v) :
    jumpBound*alpha*(q+max q (N/10)*r/N)+
      jumpBound*(alpha*u+alpha*max q (N/10)/N*v) ≤
    jumpBound*alpha*((q+u)+max (q+u) (N/10)*(r+v)/N) := by
  have hm : max q (N/10) ≤ max (q+u) (N/10) := max_le_max_right _ (by linarith)
  have hp := mul_le_mul_of_nonneg_right hm (add_nonneg hr hv)
  have hd := div_le_div_of_nonneg_right hp (show 0≤N by norm_num [N])
  have hj : 0≤jumpBound*alpha := by norm_num [jumpBound,alpha,L,kappa,N]
  have h := mul_le_mul_of_nonneg_left (add_le_add_left hd (q+u)) hj
  calc
    _ = jumpBound*alpha*((q+u)+max q (N/10)*(r+v)/N) := by ring
    _ ≤ _ := by simpa only [add_comm] using h

theorem actual_count_steps (m : Message) (t : Spec.Domain) (c : hashSpec.QueryCache)
    (out : Spec.Range t × hashSpec.QueryCache)
    (hout : out ∈ support ((oracleImpl t).run c)) :
    globalCount out.2 = globalCount c+globalStep (queryPhase m t c) ∧
    rowCount m out.2 = rowCount m c+rowStep (queryPhase m t c) := by
  have hg := actual_seen_count indexDomain t c out hout
  have hr := actual_seen_count (rowDomain m) t c out hout
  have he := protected_phase_steps (rowDomain m) indexDomain (row_subset m) t c
  exact ⟨hg.trans (congrArg (fun n => globalCount c+n) he.1.symm),
    hr.trans (congrArg (fun n => rowCount m c+n) he.2.symm)⟩

theorem actual_ZW_steps (m : Message) (t : Spec.Domain) (c : hashSpec.QueryCache)
    (out : Spec.Range t × hashSpec.QueryCache)
    (hout : out ∈ support ((oracleImpl t).run c)) :
    Z m out.2 = Z m c+(hazard m out.2-hazard m c-alpha*(globalStep (queryPhase m t c):ℝ)) ∧
    W m c+jumpBound*gainRate (cap c) (queryPhase m t c) ≤ W m out.2 := by
  obtain ⟨hg,hr⟩ := actual_count_steps m t c out hout
  constructor
  · unfold Z
    rw [hg,Nat.cast_add]
    ring
  · unfold W cap gainRate
    rw [hg,hr,Nat.cast_add,Nat.cast_add]
    exact clock_growth _ _ _ _ (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _)

theorem actual_potential_step (m : Message) (t : Spec.Domain) (c : hashSpec.QueryCache)
    (hc : WideEmpirical.Good c)
    (θ : ℝ) (hθ : 0≤θ) (hθJ : θ*jumpBound<3) :
    expectedValue ((oracleImpl t).run c)
      (fun out => ENNReal.ofReal (Real.exp
        (θ*Z m out.2-θ^2*W m out.2/(2*(1-θ*jumpBound/3))))) ≤
      ENNReal.ofReal (Real.exp (θ*Z m c-θ^2*W m c/(2*(1-θ*jumpBound/3)))) := by
  rw [←ofReal_realEval _ _ (fun _ => Real.exp_nonneg _)]
  apply ENNReal.ofReal_le_ofReal
  have hp := WeightedKernel.exponential_step (realEval ((oracleImpl t).run c)) (Z m c)
    (θ^2*W m c/(2*(1-θ*jumpBound/3))) θ
    (θ^2*(jumpBound*gainRate (cap c) (queryPhase m t c))/(2*(1-θ*jumpBound/3)))
    (fun out => hazard m out.2-hazard m c-alpha*(globalStep (queryPhase m t c):ℝ))
    (actual_good_delta_mgf (cap c) m t c hc (le_max_right _ _) (le_max_left _ _) θ hθ hθJ)
  apply (realEval_mono_of_support ((oracleImpl t).run c) _ _ (fun out hout => ?_)).trans hp
  obtain ⟨hz,hw⟩ := actual_ZW_steps m t c out hout
  apply Real.exp_le_exp.mpr
  rw [hz]
  have hden : 0<2*(1-θ*jumpBound/3) := by linarith
  have hv := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hw (sq_nonneg θ)) hden.le
  rw [mul_add,add_div] at hv
  exact sub_le_sub_left hv _

theorem W_budget_bound (B : ℝ) (m : Message) (c : hashSpec.QueryCache)
    (hB : N/10≤B) (hq : (globalCount c:ℝ)≤B) :
    W m c ≤ (182/100)*jumpBound*kappa*B := by
  have hr := rowCount_le m c
  have hn : (0:ℝ)<N := by norm_num [N]
  have hcap : cap c≤B := max_le hq hB
  have hc0 : 0≤cap c := (Nat.cast_nonneg (globalCount c) : (0:ℝ)≤globalCount c).trans (le_max_left _ _)
  have hbr := mul_le_mul_of_nonneg_left ((div_le_one hn).mpr hr) hc0
  have hj : 0≤jumpBound*alpha := by norm_num [jumpBound,alpha,L,kappa,N]
  have hs : (globalCount c:ℝ)+cap c*(rowCount m c:ℝ)/N ≤ 2*B := by
    rw [←mul_div_assoc] at hbr
    linarith
  have h := mul_le_mul_of_nonneg_left hs hj
  unfold W
  exact h.trans_eq (by unfold alpha; ring)

#print axioms actual_potential_step
#print axioms W_budget_bound
end OptimalOTS.WeightedConstruction.WideHazard
