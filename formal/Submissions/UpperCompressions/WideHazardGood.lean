import Submissions.UpperCompressions.WideHazardMoments
import Submissions.UpperCompressions.DualCountSteps
import Submissions.UpperCompressions.WideEmpiricalBounds
import Submissions.UpperCompressions.WeightedHazardPair

/-! The actual common empirical Good event bounds the clipped-hazard drift
and its cumulative inside-row variance contribution. -/
noncomputable section
open OracleSpec OracleComp
open scoped Classical
namespace OptimalOTS.WeightedConstruction.WideHazard
open WeightedSchedule WideDomains WeightedRow.Weights
open WeightedRealExecution WeightedDualCache WeightedReference WeightedConstants
attribute [local irreducible] Finset.univ Finset.filter queryPhase

def globalCount (c : hashSpec.QueryCache) : ℕ :=
  (WeightedCacheCounts.seen indexDomain c).card
def alpha : ℝ := (91/100)*kappa
def gainRate (B : ℝ) (s : Phase) : ℝ :=
  alpha*(globalStep s : ℝ)+alpha*B/N*(rowStep s : ℝ)

theorem mean_margin_le : securityWeights.mean+kappa/100 ≤ alpha := by
  have h := securityWeights_mean
  unfold alpha
  linarith [show (0:ℝ)≤kappa by norm_num [kappa]]

theorem good_row_hyp (m : Message) (c : hashSpec.QueryCache) (hc : WideEmpirical.Good c) :
    securityWeights.score (rowCounts m c) ≤
      (rowCount m c : ℝ)*securityWeights.mean+(1/100)*kappa*N := by
  have h := WideEmpirical.good_row_score c hc m
  change securityWeights.score (rowCounts m c) ≤
    securityWeights.mean*(rowCount m c : ℝ)+kappa*(2:ℝ)^86/100 at h
  exact h.trans_eq (by unfold N; ring)

theorem good_global_seen (B : ℝ) (c : hashSpec.QueryCache) (hc : WideEmpirical.Good c)
    (hB : N/10 ≤ B) (hq : (globalCount c : ℝ) ≤ B) :
    securityWeights.seen (globalCounts c) ≤ alpha*B := by
  have hs := WideEmpirical.good_global c hc
  change securityWeights.score (globalCounts c) ≤
    securityWeights.mean*(globalCount c : ℝ)+(kappa/100)*max (globalCount c : ℝ) (N/10) at hs
  have hm0 : 0 ≤ securityWeights.mean :=
    Finset.sum_nonneg (fun i _ => mul_nonneg (securityWeights.p_pos i).le
      (securityWeights.g_nonneg i))
  have hmax : max (globalCount c : ℝ) (N/10) ≤ B := max_le hq hB
  have h1 := mul_le_mul_of_nonneg_left hq hm0
  have h2 := mul_le_mul_of_nonneg_left hmax (show 0≤kappa/100 by norm_num [kappa])
  have h3 := mul_le_mul_of_nonneg_right mean_margin_le ((Nat.cast_nonneg (globalCount c) : (0:ℝ)≤globalCount c).trans hq)
  exact (securityWeights.seen_le_score (globalCounts c)).trans (by nlinarith)

theorem good_delta_drift (m : Message) (t : Spec.Domain) (c : hashSpec.QueryCache)
    (hc : WideEmpirical.Good c) :
    securityWeights.expect (delta (queryPhase m t c) m c) ≤
      alpha*(globalStep (queryPhase m t c) : ℝ) := by
  have h := (delta_drift_le m t c (1/100) (by norm_num) (good_row_hyp m c hc)).trans
    (show securityWeights.mean+(1/100)*kappa ≤ alpha from
      (by calc
        _ = securityWeights.mean+kappa/100 := by ring
        _ ≤ alpha := mean_margin_le))
  cases hs : queryPhase m t c with
  | idle =>
    have hz : delta Phase.idle m c = fun _ => 0 := by funext x; exact sub_self _
    rw [hz,expect_const]
    simp [globalStep]
  | outside => simpa only [hs,globalStep,Nat.cast_one,mul_one] using h
  | inside => simpa only [hs,globalStep,Nat.cast_one,mul_one] using h

theorem good_gain_mean (B : ℝ) (m : Message) (t : Spec.Domain) (c : hashSpec.QueryCache)
    (hc : WideEmpirical.Good c) (hB : N/10 ≤ B) (hq : (globalCount c : ℝ) ≤ B) :
    securityWeights.expect (gain (queryPhase m t c) m c) ≤ gainRate B (queryPhase m t c) := by
  have hd := good_delta_drift m t c hc
  have he : securityWeights.expect (delta (queryPhase m t c) m c) =
      securityWeights.expect (gain (queryPhase m t c) m c)-shift (queryPhase m t c) c := by
    simp only [show delta (queryPhase m t c) m c =
      (fun x => gain (queryPhase m t c) m c x-shift (queryPhase m t c) c) from
      funext (delta_gain_shift _ _ _),expect_sub,expect_const]
  have hs := div_le_div_of_nonneg_right (good_global_seen B c hc hB hq)
    (show 0≤N by norm_num [N])
  cases hp : queryPhase m t c with
  | idle =>
    simp only [gain,expect_const,gainRate,globalStep,rowStep,Nat.cast_zero,mul_zero,add_zero]
    exact le_rfl
  | outside =>
    simp only [hp,shift,globalStep,Nat.cast_one,mul_one,sub_zero] at he hd
    simpa only [gainRate,globalStep,rowStep,Nat.cast_one,Nat.cast_zero,mul_one,mul_zero,add_zero]
      using he.symm.trans_le hd
  | inside =>
    simp only [hp,shift,globalStep,Nat.cast_one,mul_one] at he hd
    simp only [gainRate,globalStep,rowStep,Nat.cast_one,mul_one]
    linarith

#print axioms good_global_seen
#print axioms good_delta_drift
#print axioms good_gain_mean
end OptimalOTS.WeightedConstruction.WideHazard
