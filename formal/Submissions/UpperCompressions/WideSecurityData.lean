import Submissions.UpperCompressions.WideReference
import Submissions.UpperCompressions.ClippedDrift

/-! Concrete distribution and bounded score data for the stochastic lemmas.
No security theorem is assumed by this interface. -/
noncomputable section
namespace OptimalOTS.WeightedConstruction.WeightedSchedule
open WeightedReference WeightedConstants WeightedReplacement
set_option maxHeartbeats 1000000

def securityWeights : WeightedRow.Weights (Fin M) where
  p := classProbability
  g := referenceWeight
  p_pos := classProbability_pos
  g_nonneg := referenceWeight_nonneg
  mass_le_one := by rw [classProbability_sum]; norm_num [acceptance]

theorem securityWeights_mean : securityWeights.mean ≤ kappa*(223/250) := mean_le

theorem survival_le_one (j : ℕ) : survival j ≤ 1 := by
  have h : 0 ≤ (j:ℝ)*q := mul_nonneg (Nat.cast_nonneg _) (by norm_num [q,L])
  unfold survival
  linarith

theorem survival_ge_reject (j : ℕ) (hj : j ≤ 71) : 1-acceptance ≤ survival j := by
  have hjr : (j:ℝ) ≤ 71 := by exact_mod_cast hj
  have hh := mul_le_mul_of_nonneg_right hjr (show 0 ≤ q by norm_num [q,L])
  have hn : (71:ℝ)*q ≤ acceptance := by norm_num [q,L,acceptance]
  unfold survival
  linarith

theorem lower_ge_reject (j : ℕ) (hj : j ≤ 71) : 1-acceptance ≤ lower j := by
  unfold lower
  split_ifs with h
  · exact survival_ge_reject _ (by omega)
  · exact le_refl _

theorem weight_ratio (i : Fin M) : referenceWeight i/classProbability i =
    kernel L (survival (tier i)) (lower (tier i)) := by
  unfold referenceWeight weight
  rw [← classProbability_eq]
  exact mul_div_cancel_left₀ _ (classProbability_pos i).ne'

theorem weight_ratio_le (i : Fin M) : referenceWeight i/classProbability i ≤ (L:ℝ) := by
  rw [weight_ratio]
  have hj : tier i ≤ 71 := by have := tier_lt i; omega
  have hm := kernel_mono L (survival_nonneg _ hj) (lower_nonneg _ hj)
    (survival_le_one _) ((lower_le_survival _ hj).trans (survival_le_one _))
  rw [kernel_diagonal,one_pow,mul_one] at hm
  exact hm

theorem excessScore_nonneg (i : Fin M) : 0 ≤ referenceWeight i*excess i/classProbability i := by
  apply div_nonneg
  · exact mul_nonneg (referenceWeight_nonneg i) (le_max_right _ _)
  · exact (classProbability_pos i).le

theorem excessScore_le (i : Fin M) :
    referenceWeight i*excess i/classProbability i ≤ (L:ℝ)*kappa := by
  have hd : 0 < 1-acceptance := by norm_num [acceptance]
  have hp := classProbability_pos i
  have hg := referenceWeight_nonneg i
  have he : excess i ≤ classProbability i/(1-acceptance) := by
    rw [excess_eq]
    have hk : 0 ≤ kappa/2 := by unfold kappa; positivity
    linarith
  calc
    _ ≤ (referenceWeight i*(classProbability i/(1-acceptance)))/classProbability i :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left he hg) hp.le
    _ = referenceWeight i/(1-acceptance) := by field_simp
    _ ≤ ((L:ℝ)*kappa/2)/(1-acceptance) :=
      div_le_div_of_nonneg_right (referenceWeight_le i) hd.le
    _ ≤ (L:ℝ)*kappa := by
      norm_num [L,kappa,acceptance]

/-- A complete-row prefix deficit implies the common multiplicative kernel
envelope; this is a pointwise implication, never a conditioning operation. -/
theorem empirical_kernel_le (i : Fin M) (Ah Bh : ℝ)
    (ha : 0 ≤ Ah) (hb : 0 ≤ Bh)
    (hA : Ah ≤ survival (tier i)+1/(100*(L:ℝ)))
    (hB : Bh ≤ lower (tier i)+1/(100*(L:ℝ))) :
    kernel L Ah Bh ≤ (99:ℝ)/98*(referenceWeight i/classProbability i) := by
  have hj : tier i ≤ 71 := by have := tier_lt i; omega
  have h := kernel_additive_envelope L ha hb
    (show 0 < 1-acceptance by norm_num [acceptance])
    (show 0 ≤ 1/(100*(L:ℝ)) by norm_num [L])
    (survival_ge_reject _ hj) (lower_ge_reject _ hj) hA hB
  rw [weight_ratio]
  exact h.trans (mul_le_mul_of_nonneg_right common_envelope
    (kernel_nonneg L (survival_nonneg _ hj) (lower_nonneg _ hj)))

#print axioms securityWeights
#print axioms weight_ratio_le
#print axioms excessScore_le
#print axioms empirical_kernel_le
end OptimalOTS.WeightedConstruction.WeightedSchedule
