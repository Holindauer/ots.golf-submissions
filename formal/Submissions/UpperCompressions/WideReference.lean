import Submissions.UpperCompressions.WeightedReference
import Submissions.UpperCompressions.WeightedGrouping

/-! Concrete class-average coefficients for the mixed72 decoder. -/
noncomputable section
namespace OptimalOTS.WeightedConstruction.WeightedSchedule
open WeightedReference
attribute [local irreducible] WeightedResearch92.tierClasses WeightedResearch92.classes
set_option maxHeartbeats 1000000

theorem classProbability_eq (i : Fin M) : classProbability i = probability (tier i) := by
  unfold classProbability probability kappa
  rw [pow_succ]
  norm_num
  ring

theorem population_probability (j : Tier) :
    (population j : ℝ)*probability j.val = mass j.val := by
  have hh := congrArg (fun n : ℕ => (n : ℝ)) (tier_alias_count j)
  push_cast at hh
  have ha : (population j : ℝ)*probability j.val =
      (if j.val < 71 then 19 else 91 : ℝ)/2^24 := by
    unfold probability kappa
    rw [pow_succ] at hh
    split_ifs at hh ⊢ <;> norm_num at hh ⊢ <;> nlinarith [hh]
  rw [ha]
  unfold mass lower
  split_ifs with h
  · norm_num [survival,WeightedConstants.q,WeightedConstants.L]
    ring
  · have hj : j.val=71 := by have := j.isLt; omega
    norm_num [hj,survival,acceptance,WeightedConstants.q,WeightedConstants.L]

def referenceWeight (i : Fin M) : ℝ := weight (tier i)
def mean : ℝ := ∑ i : Fin M,classProbability i*referenceWeight i

theorem mean_eq : mean = kappa*WeightedConstants.referenceMean failure := by
  unfold mean referenceWeight
  simp only [classProbability_eq]
  rw [sum_tier (fun j => probability j*weight j)]
  have he : (∑ j : Tier,(population j:ℝ)*(probability j.val*weight j.val)) =
      ∑ j : Tier,mass j.val*weight j.val := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [← mul_assoc,population_probability]
  rw [he]
  change (∑ j : Fin 72,mass j.val*weight j.val) = _
  rw [Fin.sum_univ_eq_sum_range (fun j => mass j*weight j) 72]
  exact reference_mean_identity

theorem mean_le : mean ≤ kappa*(223/250) := by
  rw [mean_eq]
  exact mul_le_mul_of_nonneg_left (WeightedConstants.referenceMean_le failure failure_nonneg)
    (by unfold kappa; positivity)

theorem referenceWeight_nonneg (i : Fin M) : 0 ≤ referenceWeight i :=
  weight_nonneg _ (by have := tier_lt i; omega)

theorem referenceWeight_le (i : Fin M) : referenceWeight i ≤ (WeightedConstants.L:ℝ)*kappa/2 :=
  weight_le _ (by have := tier_lt i; omega)

theorem classProbability_pos (i : Fin M) : 0 < classProbability i := by
  unfold classProbability
  positivity

theorem classProbability_sum : (∑ i : Fin M,classProbability i) = acceptance := by
  simp only [classProbability_eq]
  rw [sum_tier probability]
  simp only [population_probability]
  rw [Fin.sum_univ_eq_sum_range mass 72]
  exact total_mass

theorem referenceWeight_sum : (∑ i : Fin M,referenceWeight i) = 1-failure := by
  unfold referenceWeight
  rw [sum_tier weight]
  have he : (∑ j : Tier,(population j:ℝ)*weight j.val) =
      ∑ j : Tier,mass j.val*WeightedReplacement.kernel WeightedConstants.L
        (survival j.val) (lower j.val) := by
    apply Finset.sum_congr rfl
    intro j hj
    unfold weight
    rw [← mul_assoc,population_probability]
  rw [he]
  rw [Fin.sum_univ_eq_sum_range
    (fun j => mass j*WeightedReplacement.kernel WeightedConstants.L (survival j) (lower j)) 72]
  exact total_winner_mass

def excess (i : Fin M) : ℝ := max (classProbability i/(1-acceptance)-kappa/2) 0

theorem excess_eq (i : Fin M) : excess i = classProbability i/(1-acceptance)-kappa/2 := by
  apply max_eq_left
  have hp : kappa/2 ≤ classProbability i := by
    rw [classProbability_eq]
    have h : (1:ℝ) ≤ 2^(tier i) := one_le_pow₀ (by norm_num)
    have hh := mul_le_mul_of_nonneg_left h (show 0 ≤ kappa/2 by unfold kappa; positivity)
    simpa only [mul_one,probability] using hh
  have hd : 0 < 1-acceptance := by norm_num [acceptance]
  have hp' : classProbability i ≤ classProbability i/(1-acceptance) := by
    apply (le_div_iff₀ hd).2
    have h := mul_le_mul_of_nonneg_left
      (show 1-acceptance ≤ 1 by norm_num [acceptance]) (classProbability_pos i).le
    simpa only [mul_one] using h
  linarith

theorem excess_mean_eq :
    (∑ i : Fin M,referenceWeight i*excess i) = mean/(1-acceptance)-kappa/2*(1-failure) := by
  simp only [excess_eq,mul_sub,← mul_div_assoc,Finset.sum_sub_distrib,← Finset.sum_div,
    ← Finset.sum_mul]
  rw [referenceWeight_sum]
  have hm : (∑ i : Fin M,referenceWeight i*classProbability i) = mean := by
    unfold mean
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [hm]
  ring

theorem excess_mean_le : (∑ i : Fin M,referenceWeight i*excess i) ≤ kappa*(2/5) := by
  rw [excess_mean_eq]
  exact post_excess_le mean_le failure_le

#print axioms mean_eq
#print axioms mean_le
#print axioms referenceWeight_le
#print axioms classProbability_sum
#print axioms referenceWeight_sum
#print axioms excess_mean_le
end OptimalOTS.WeightedConstruction.WeightedSchedule
