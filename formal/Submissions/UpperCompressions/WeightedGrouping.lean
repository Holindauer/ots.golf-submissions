import Submissions.UpperCompressions.WeightedTier
import Submissions.UpperCompressions.WeightedProbabilities
import Submissions.UpperCompressions.WeightedConstants

/-! Exact grouping and real-number masses for the actual mixed72 decoder.
These identities connect construction fibers to the reference distribution;
they do not assert an adaptive game bound. -/

namespace OptimalOTS.WeightedConstruction.WeightedSchedule
noncomputable section
open scoped Classical
attribute [local irreducible] Finset.univ Finset.filter
attribute [local irreducible] WeightedResearch92.tierClasses WeightedResearch92.classes WeightedResearch92.acceptedAliases

/-- Reindex any real-valued tier function by the exact class populations. -/
theorem sum_tier (f : ℕ → ℝ) :
    (∑ i : Fin M, f (tier i)) = ∑ j : Tier, (population j : ℝ) * f j.val := by
  calc
    _ = ∑ c : Class, f c.1.val := by
      apply Fintype.sum_equiv classEquiv.symm
      intro i
      rfl
    _ = ∑ j : Tier, (population j : ℝ) * f j.val := by
      rw [Fintype.sum_sigma]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

def classProbability (i : Fin M) : ℝ := (2:ℝ)^(tier i+1) / 2^129

def tierProbability (j : Tier) : ℝ :=
    ((Finset.univ.filter fun x : BitVec 256 => (decode x).map tier = some j.val).card : ℝ) / 2^256

theorem class_probability_real (i : Fin M) :
    ((Finset.univ.filter fun x : BitVec 256 => decode x = some i).card : ℝ) / 2^256 =
      classProbability i := by
  have h (a : ℝ) : a * 2^127 / 2^256 = a / 2^129 := by norm_num; ring
  unfold classProbability
  rw [decode_fiber]
  push_cast
  convert h ((2:ℝ)^(tier i+1)) using 1 <;> norm_num

theorem tier_probability_eq (j : Tier) :
    tierProbability j = (if j.val < 71 then 19 else 91 : ℝ) / 2^24 := by
  unfold tierProbability
  rw [decodeTier_fiber, tier_alias_count]
  push_cast
  split_ifs <;> norm_num

theorem early_tier_probability (j : Tier) (hj : j.val < 71) :
    tierProbability j = WeightedConstants.q := by
  rw [tier_probability_eq, if_pos hj]
  norm_num [WeightedConstants.q, WeightedConstants.L]

theorem last_tier_probability :
    tierProbability ⟨71, by decide⟩ = (91:ℝ)/2^24 := by
  rw [tier_probability_eq]
  norm_num

/-- The exact early-tier mass accumulated before tier j. -/
theorem early_prefix_probability (j : ℕ) (hj : j ≤ 71) :
    (∑ t ∈ Finset.range j,
      (if t < 71 then (19:ℝ) else 91) / 2^24) = (j:ℝ) * WeightedConstants.q := by
  calc
    _ = ∑ _t ∈ Finset.range j, WeightedConstants.q := by
      apply Finset.sum_congr rfl
      intro t ht
      rw [if_pos (by have := Finset.mem_range.mp ht; omega)]
      norm_num [WeightedConstants.q, WeightedConstants.L]
    _ = _ := by simp

/-- Class mass divided by kappa=2^-127 is half of its tier's power of two. -/
theorem relative_class_probability (i : Fin M) :
    classProbability i / ((2:ℝ)^127)⁻¹ = (1:ℝ)/2 * 2^(tier i) := by
  unfold classProbability
  rw [pow_succ]
  have h (a : ℝ) : (a*2/2^129) / ((2:ℝ)^127)⁻¹ = (1:ℝ)/2*a := by norm_num; ring
  exact h _

end
end OptimalOTS.WeightedConstruction.WeightedSchedule

#print axioms OptimalOTS.WeightedConstruction.WeightedSchedule.sum_tier
#print axioms OptimalOTS.WeightedConstruction.WeightedSchedule.tier_probability_eq
#print axioms OptimalOTS.WeightedConstruction.WeightedSchedule.relative_class_probability
