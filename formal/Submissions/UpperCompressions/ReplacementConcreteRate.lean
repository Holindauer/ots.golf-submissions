import Submissions.UpperCompressions.ReplacementFreshOverlay
import Submissions.UpperCompressions.WeightedPrefix
import Submissions.UpperCompressions.WideSecurityData

/-! Actual decoder probabilities and the concrete fresh-public-input posterior
rate for the mixed72 schedule. -/
open OptimalOTS
namespace WeightedReplacement
noncomputable section
open scoped Classical
open OptimalOTS.WeightedConstruction.WeightedSchedule WeightedReference
attribute [local irreducible] Finset.univ Finset.filter OptimalOTS.WeightedResearch92.classes

theorem concrete_weak_mass_pos (i : Fin M) :
    0 < fraction (weakRank tier i ∘ decode) := by
  rw [weakRank_probability]
  exact lt_of_lt_of_le (by norm_num [acceptance])
    (survival_ge_reject _ (by have := tier_lt i; omega))

theorem concrete_class_fraction (i : Fin M) :
    fraction (fun y => decode y = some i) = classProbability i := by
  unfold fraction
  convert uniform_decode_probability i using 1
  congr 1
  funext y
  split_ifs <;> rfl

theorem concrete_posterior_rate (i : Fin M) :
    fraction (fun y => decode y = some i) / fraction (weakRank tier i ∘ decode) =
      classProbability i / survival (tier i) := by
  rw [concrete_class_fraction, weakRank_probability]

theorem concrete_posterior_rate_le (i : Fin M) :
    fraction (fun y => decode y = some i) / fraction (weakRank tier i ∘ decode) ≤
      classProbability i / (1-acceptance) := by
  rw [concrete_posterior_rate]
  exact div_le_div_of_nonneg_left (classProbability_pos i).le
    (by norm_num [acceptance]) (survival_ge_reject _ (by have := tier_lt i; omega))

theorem concrete_posterior_rate_ennreal (i : Fin M) :
    ENNReal.ofReal (fraction (fun y => decode y = some i) / fraction (weakRank tier i ∘ decode)) ≤
      ENNReal.ofReal (classProbability i / (1-acceptance)) :=
  ENNReal.ofReal_le_ofReal (concrete_posterior_rate_le i)

theorem concrete_rate_eq_base_excess (i : Fin M) :
    classProbability i / (1-acceptance) = kappa/2 + excess i := by
  rw [excess_eq]
  ring

theorem concrete_posterior_rate_base_excess (i : Fin M) :
    fraction (fun y => decode y = some i) / fraction (weakRank tier i ∘ decode) ≤
      kappa/2 + excess i := by
  rw [← concrete_rate_eq_base_excess]
  exact concrete_posterior_rate_le i

theorem concrete_posterior_rate_ennreal_base_excess (i : Fin M) :
    ENNReal.ofReal (fraction (fun y => decode y = some i) / fraction (weakRank tier i ∘ decode)) ≤
      ENNReal.ofReal (kappa/2) + ENNReal.ofReal (excess i) := by
  have he : 0 ≤ excess i := le_max_right _ _
  rw [← ENNReal.ofReal_add (show 0 ≤ kappa/2 by unfold kappa; positivity) he]
  exact ENNReal.ofReal_le_ofReal (concrete_posterior_rate_base_excess i)

#print axioms concrete_posterior_rate_ennreal_base_excess
#print axioms concrete_weak_mass_pos
#print axioms concrete_posterior_rate_le
end
end WeightedReplacement
