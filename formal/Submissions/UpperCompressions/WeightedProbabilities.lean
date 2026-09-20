import Submissions.UpperCompressions.WeightedOutputFibers
namespace OptimalOTS.WeightedConstruction.WeightedSchedule
noncomputable section
open scoped Classical
attribute [local irreducible] Finset.univ Finset.filter tier WeightedResearch92.tierClasses WeightedResearch92.classes WeightedResearch92.acceptedAliases
theorem decode_probability (i : Fin M) :
    ((Finset.univ.filter fun x : BitVec 256 => decode x = some i).card : ℚ) / 2^256 =
      (2 : ℚ)^(tier i+1) / 2^129 := by
  have h (a : ℚ) : a * 2^127 / 2^256 = a / 2^129 := by norm_num; ring
  rw [decode_fiber]
  push_cast
  exact h _

theorem acceptance_probability :
    ((Finset.univ.filter fun x : BitVec 256 => (decode x).isSome).card : ℚ) / 2^256 =
      45/524288 := by
  rw [accepted_decode_count]
  change ((WeightedResearch92.acceptedAliases * 2^127 : ℕ) : ℚ) / 2^256 = _
  rw [WeightedResearch92.aliases_exact]
  norm_num


end
end OptimalOTS.WeightedConstruction.WeightedSchedule
#print axioms OptimalOTS.WeightedConstruction.WeightedSchedule.decode_probability
#print axioms OptimalOTS.WeightedConstruction.WeightedSchedule.acceptance_probability
