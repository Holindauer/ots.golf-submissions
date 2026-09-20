import Submissions.UpperCompressions.WeightedFibers

namespace OptimalOTS.WeightedConstruction.WeightedSchedule
noncomputable section
open scoped Classical
attribute [local irreducible] Finset.univ Finset.filter tier
attribute [local irreducible] WeightedResearch92.tierClasses WeightedResearch92.classes WeightedResearch92.acceptedAliases

theorem decode_fiber (i : Fin M) :
    (Finset.univ.filter fun x : BitVec 256 => decode x = some i).card =
      2^(tier i+1) * 2^127 := by
  have h := card_truncPredicate (n := 256) (w := 129) (by omega)
    (fun x => decodeRaw x = some i)
  exact h.trans (congrArg (fun k : ℕ => k * 2^(256-129)) (decodeRaw_fiber i))


theorem accepted_decode_count :
    (Finset.univ.filter fun x : BitVec 256 => (decode x).isSome).card = A * 2^127 := by
  have h := card_truncPredicate (n := 256) (w := 129) (by omega)
    (fun x => (decodeRaw x).isSome = true)
  exact h.trans (congrArg (fun k : ℕ => k * 2^(256-129)) accepted_decodeRaw_count)



end
end OptimalOTS.WeightedConstruction.WeightedSchedule
#print axioms OptimalOTS.WeightedConstruction.WeightedSchedule.decode_fiber
#print axioms OptimalOTS.WeightedConstruction.WeightedSchedule.accepted_decode_count
