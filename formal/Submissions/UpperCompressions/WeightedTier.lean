import Submissions.UpperCompressions.WeightedFibers

namespace OptimalOTS.WeightedConstruction.WeightedSchedule
noncomputable section
open scoped Classical
attribute [local irreducible] Finset.univ Finset.filter
attribute [local irreducible] WeightedResearch92.tierClasses WeightedResearch92.classes WeightedResearch92.acceptedAliases

theorem rawTier_eq_decodeTier (x : BitVec 129) (j : Tier) :
    (decodeRaw x).map tier = some j.val ↔ rawTier x = some j := by
  cases h : rawAlias x with
  | none => simp only [decodeRaw, rawClass, rawTier, h, Option.map_none, reduceCtorEq]
  | some a =>
    simp only [decodeRaw, rawClass, rawTier, h, Option.map_some, Option.some.injEq]
    change (classEquiv.symm (classEquiv a.1)).1.val = j.val ↔ a.1.1 = j
    rw [classEquiv.symm_apply_apply, Fin.ext_iff]

theorem decodeTier_fiber (j : Tier) :
    (Finset.univ.filter fun x : BitVec 256 => (decode x).map tier = some j.val).card =
      population j * 2^(j.val+1) * 2^127 := by
  have he : (Finset.univ.filter fun x : BitVec 256 => (decode x).map tier = some j.val) =
      Finset.univ.filter fun x : BitVec 256 => rawTier (x.setWidth 129) = some j := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, decode, rawTier_eq_decodeTier]
  have h := card_truncPredicate (n := 256) (w := 129) (by omega)
    (fun x => rawTier x = some j)
  exact (congrArg Finset.card he).trans
    (h.trans (congrArg (fun k : ℕ => k * 2^(256-129)) (rawTier_fiber j)))


end
end OptimalOTS.WeightedConstruction.WeightedSchedule

#print axioms OptimalOTS.WeightedConstruction.WeightedSchedule.rawTier_eq_decodeTier
#print axioms OptimalOTS.WeightedConstruction.WeightedSchedule.decodeTier_fiber
