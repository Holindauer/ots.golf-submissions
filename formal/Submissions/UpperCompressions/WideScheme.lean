import Submissions.UpperCompressions.WeightedScheme
import Submissions.UpperCompressions.WideCapacity
import Submissions.UpperCompressions.WeightedSchedule

/-! Concrete weighted rank74/word129 construction. Correctness and resources
are certified here; signing availability and strong security remain unproved. -/

open OracleSpec OracleComp ENNReal
noncomputable section
open scoped Classical
set_option maxRecDepth 10000

namespace OptimalOTS.WeightedConstruction.WideForest

open OptimalOTS.Dag
open Name

/-- Select distinct cuts from the certified shallow family. -/
def setsName (i : Fin WeightedSchedule.M) : Finset Name :=
  (family.equivFin.symm (Fin.castLE card_family i)).1

theorem setsName_mem (i : Fin WeightedSchedule.M) : setsName i ∈ family :=
  (family.equivFin.symm (Fin.castLE card_family i)).2

theorem setsName_injective : Function.Injective setsName := by
  intro i j h
  unfold setsName at h
  exact Fin.castLE_injective _ (family.equivFin.symm.injective (Subtype.ext h))

def forestScheme : WeightedScheme.Scheme WeightedSchedule.M where
  graph := graph
  decode := WeightedSchedule.decode
  tier := WeightedSchedule.tier
  sets := fun i => fins (setsName i)
  root_not_mem := by
    intro i
    show rh.fin ∉ fins (setsName i)
    rw [mem_fins]
    exact (isCut_of_mem_family (setsName_mem i)).rh_not_mem
  no_hidden_source := by
    intro i
    exact (no_hidden_source_iff (setsName i)).mpr
      (isCut_of_mem_family (setsName_mem i)).covers
  reveal_le := by
    intro i
    show graph.revealBits (fins (setsName i)) + 86 ≤ 5504
    rw [revealBits_eq, Finset.sum_const_nat
      fun n hn => (isCut_of_mem_family (setsName_mem i)).values n hn]
    have := card_of_mem_family (setsName_mem i)
    omega
  keygen_le := by
    show graph.keygenCost ≤ 1024
    rw [graph_keygenCost]
    norm_num

theorem isCut_setsName (i : Fin WeightedSchedule.M) : IsCut (setsName i) :=
  isCut_of_mem_family (setsName_mem i)

theorem card_setsName (i : Fin WeightedSchedule.M) : (setsName i).card = 42 :=
  card_of_mem_family (setsName_mem i)

theorem cost_setsName (i : Fin WeightedSchedule.M) :
    ∑ n ∈ evaluatedSet (setsName i), n.cost = 91 :=
  cost_of_mem_family (setsName_mem i)

theorem forestScheme_reconstructCost (i : Fin WeightedSchedule.M) :
    forestScheme.graph.reconstructCost (forestScheme.sets i) = 91 := by
  change graph.reconstructCost (fins (setsName i)) = 91
  rw [reconstructCost_eq, cost_setsName]

theorem forestScheme_revealBits (i : Fin WeightedSchedule.M) :
    forestScheme.graph.revealBits (forestScheme.sets i) = 42 * 129 := by
  change graph.revealBits (fins (setsName i)) = 42 * 129
  rw [revealBits_eq, Finset.sum_const_nat fun n hn => (isCut_setsName i).values n hn,
    card_setsName]

theorem forestScheme_keygenCost : forestScheme.graph.keygenCost = 995 :=
  graph_keygenCost

theorem typed_cost : forestScheme.toAlgorithm.VerifyCostAtMost 92 :=
  forestScheme.verifyCost (fun i => (forestScheme_reconstructCost i).le)

theorem typed_correct : forestScheme.toAlgorithm.Correct := forestScheme.correct

theorem typed_signatureSize : forestScheme.toAlgorithm.SignatureSizeAtMost maxSignatureBits :=
  forestScheme.signatureSize

theorem typed_rejectsOversized : forestScheme.toAlgorithm.RejectsOversized maxSignatureBits :=
  forestScheme.rejectsOversized

theorem typed_keygenCost : forestScheme.toAlgorithm.KeygenCostAtMost keygenBudget :=
  forestScheme.keygenCost

theorem typed_signCost : forestScheme.toAlgorithm.SignCostAtMost signBudget :=
  forestScheme.signCost

theorem typed_verifyDeterministic : forestScheme.toAlgorithm.VerifyDeterministic :=
  forestScheme.verifyDeterministic

#print axioms typed_cost
#print axioms typed_correct
#print axioms typed_signatureSize
#print axioms typed_rejectsOversized
#print axioms typed_keygenCost
#print axioms typed_signCost
#print axioms typed_verifyDeterministic

end OptimalOTS.WeightedConstruction.WideForest
