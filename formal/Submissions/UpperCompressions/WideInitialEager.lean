import Submissions.UpperCompressions.WideInitialGame
import Submissions.UpperCompressions.SignedGameExpectation

/-! The reduced actual sign/post continuation as the full-table expectation
used by the signed/no-sign conditional master. -/
open OracleSpec OracleComp OracleComp.EvalDist ENNReal
noncomputable section
open scoped Classical BigOperators
set_option maxRecDepth 10000
set_option maxHeartbeats 800000
namespace OptimalOTS.WeightedConstruction.WideInitialGame
open OptimalOTS.Dag WideForest WideForest.Name WeightedReplacement WeightedSampling
attribute [local irreducible] Finset.univ Finset.filter graph CostAtMost WeightedResearch92.classes
variable (A : forestScheme.toAlgorithm.Adversary)

theorem kc_indexLength_none (ξ : Rec) (q : Query) (hq : q.1 = msgBits+86) : kc ξ q = none := by
  cases hc : kc ξ q with
  | none => rfl
  | some u =>
    obtain ⟨h,p,hp,he,_⟩ := (kc_apply_iff ξ q u).mp hc
    exact False.elim (len_hashParent_ne_enc hp ((congrArg Sigma.fst he).symm.trans hq))

theorem afterChoose_eager (pk : PublicKey) (ξ : Rec) (x : Message × A.State) (d : Cache) :
    E (run (afterChoose A pk (graph.evalRec ξ) x) (Cache.extend d (kc ξ))) successValue =
      E ($ᵗ (BitVec (msgBits+86) → BitVec hashBits)) (fun g =>
        E (run (loop 86 WeightedSchedule.decode WeightedSchedule.tier x.1 signBudget)
          ((lengthSlice (msgBits+86)).preload d g)) (fun p =>
          E (run (stBWithForgery A pk x.1 x.2 (signatureFromWinner ξ p.1))
            (Cache.extend p.2 (kc ξ))) forgerySuccess)) := by
  have h := outE_length_preload (msgBits+86) (afterChoose A pk (graph.evalRec ξ) x)
    (Cache.extend d (kc ξ)) (fun b => if b = true then 1 else 0)
  change E (run (afterChoose A pk (graph.evalRec ξ) x) (Cache.extend d (kc ξ))) successValue = _ at h
  rw [h]
  apply congrArg (E ($ᵗ (BitVec (msgBits+86) → BitVec hashBits)))
  funext g
  rw [preload_extend_commute _ d (kc ξ) (kc_indexLength_none ξ)]
  change E (run (afterChoose A pk (graph.evalRec ξ) x)
    (Cache.extend ((lengthSlice (msgBits+86)).preload d g) (kc ξ))) successValue = _
  rw [afterChoose_extend]
  congr 1
  funext p
  exact (retained_success_eq A pk x.1 x.2 (signatureFromWinner ξ p.1) _).symm

/-- The initial first-stage conditional is exactly a joint full-table average,
with original-public-cache exclusions kept outside the sign/post experiment. -/
theorem conditional_eager (pk : PublicKey) (x : Message × A.State) (d : Cache) :
    conditional A pk x d = ∑ ξ ∈ (fiberA pk).filter (fun ξ => ¬ Cache.Hits d (kc ξ)), w *
      E ($ᵗ (BitVec (msgBits+86) → BitVec hashBits)) (fun g =>
        E (run (loop 86 WeightedSchedule.decode WeightedSchedule.tier x.1 signBudget)
          ((lengthSlice (msgBits+86)).preload d g)) (fun p =>
          E (run (stBWithForgery A pk x.1 x.2 (signatureFromWinner ξ p.1))
            (Cache.extend p.2 (kc ξ))) forgerySuccess)) := by
  unfold conditional
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro ξ _
  by_cases hh : Cache.Hits d (kc ξ)
  · simp [hh]
  · simp only [hh,if_false,not_false_eq_true,if_true]
    rw [afterChoose_eager]

#print axioms afterChoose_eager
#print axioms conditional_eager
end OptimalOTS.WeightedConstruction.WideInitialGame
