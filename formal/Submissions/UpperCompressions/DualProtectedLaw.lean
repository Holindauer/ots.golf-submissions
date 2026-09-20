import Submissions.UpperCompressions.DualCacheSupport
import Submissions.UpperCompressions.ProtectedCacheStatistics

noncomputable section
open OracleSpec OracleComp
open scoped Classical
namespace WeightedDualCache
open WeightedRealExecution WeightedRow.Weights WeightedCacheCounts
variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem actual_query_law (w : WeightedRow.Weights ι)
    (A G : Finset OptimalOTS.Query) (hAG : A ⊆ G)
    (decode : BitVec OptimalOTS.hashBits → Option ι)
    (hfiber : ∀ x, ((Finset.univ.filter (fun b => decode b=x)).card:ℝ) /
      Fintype.card (BitVec OptimalOTS.hashBits) = w.classMass x)
    (t : OptimalOTS.Spec.Domain) (cache : OptimalOTS.hashSpec.QueryCache)
    (f : ℕ → (ι → ℕ) → (ι → ℕ) → ℝ) :
    realEval ((OptimalOTS.oracleImpl t).run cache)
      (fun out => f (seen A out.2).card (classCounts G out.2 decode)
        (classCounts A out.2 decode)) =
    w.expect (after f (protectedPhase A G t cache) (seen A cache).card
      (classCounts G cache decode) (classCounts A cache decode)) := by
  have h := protected_query_law w A G hAG decode hfiber t cache f
  rw [WeightedProtectedCache.protectedImpl_eq] at h
  exact h

theorem actual_payoff_support
    (A G : Finset OptimalOTS.Query) (hAG : A ⊆ G)
    (decode : BitVec OptimalOTS.hashBits → Option ι)
    (t : OptimalOTS.Spec.Domain) (cache : OptimalOTS.hashSpec.QueryCache)
    (f : ℕ → (ι → ℕ) → (ι → ℕ) → ℝ)
    (out : OptimalOTS.Spec.Range t × OptimalOTS.hashSpec.QueryCache)
    (hout : out ∈ support ((OptimalOTS.oracleImpl t).run cache)) :
    ∃ x : Option ι, f (seen A out.2).card (classCounts G out.2 decode)
        (classCounts A out.2 decode) =
      after f (protectedPhase A G t cache) (seen A cache).card
        (classCounts G cache decode) (classCounts A cache decode) x := by
  have h := protected_payoff_support A G hAG decode t cache f out
  rw [WeightedProtectedCache.protectedImpl_eq] at h
  exact h hout

#print axioms actual_query_law
#print axioms actual_payoff_support
end WeightedDualCache
