import Submissions.UpperCompressions.DirectCacheLaw
import Submissions.UpperCompressions.ActualScoreConcentration

/-! The actual protected shared-oracle implementation, with statistics defined
from its cache rather than from an auxiliary execution law. A finite selected
input domain A provides the fresh-count cap by definition. All initial selected
entries must be absent when these counts represent a pre-sign public transcript.
Private signing entries invalidate a post-sign public-fresh interpretation. -/
noncomputable section
open OracleSpec OracleComp
open scoped Classical BigOperators
namespace WeightedProtectedCache
open WeightedRealExecution WeightedRow.Weights WeightedCacheCounts WeightedDirectCache
set_option maxHeartbeats 800000
variable {ι α : Type} [Fintype ι] [DecidableEq ι]

/-- The generic protected implementation specializes exactly to the contract. -/
theorem protectedImpl_eq :
    protectedImpl (D := OptimalOTS.Query) (B := BitVec OptimalOTS.hashBits) = OptimalOTS.oracleImpl := rfl

/-- Exact primitive-query class law for the contract's actual shared oracle. -/
theorem query_law (w : WeightedRow.Weights ι)
    (A : Finset OptimalOTS.Query) (decode : BitVec OptimalOTS.hashBits → Option ι)
    (hfiber : ∀ x, ((Finset.univ.filter (fun b => decode b=x)).card:ℝ) /
      Fintype.card (BitVec OptimalOTS.hashBits) = w.classMass x)
    (t : OptimalOTS.Spec.Domain) (cache : OptimalOTS.hashSpec.QueryCache)
    (f : ℕ → (ι → ℕ) → ℝ) :
    realEval ((OptimalOTS.oracleImpl t).run cache)
      (fun out => f (seen A out.2).card (classCounts A out.2 decode)) =
    w.expect (fun x => f
      (step (protectedFresh A t cache) (seen A cache).card (classCounts A cache decode) x).1
      (step (protectedFresh A t cache) (seen A cache).card (classCounts A cache decode) x).2) := by
  have h := protected_query_law w A decode hfiber t cache f
  rw [protectedImpl_eq] at h
  exact h

/-- Each newly cached selected hash is charged to a paid primitive query. -/
theorem count_le_cost (A : Finset OptimalOTS.Query) (t : OptimalOTS.Spec.Domain)
    (cache : OptimalOTS.hashSpec.QueryCache)
    (out : OptimalOTS.Spec.Range t × OptimalOTS.hashSpec.QueryCache)
    (hout : out ∈ support ((OptimalOTS.oracleImpl t).run cache)) :
    (seen A out.2).card ≤ (seen A cache).card+OptimalOTS.queryCost t := by
  have h := protected_count_le A t cache out
  rw [protectedImpl_eq] at h
  have hc : (if t.isRight then 1 else 0) ≤ OptimalOTS.queryCost t := by
    cases t with
    | inl n => simp [OptimalOTS.queryCost]
    | inr q => exact Nat.le_max_left 1 _
  exact (h hout).trans (Nat.add_le_add_left hc _)

/-- Actual execution respects both the finite domain and the paid budget,
including arbitrary initial selected-cache contents and free private randomness. -/
theorem count_bound (A : Finset OptimalOTS.Query)
    (oa : OracleComp OptimalOTS.Spec α) (B : ℕ) (hbudget : OptimalOTS.CostAtMost oa B)
    (cache : OptimalOTS.hashSpec.QueryCache) (out : α × OptimalOTS.hashSpec.QueryCache)
    (hout : out ∈ support ((simulateQ OptimalOTS.oracleImpl oa).run cache)) :
    (seen A out.2).card ≤ min A.card ((seen A cache).card+B) := by
  apply le_min (seen_card_le A out.2)
  have hstep : ∀ t c z, z ∈ support ((OptimalOTS.oracleImpl t).run c) →
      ((seen A z.2).card:ℝ) ≤ ((seen A c).card:ℝ)+1*(OptimalOTS.queryCost t:ℝ) := by
    intro t c z hz
    norm_num only [one_mul]
    exact_mod_cast count_le_cost A t c z hz
  have h := WeightedOracleExecution.state_bound_of_protected_budget OptimalOTS.oracleImpl
    (fun c => ((seen A c).card:ℝ)) 1 zero_le_one hstep oa B hbudget cache out hout
  norm_num only [one_mul] at h
  exact_mod_cast h

/-- All stopped moment hypotheses follow from actual shared-oracle execution. -/
theorem stopped_moments (w : WeightedRow.Weights ι)
    (A : Finset OptimalOTS.Query) (decode : BitVec OptimalOTS.hashBits → Option ι)
    (hfiber : ∀ x, ((Finset.univ.filter (fun b => decode b=x)).card:ℝ) /
      Fintype.card (BitVec OptimalOTS.hashBits) = w.classMass x)
    (G : ℝ) (hG : 0 ≤ G) (hg : ∀ i, w.g i ≤ G)
    (oa : OracleComp OptimalOTS.Spec α) (B : ℕ) (hbudget : OptimalOTS.CostAtMost oa B)
    (cache : OptimalOTS.hashSpec.QueryCache)
    (hq0 : (seen A cache).card = 0) (hk0 : classCounts A cache decode = fun _ => 0) :
    let run := (simulateQ OptimalOTS.oracleImpl oa).run cache
    realEval run (fun out => w.M1 (seen A out.2).card (classCounts A out.2 decode)) = 0 ∧
    realEval run (fun out => w.M2 (seen A out.2).card (classCounts A out.2 decode)) = 0 ∧
    realEval run (fun out => (w.M1 (seen A out.2).card (classCounts A out.2 decode))^2) ≤
      (B:ℝ)*G*w.mean := by
  exact WeightedActualMoments.actual_stopped_moments w OptimalOTS.oracleImpl
    (fun c => (seen A c).card) (fun c => classCounts A c decode)
    (protectedFresh A) (query_law w A decode hfiber) (count_le_cost A)
    G hG hg oa B hbudget cache hq0 hk0

#print axioms count_le_cost
#print axioms count_bound
#print axioms stopped_moments

#print axioms protectedImpl_eq
#print axioms query_law
end WeightedProtectedCache
