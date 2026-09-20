import Submissions.UpperCompressions.ActualUniformExpectation
import Submissions.UpperCompressions.FiniteCacheCounts

/-! Statistics computed directly from the actual cache, over a finite selected
domain. Unlike an auxiliary counter, their finite-domain bound is immediate. -/
noncomputable section
open OracleSpec OracleComp
open scoped Classical BigOperators
namespace WeightedDirectCache
open WeightedRealExecution WeightedRow.Weights WeightedCacheCounts
set_option maxHeartbeats 800000
variable {D B ι : Type} [DecidableEq D] [Fintype B] [SampleableType B]
  [Fintype ι] [DecidableEq ι]

def fresh (A : Finset D) (q : D) (cache : D → Option B) : Bool :=
  decide (q ∈ A) && (cache q).isNone

/-- Exact one-query class law for the library's actual memoized uniform oracle.
The output alphabet remains generic here to avoid expanding a concrete giant sampler. -/
theorem hash_query_law (w : WeightedRow.Weights ι)
    (A : Finset D) (decode : B → Option ι)
    (hfiber : ∀ x, ((Finset.univ.filter (fun b => decode b=x)).card:ℝ) /
      Fintype.card B = w.classMass x)
    (q : D) (cache : (D →ₒ B).QueryCache) (f : ℕ → (ι → ℕ) → ℝ) :
    realEval (((D →ₒ B).randomOracle q).run cache)
      (fun out => f (seen A out.2).card (classCounts A out.2 decode)) =
    w.expect (fun x => f (step (fresh A q cache) (seen A cache).card (classCounts A cache decode) x).1
      (step (fresh A q cache) (seen A cache).card (classCounts A cache decode) x).2) := by
  rw [randomOracle.run_eq]
  cases hc : cache q with
  | some u => simp [hc, fresh, step, expect_const]
  | none =>
    simp only [realEval_bind, realEval_pure]
    by_cases hq : q ∈ A
    · have hcard (u : B) : (seen A (cache.cacheQuery q u)).card = (seen A cache).card+1 :=
        seen_card_update A cache q u hq hc
      have hcounts (u : B) : classCounts A (cache.cacheQuery q u) decode =
          advance (classCounts A cache decode) (decode u) :=
        classCounts_update_of_mem A cache decode q u hq hc
      simp only [hcard, hcounts, fresh, hq, decide_true, hc, Option.isNone_none,
        Bool.and_self, step, ite_true]
      exact realEval_decoded_uniform w decode hfiber (fun x =>
        f ((seen A cache).card+1) (advance (classCounts A cache decode) x))
    · have hseen (u : B) : seen A (cache.cacheQuery q u) = seen A cache :=
        seen_update_of_not_mem A cache q u hq
      have hcounts (u : B) : classCounts A (cache.cacheQuery q u) decode = classCounts A cache decode :=
        classCounts_update_of_not_mem A cache decode q u hq
      simp only [hseen, hcounts, fresh, hq, decide_false, Bool.false_and,
        step_not_fresh, realEval_const, expect_const]

/-- Generic protected oracle, with free private randomness and the shared cache. -/
def protectedImpl : QueryImpl (unifSpec+(D →ₒ B)) (StateT (D →ₒ B).QueryCache ProbComp) :=
  (HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)).liftTarget
    (StateT (D →ₒ B).QueryCache ProbComp) + (D →ₒ B).randomOracle

def protectedFresh (A : Finset D) (t : (unifSpec+(D →ₒ B)).Domain)
    (cache : (D →ₒ B).QueryCache) : Bool :=
  match t with
  | .inl _ => false
  | .inr q => fresh A q cache

theorem protected_query_law (w : WeightedRow.Weights ι)
    (A : Finset D) (decode : B → Option ι)
    (hfiber : ∀ x, ((Finset.univ.filter (fun b => decode b=x)).card:ℝ) /
      Fintype.card B = w.classMass x)
    (t : (unifSpec+(D →ₒ B)).Domain) (cache : (D →ₒ B).QueryCache)
    (f : ℕ → (ι → ℕ) → ℝ) :
    realEval ((protectedImpl (D := D) (B := B) t).run cache)
      (fun out => f (seen A out.2).card (classCounts A out.2 decode)) =
    w.expect (fun x => f
      (step (protectedFresh A t cache) (seen A cache).card (classCounts A cache decode) x).1
      (step (protectedFresh A t cache) (seen A cache).card (classCounts A cache decode) x).2) := by
  cases t with
  | inl t =>
    simp only [protectedImpl, protectedFresh, step_not_fresh, expect_const]
    change realEval ((liftM (unifSpec.query t) : ProbComp (unifSpec.Range t)) >>=
      fun u => pure (u,cache)) (fun out => f (seen A out.2).card (classCounts A out.2 decode)) = _
    rw [realEval_bind]
    simp only [realEval_pure, realEval_const]
  | inr q => exact hash_query_law w A decode hfiber q cache f

/-- A hash query adds at most one selected cache entry on every supported outcome. -/
theorem hash_count_le_one (A : Finset D) (q : D) (cache : (D →ₒ B).QueryCache)
    (out : B × (D →ₒ B).QueryCache)
    (hout : out ∈ support (((D →ₒ B).randomOracle q).run cache)) :
    (seen A out.2).card ≤ (seen A cache).card+1 := by
  rw [randomOracle.run_eq] at hout
  cases hc : cache q with
  | some u =>
    simp only [hc, support_pure, Set.mem_singleton_iff] at hout
    subst out
    exact Nat.le_succ _
  | none =>
    simp only [hc, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hout
    obtain ⟨u, hu, rfl⟩ := hout
    by_cases hq : q ∈ A
    · exact (seen_card_update A cache q u hq hc).le
    · rw [show seen A (cache.cacheQuery q u) = seen A cache from seen_update_of_not_mem A cache q u hq]
      exact Nat.le_succ _

/-- Free private queries preserve the selected cache count; hashes add at most one. -/
theorem protected_count_le (A : Finset D) (t : (unifSpec+(D →ₒ B)).Domain)
    (cache : (D →ₒ B).QueryCache) (out : (unifSpec+(D →ₒ B)).Range t × (D →ₒ B).QueryCache)
    (hout : out ∈ support ((protectedImpl (D := D) (B := B) t).run cache)) :
    (seen A out.2).card ≤ (seen A cache).card+(if t.isRight then 1 else 0) := by
  cases t with
  | inl t =>
    change out ∈ support ((liftM (unifSpec.query t) : ProbComp (unifSpec.Range t)) >>=
      fun u => pure (u,cache)) at hout
    obtain ⟨u, hu, hp⟩ := (mem_support_bind_iff _ _ _).1 hout
    simp only [support_pure, Set.mem_singleton_iff] at hp
    subst out
    simp
  | inr q => exact hash_count_le_one A q cache out hout

#print axioms hash_count_le_one
#print axioms protected_count_le

#print axioms protected_query_law

#print axioms hash_query_law
end WeightedDirectCache
