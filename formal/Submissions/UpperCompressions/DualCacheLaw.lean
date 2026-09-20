import Submissions.UpperCompressions.DirectCacheLaw
import Submissions.UpperCompressions.WideCountRelations

/-! Joint row/global statistics use a single actual decoded oracle answer. -/
noncomputable section
open OracleSpec OracleComp
open scoped Classical
namespace WeightedDualCache
open WeightedRealExecution WeightedRow.Weights WeightedCacheCounts
set_option maxHeartbeats 800000
variable {D B ι : Type} [DecidableEq D] [Fintype B] [SampleableType B]
  [Fintype ι] [DecidableEq ι]

inductive Phase where
  | idle | outside | inside
  deriving DecidableEq

def phase (A G : Finset D) (q : D) (cache : D → Option B) : Phase :=
  if (cache q).isSome then .idle else
  if q ∈ A then .inside else if q ∈ G then .outside else .idle

def protectedPhase (A G : Finset D) (t : (unifSpec+(D →ₒ B)).Domain)
    (cache : (D →ₒ B).QueryCache) : Phase :=
  match t with
  | .inl _ => .idle
  | .inr q => phase A G q cache

def after (f : ℕ → (ι → ℕ) → (ι → ℕ) → ℝ)
    (s : Phase) (r : ℕ) (k row : ι → ℕ) : Option ι → ℝ :=
  match s with
  | .idle => fun _ => f r k row
  | .outside => fun x => f r (advance k x) row
  | .inside => fun x => f (r+1) (advance k x) (advance row x)

theorem after_comp (f : ℝ → ℝ) (g : ℕ → (ι → ℕ) → (ι → ℕ) → ℝ)
    (s : Phase) (r : ℕ) (k row : ι → ℕ) :
    after (fun r k row => f (g r k row)) s r k row =
      fun x => f (after g s r k row x) := by
  cases s <;> rfl

theorem hash_query_law (w : WeightedRow.Weights ι)
    (A G : Finset D) (hAG : A ⊆ G) (decode : B → Option ι)
    (hfiber : ∀ x, ((Finset.univ.filter (fun b => decode b=x)).card:ℝ) /
      Fintype.card B = w.classMass x)
    (q : D) (cache : (D →ₒ B).QueryCache)
    (f : ℕ → (ι → ℕ) → (ι → ℕ) → ℝ) :
    realEval (((D →ₒ B).randomOracle q).run cache)
      (fun out => f (seen A out.2).card (classCounts G out.2 decode)
        (classCounts A out.2 decode)) =
    w.expect (after f (phase A G q cache) (seen A cache).card
      (classCounts G cache decode) (classCounts A cache decode)) := by
  rw [randomOracle.run_eq]
  cases hc : cache q with
  | some u => simp [hc, phase, after, expect_const]
  | none =>
    simp only [realEval_bind, realEval_pure]
    by_cases hqA : q ∈ A
    · have hqG := hAG hqA
      have hr (u : B) : (seen A (cache.cacheQuery q u)).card =
          (seen A cache).card+1 := seen_card_update A cache q u hqA hc
      have hk (u : B) : classCounts G (cache.cacheQuery q u) decode =
          advance (classCounts G cache decode) (decode u) :=
        classCounts_update_of_mem G cache decode q u hqG hc
      have hrow (u : B) : classCounts A (cache.cacheQuery q u) decode =
          advance (classCounts A cache decode) (decode u) :=
        classCounts_update_of_mem A cache decode q u hqA hc
      simp only [hr, hk, hrow, phase, hc, Option.isSome_none, Bool.false_eq_true,
        ite_false, hqA, ite_true, after]
      exact realEval_decoded_uniform w decode hfiber (fun x =>
        f ((seen A cache).card+1) (advance (classCounts G cache decode) x)
          (advance (classCounts A cache decode) x))
    · have hr (u : B) : seen A (cache.cacheQuery q u) = seen A cache :=
        seen_update_of_not_mem A cache q u hqA
      have hrow (u : B) : classCounts A (cache.cacheQuery q u) decode =
          classCounts A cache decode := classCounts_update_of_not_mem A cache decode q u hqA
      by_cases hqG : q ∈ G
      · have hk (u : B) : classCounts G (cache.cacheQuery q u) decode =
            advance (classCounts G cache decode) (decode u) :=
          classCounts_update_of_mem G cache decode q u hqG hc
        simp only [hr, hk, hrow, phase, hc, Option.isSome_none, Bool.false_eq_true,
          ite_false, hqA, hqG, ite_true, after]
        exact realEval_decoded_uniform w decode hfiber (fun x =>
          f (seen A cache).card (advance (classCounts G cache decode) x)
            (classCounts A cache decode))
      · have hk (u : B) : classCounts G (cache.cacheQuery q u) decode =
            classCounts G cache decode := classCounts_update_of_not_mem G cache decode q u hqG
        simp only [hr, hk, hrow, phase, hc, Option.isSome_none, Bool.false_eq_true,
          ite_false, hqA, hqG, after, realEval_const, expect_const]

theorem protected_query_law (w : WeightedRow.Weights ι)
    (A G : Finset D) (hAG : A ⊆ G) (decode : B → Option ι)
    (hfiber : ∀ x, ((Finset.univ.filter (fun b => decode b=x)).card:ℝ) /
      Fintype.card B = w.classMass x)
    (t : (unifSpec+(D →ₒ B)).Domain) (cache : (D →ₒ B).QueryCache)
    (f : ℕ → (ι → ℕ) → (ι → ℕ) → ℝ) :
    realEval ((WeightedDirectCache.protectedImpl (D := D) (B := B) t).run cache)
      (fun out => f (seen A out.2).card (classCounts G out.2 decode)
        (classCounts A out.2 decode)) =
    w.expect (after f (protectedPhase A G t cache) (seen A cache).card
      (classCounts G cache decode) (classCounts A cache decode)) := by
  cases t with
  | inl t =>
    simp only [WeightedDirectCache.protectedImpl, protectedPhase, after, expect_const]
    change realEval ((liftM (unifSpec.query t) : ProbComp (unifSpec.Range t)) >>=
      fun u => pure (u,cache)) (fun out => f (seen A out.2).card
        (classCounts G out.2 decode) (classCounts A out.2 decode)) = _
    rw [realEval_bind]
    simp only [realEval_pure, realEval_const]
  | inr q => exact hash_query_law w A G hAG decode hfiber q cache f

#print axioms protected_query_law
end WeightedDualCache
