import Submissions.UpperCompressions.ReplacementProgram
import VCVio.OracleComp.QueryTracking.RandomOracle.EagerTable

/-! Exact finite-subset eager preloading for the protected shared-cache oracle.
All executions still use `OptimalOTS.run` and its original `oracleImpl`; inputs
outside the distinguished subset are neither split off nor resampled separately. -/

open OracleSpec OracleComp OracleComp.EvalDist ENNReal
open OptimalOTS

namespace WeightedReplacement

noncomputable section
open scoped Classical
local instance stagedLocal_ReplacementPreload_1 {α : Type*} : DecidableEq α := Classical.decEq α

/-- A finite set of distinguished query coordinates. Distinct queries cannot
name the same coordinate; unused coordinates are harmless. -/
structure QuerySlice (D : Type) where
  locate : Query → Option D
  unique : ∀ {q q' : Query} {d : D}, locate q = some d → locate q' = some d → q = q'

namespace QuerySlice

def tableCache {D : Type} (S : QuerySlice D) (g : D → BitVec hashBits) : Cache :=
  fun q => g <$> S.locate q

def preload {D : Type} (S : QuerySlice D) (c : Cache) (g : D → BitVec hashBits) : Cache :=
  Cache.extend c (S.tableCache g)

theorem preload_some {D : Type} (S : QuerySlice D) (c : Cache)
    (g : D → BitVec hashBits) (q : Query) (y : BitVec hashBits) (hc : c q = some y) :
    S.preload c g q = some y := by simp [preload, Cache.extend, hc]

theorem preload_outside {D : Type} (S : QuerySlice D) (c : Cache)
    (g : D → BitVec hashBits) (q : Query) (hq : S.locate q = none) :
    S.preload c g q = c q := by simp [preload, Cache.extend, tableCache, hq]

theorem preload_fresh_inside {D : Type} (S : QuerySlice D) (c : Cache)
    (g : D → BitVec hashBits) (q : Query) (d : D)
    (hc : c q = none) (hq : S.locate q = some d) :
    S.preload c g q = some (g d) := by simp [preload, Cache.extend, tableCache, hc, hq]

theorem preload_cacheQuery {D : Type} (S : QuerySlice D) (c : Cache)
    (g : D → BitVec hashBits) (q : Query) (y : BitVec hashBits) :
    S.preload (c.cacheQuery q y) g = (S.preload c g).cacheQuery q y :=
  Cache.extend_cacheQuery c (S.tableCache g) q y

theorem preload_update_of_none {D : Type} (S : QuerySlice D) (c : Cache)
    (g : D → BitVec hashBits) (q : Query) (d : D) (y : BitVec hashBits)
    (hc : c q = none) (hq : S.locate q = some d) :
    S.preload (c.cacheQuery q y) g = S.preload c (Function.update g d y) := by
  funext q'
  by_cases hqq : q' = q
  · subst q'
    simp [preload, Cache.extend, tableCache, hc, hq]
  · simp only [preload, Cache.extend, QueryCache.cacheQuery_of_ne _ _ hqq]
    apply congrArg (fun x => (c q').or x)
    cases hx : S.locate q' with
    | none => simp [tableCache, hx]
    | some d' =>
      have hdd : d' ≠ d := by
        intro hd
        subst d'
        exact hqq (S.unique hx hq)
      simp [tableCache, hx, Function.update_of_ne hdd]

end QuerySlice

theorem E_independent_swap {α β : Type} (p : ProbComp α) (q : ProbComp β)
    (f : α → β → ℝ≥0∞) :
    E p (fun a => E q (fun b => f a b)) = E q (fun b => E p (fun a => f a b)) := by
  simp only [E, expectedValue_def, ← ENNReal.tsum_mul_left]
  rw [ENNReal.tsum_comm]
  exact tsum_congr fun b => tsum_congr fun a => by ring

theorem E_uniform_constant (α : Type) [SampleableType α] (c : ℝ≥0∞) :
    E ($ᵗ α) (fun _ => c) = c :=
  expectedValue_const (by simp) c

/-- Eager-table marginalization from the existing VCVio theorem, expressed as an
expectation identity usable with arbitrary probabilistic continuations. -/
theorem E_uniform_update {D : Type} [Fintype D] [SampleableType (D → BitVec hashBits)]
    (d : D) (f : (D → BitVec hashBits) → ℝ≥0∞) :
    E ($ᵗ BitVec hashBits) (fun y => E ($ᵗ (D → BitVec hashBits))
      (fun g => f (Function.update g d y))) = E ($ᵗ (D → BitVec hashBits)) f := by
  have hd := OracleComp.evalSPMF_uniformSample_bind_update_map
    (R := BitVec hashBits) d (fun g : D → BitVec hashBits => g)
  have he : E (do
      let y ← $ᵗ BitVec hashBits
      let g ← $ᵗ (D → BitVec hashBits)
      pure (Function.update g d y)) f = E ($ᵗ (D → BitVec hashBits)) f := by
    apply expectedValue_congr
    intro g
    simp only [probOutput_def]
    simpa only [bind_pure] using congrArg (fun p : SPMF (D → BitVec hashBits) => p g) hd
  simpa only [E_bind, E_pure] using he

abbrev outE {α : Type} (oa : OracleComp Spec α) (c : Cache) (f : α → ℝ≥0∞) : ℝ≥0∞ :=
  E (run oa c) (fun p => f p.1)

theorem outE_pure {α : Type} (a : α) (c : Cache) (f : α → ℝ≥0∞) :
    outE (pure a) c f = f a := by rw [outE, run_pure, E_pure]

theorem outE_unif {α : Type} (n : ℕ) (k : Spec.Range (.inl n) → OracleComp Spec α)
    (c : Cache) (f : α → ℝ≥0∞) :
    outE (liftM (Spec.query (.inl n)) >>= k) c f =
      E (HasQuery.query (spec := unifSpec) (m := ProbComp) n) (fun a => outE (k a) c f) := by
  simp only [outE, run_query_bind, oracleImpl_run_inl, E_bind, E_pure]

theorem outE_hash_none {α : Type} (q : Query)
    (k : BitVec hashBits → OracleComp Spec α) (c : Cache) (f : α → ℝ≥0∞)
    (hc : c q = none) :
    outE (liftM (Spec.query (.inr q)) >>= k) c f =
      E ($ᵗ BitVec hashBits) (fun y => outE (k y) (c.cacheQuery q y) f) := by
  simp only [outE, run_query_bind, oracleImpl_run_inr_none hc, E_bind, E_pure]

theorem outE_hash_some {α : Type} (q : Query)
    (k : BitVec hashBits → OracleComp Spec α) (c : Cache) (f : α → ℝ≥0∞)
    (y : BitVec hashBits) (hc : c q = some y) :
    outE (liftM (Spec.query (.inr q)) >>= k) c f = outE (k y) c f := by
  simp only [outE, run_query_bind, oracleImpl_run_inr_some hc, pure_bind]

/-- Exact hybrid lazy/eager equivalence for any distinguished finite query subset.
Only the subset is preloaded. The computation and every other query still run
through the original protected shared-cache interpreter. The final cache is
hidden; this theorem equates every payoff of the actual program's output. -/
theorem outE_finite_preload {D α : Type} [Fintype D]
    [SampleableType (D → BitVec hashBits)] (S : QuerySlice D)
    (oa : OracleComp Spec α) (c : Cache) (f : α → ℝ≥0∞) :
    outE oa c f = E ($ᵗ (D → BitVec hashBits)) (fun g => outE oa (S.preload c g) f) := by
  induction oa using OracleComp.inductionOn generalizing c with
  | pure a =>
    simp only [outE_pure]
    exact (E_uniform_constant _ _).symm
  | query_bind t k ih =>
    cases t with
    | inl n =>
      rw [outE_unif]
      calc
        _ = E (HasQuery.query (spec := unifSpec) (m := ProbComp) n)
            (fun a => E ($ᵗ (D → BitVec hashBits))
              (fun g => outE (k a) (S.preload c g) f)) := by
          congr 1
          funext a
          exact ih a c
        _ = E ($ᵗ (D → BitVec hashBits))
            (fun g => E (HasQuery.query (spec := unifSpec) (m := ProbComp) n)
              (fun a => outE (k a) (S.preload c g) f)) := E_independent_swap _ _ _
        _ = _ := by
          congr 1
          funext g
          rw [outE_unif]
    | inr q =>
      cases hc : c q with
      | some y =>
        rw [outE_hash_some q k c f y hc]
        calc
          _ = E ($ᵗ (D → BitVec hashBits)) (fun g => outE (k y) (S.preload c g) f) := ih y c
          _ = _ := by
            congr 1
            funext g
            rw [outE_hash_some q k (S.preload c g) f y (S.preload_some c g q y hc)]
      | none =>
        rw [outE_hash_none q k c f hc]
        cases hq : S.locate q with
        | none =>
          calc
            _ = E ($ᵗ BitVec hashBits) (fun y => E ($ᵗ (D → BitVec hashBits))
                (fun g => outE (k y) (S.preload (c.cacheQuery q y) g) f)) := by
              congr 1
              funext y
              exact ih y (c.cacheQuery q y)
            _ = E ($ᵗ (D → BitVec hashBits)) (fun g => E ($ᵗ BitVec hashBits)
                (fun y => outE (k y) (S.preload (c.cacheQuery q y) g) f)) :=
              E_independent_swap _ _ _
            _ = _ := by
              congr 1
              funext g
              have hg : S.preload c g q = none := (S.preload_outside c g q hq).trans hc
              rw [outE_hash_none q k (S.preload c g) f hg]
              congr 1
              funext y
              rw [S.preload_cacheQuery]
        | some d =>
          let ψ : (D → BitVec hashBits) → ℝ≥0∞ :=
            fun g => outE (k (g d)) (S.preload c g) f
          have he (y : BitVec hashBits) (g : D → BitVec hashBits) :
              outE (k y) (S.preload (c.cacheQuery q y) g) f = ψ (Function.update g d y) := by
            dsimp only [ψ]
            rw [Function.update_self, S.preload_update_of_none c g q d y hc hq]
          calc
            _ = E ($ᵗ BitVec hashBits) (fun y => E ($ᵗ (D → BitVec hashBits))
                (fun g => ψ (Function.update g d y))) := by
              congr 1
              funext y
              rw [ih y (c.cacheQuery q y)]
              congr 1
              funext g
              exact he y g
            _ = E ($ᵗ (D → BitVec hashBits)) ψ := E_uniform_update d ψ
            _ = _ := by
              congr 1
              funext g
              exact (outE_hash_some q k (S.preload c g) f (g d)
                (S.preload_fresh_inside c g q d hc hq)).symm

#print axioms QuerySlice.preload_update_of_none
#print axioms E_uniform_update
#print axioms outE_finite_preload

end
end WeightedReplacement
