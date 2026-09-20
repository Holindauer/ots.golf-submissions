import Submissions.UpperCompressions.ReplacementLengthSlice

/-! Exact conditional-completion tower for cache-sensitive terminal payoffs.
The lazy side retains the actual observed cache, then completes its unqueried
finite coordinates uniformly. The eager side samples once before execution. -/
open OracleSpec OracleComp OracleComp.EvalDist ENNReal
open OptimalOTS
namespace WeightedReplacement
noncomputable section
open scoped Classical
local instance stagedLocal_ReplacementCompletion_1 {α : Type*} : DecidableEq α := Classical.decEq α

abbrev cacheE {α : Type} (oa : OracleComp Spec α) (c : Cache)
    (f : α → Cache → ℝ≥0∞) : ℝ≥0∞ := E (run oa c) (fun p => f p.1 p.2)

def completePayoff {D α : Type} [Fintype D] [SampleableType (D → BitVec hashBits)]
    (S : QuerySlice D) (f : α → Cache → ℝ≥0∞) (a : α) (c : Cache) : ℝ≥0∞ :=
  E ($ᵗ (D → BitVec hashBits)) (fun g => f a (S.preload c g))

theorem cacheE_pure {α : Type} (a : α) (c : Cache) (f : α → Cache → ℝ≥0∞) :
    cacheE (pure a) c f = f a c := by rw [cacheE, run_pure, E_pure]

theorem cacheE_unif {α : Type} (n : ℕ) (k : Spec.Range (.inl n) → OracleComp Spec α)
    (c : Cache) (f : α → Cache → ℝ≥0∞) :
    cacheE (liftM (Spec.query (.inl n)) >>= k) c f =
      E (HasQuery.query (spec := unifSpec) (m := ProbComp) n) (fun a => cacheE (k a) c f) := by
  simp only [cacheE, run_query_bind, oracleImpl_run_inl, E_bind, E_pure]

theorem cacheE_hash_none {α : Type} (q : Query)
    (k : BitVec hashBits → OracleComp Spec α) (c : Cache) (f : α → Cache → ℝ≥0∞)
    (hc : c q = none) :
    cacheE (liftM (Spec.query (.inr q)) >>= k) c f =
      E ($ᵗ BitVec hashBits) (fun y => cacheE (k y) (c.cacheQuery q y) f) := by
  simp only [cacheE, run_query_bind, oracleImpl_run_inr_none hc, E_bind, E_pure]

theorem cacheE_hash_some {α : Type} (q : Query)
    (k : BitVec hashBits → OracleComp Spec α) (c : Cache) (f : α → Cache → ℝ≥0∞)
    (y : BitVec hashBits) (hc : c q = some y) :
    cacheE (liftM (Spec.query (.inr q)) >>= k) c f = cacheE (k y) c f := by
  simp only [cacheE, run_query_bind, oracleImpl_run_inr_some hc, pure_bind]

/-- Uniform completion after the actual lazy execution equals sampling the
same finite table before execution, for arbitrary output-and-cache payoffs. -/
theorem cacheE_finite_completion {D α : Type} [Fintype D]
    [SampleableType (D → BitVec hashBits)] (S : QuerySlice D)
    (oa : OracleComp Spec α) (c : Cache) (f : α → Cache → ℝ≥0∞) :
    cacheE oa c (completePayoff S f) =
      E ($ᵗ (D → BitVec hashBits)) (fun g => cacheE oa (S.preload c g) f) := by
  induction oa using OracleComp.inductionOn generalizing c with
  | pure a =>
    simp only [cacheE_pure]
    rfl
  | query_bind t k ih =>
    cases t with
    | inl n =>
      rw [cacheE_unif]
      calc
        _ = E (HasQuery.query (spec := unifSpec) (m := ProbComp) n)
            (fun a => E ($ᵗ (D → BitVec hashBits))
              (fun g => cacheE (k a) (S.preload c g) f)) := by
          congr 1
          funext a
          exact ih a c
        _ = E ($ᵗ (D → BitVec hashBits))
            (fun g => E (HasQuery.query (spec := unifSpec) (m := ProbComp) n)
              (fun a => cacheE (k a) (S.preload c g) f)) := E_independent_swap _ _ _
        _ = _ := by
          congr 1
          funext g
          rw [cacheE_unif]
    | inr q =>
      cases hc : c q with
      | some y =>
        rw [cacheE_hash_some q k c (completePayoff S f) y hc]
        calc
          _ = E ($ᵗ (D → BitVec hashBits)) (fun g => cacheE (k y) (S.preload c g) f) := ih y c
          _ = _ := by
            congr 1
            funext g
            rw [cacheE_hash_some q k (S.preload c g) f y (S.preload_some c g q y hc)]
      | none =>
        rw [cacheE_hash_none q k c (completePayoff S f) hc]
        cases hq : S.locate q with
        | none =>
          calc
            _ = E ($ᵗ BitVec hashBits) (fun y => E ($ᵗ (D → BitVec hashBits))
                (fun g => cacheE (k y) (S.preload (c.cacheQuery q y) g) f)) := by
              congr 1
              funext y
              exact ih y (c.cacheQuery q y)
            _ = E ($ᵗ (D → BitVec hashBits)) (fun g => E ($ᵗ BitVec hashBits)
                (fun y => cacheE (k y) (S.preload (c.cacheQuery q y) g) f)) :=
              E_independent_swap _ _ _
            _ = _ := by
              congr 1
              funext g
              have hg : S.preload c g q = none := (S.preload_outside c g q hq).trans hc
              rw [cacheE_hash_none q k (S.preload c g) f hg]
              congr 1
              funext y
              rw [S.preload_cacheQuery]
        | some d =>
          let ψ : (D → BitVec hashBits) → ℝ≥0∞ :=
            fun g => cacheE (k (g d)) (S.preload c g) f
          have he (y : BitVec hashBits) (g : D → BitVec hashBits) :
              cacheE (k y) (S.preload (c.cacheQuery q y) g) f = ψ (Function.update g d y) := by
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
              exact (cacheE_hash_some q k (S.preload c g) f (g d)
                (S.preload_fresh_inside c g q d hc hq)).symm


#print axioms cacheE_finite_completion
end
end WeightedReplacement
