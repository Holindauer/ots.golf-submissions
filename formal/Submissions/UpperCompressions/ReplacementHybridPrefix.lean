import Submissions.UpperCompressions.ReplacementPrefix

/-! Stopped public prefixes under the actual mixed lazy oracle. Only the
distinguished request is intercepted; every answered query uses oracleImpl.
The final implementation cache is hidden, while all public answers and coins
are retained. Privately cached answers therefore need no fresh-draw fiction. -/

open OracleSpec OracleComp OracleComp.EvalDist ENNReal
open OptimalOTS
namespace WeightedReplacement
noncomputable section
open scoped Classical
local instance stagedLocal_ReplacementHybridPrefix_1 {α : Type*} : DecidableEq α := Classical.decEq α

def overwrite (c : Cache) (u : Query) (y : BitVec hashBits) : Cache :=
  Function.update c u (some y)

theorem overwrite_cacheQuery (c : Cache) (u q : Query) (y w : BitVec hashBits)
    (hqu : q ≠ u) :
    (overwrite c u y).cacheQuery q w = overwrite (c.cacheQuery q w) u y := by
  funext r
  by_cases hrq : r = q
  · subst r
    simp [overwrite, Function.update_of_ne hqu]
  · by_cases hru : r = u
    · subst r
      simp [overwrite, QueryCache.cacheQuery_of_ne _ _ hrq]
    · simp [overwrite, QueryCache.cacheQuery_of_ne _ _ hrq, Function.update_of_ne hru]

theorem oracleImpl_overwrite (u q : Query) (hqu : q ≠ u)
    (c : Cache) (y : BitVec hashBits) :
    (oracleImpl (.inr q)).run (overwrite c u y) =
      (fun p => (p.1, overwrite p.2 u y)) <$> (oracleImpl (.inr q)).run c := by
  have hlookup : overwrite c u y q = c q := Function.update_of_ne hqu _ _
  cases hc : c q with
  | none =>
    have ho : overwrite c u y q = none := hlookup.trans hc
    rw [oracleImpl_run_inr_none hc, oracleImpl_run_inr_none ho]
    simp only [map_bind, map_pure]
    apply bind_congr
    intro w
    rw [overwrite_cacheQuery c u q y w hqu]
  | some w =>
    have ho : overwrite c u y q = some w := hlookup.trans hc
    rw [oracleImpl_run_inr_some hc, oracleImpl_run_inr_some ho, map_pure]

/-- All actual oracle responses before the first public request to u. Returning
none means u was requested, and its answer has not been exposed. -/
def hybridPrefix {α : Type} (u : Query) (oa : OracleComp Spec α) :
    Cache → PublicTrace → ProbComp (Option α × PublicTrace) :=
  OracleComp.construct (fun a _ tr => pure (some a, tr))
    (fun t _ rec c tr => match t with
      | .inl n => do
          let a ← HasQuery.query (spec := unifSpec) (m := ProbComp) n
          rec a c (⟨.inl n, a⟩ :: tr)
      | .inr q => if q = u then pure (none, tr) else do
          let p ← (oracleImpl (.inr q)).run c
          rec p.1 p.2 (⟨.inr q, p.1⟩ :: tr)) oa

theorem hybridPrefix_pure {α : Type} (u : Query) (a : α) (c : Cache) (tr : PublicTrace) :
    hybridPrefix u (pure a) c tr = pure (some a, tr) := by simp [hybridPrefix]

theorem hybridPrefix_unif {α : Type} (u : Query) (n : ℕ)
    (k : Spec.Range (.inl n) → OracleComp Spec α) (c : Cache) (tr : PublicTrace) :
    hybridPrefix u (liftM (Spec.query (.inl n)) >>= k) c tr =
      (HasQuery.query (spec := unifSpec) (m := ProbComp) n) >>= fun a =>
        hybridPrefix u (k a) c (⟨.inl n,a⟩ :: tr) := by simp [hybridPrefix]

theorem hybridPrefix_target {α : Type} (u : Query)
    (k : BitVec hashBits → OracleComp Spec α) (c : Cache) (tr : PublicTrace) :
    hybridPrefix u (liftM (Spec.query (.inr u)) >>= k) c tr = pure (none,tr) := by
  simp [hybridPrefix]

theorem hybridPrefix_hash {α : Type} (u q : Query) (hqu : q ≠ u)
    (k : BitVec hashBits → OracleComp Spec α) (c : Cache) (tr : PublicTrace) :
    hybridPrefix u (liftM (Spec.query (.inr q)) >>= k) c tr =
      (oracleImpl (.inr q)).run c >>= fun p =>
        hybridPrefix u (k p.1) p.2 (⟨.inr q,p.1⟩ :: tr) := by
  simp [hybridPrefix, hqu]

/-- The entire stopped public-prefix distribution is unchanged by overwriting
the distinguished cache cell, whether originally absent or privately cached. -/
theorem hybridPrefix_overwrite {α : Type} (u : Query) (oa : OracleComp Spec α)
    (c : Cache) (tr : PublicTrace) (y : BitVec hashBits) :
    hybridPrefix u oa (overwrite c u y) tr = hybridPrefix u oa c tr := by
  induction oa using OracleComp.inductionOn generalizing c tr with
  | pure a => rw [hybridPrefix_pure, hybridPrefix_pure]
  | query_bind t k ih =>
    cases t with
    | inl n =>
      rw [hybridPrefix_unif, hybridPrefix_unif]
      exact bind_congr fun a => ih a c _
    | inr q =>
      by_cases hqu : q = u
      · subst q
        rw [hybridPrefix_target, hybridPrefix_target]
      · rw [hybridPrefix_hash u q hqu, hybridPrefix_hash u q hqu,
          oracleImpl_overwrite u q hqu]
        simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def]
        apply bind_congr
        intro p
        exact ih p.1 p.2 _

theorem hybridPrefix_event_overwrite {α : Type} (u : Query) (oa : OracleComp Spec α)
    (c : Cache) (tr : PublicTrace) (y : BitVec hashBits)
    (event : Option α × PublicTrace → Prop) :
    E (hybridPrefix u oa (overwrite c u y) tr) (fun p => if event p then 1 else 0) =
      E (hybridPrefix u oa c tr) (fun p => if event p then 1 else 0) := by
  rw [hybridPrefix_overwrite]

#print axioms oracleImpl_overwrite
#print axioms hybridPrefix_overwrite

end
end WeightedReplacement
