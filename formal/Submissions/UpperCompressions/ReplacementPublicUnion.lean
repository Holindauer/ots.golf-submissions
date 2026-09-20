import Submissions.UpperCompressions.ReplacementPublicCost

/-! The terminal chosen input is charged to its actual first public query.
This uses the program's query prefix, not membership in a private signer cache. -/

open OracleSpec OracleComp OracleComp.EvalDist ENNReal
open OptimalOTS
namespace WeightedReplacement
noncomputable section
open scoped Classical BigOperators
local instance (priority := 100000) stagedLocal_ReplacementPublicUnion_1 {α : Type*} : DecidableEq α := Classical.decEq α
attribute [local irreducible] hashBits blockBits msgBits signBudget

theorem publicHit_le_one {α : Type} (u : Query) (oa : OracleComp Spec α) (c : Cache) :
    publicHit u oa c ≤ 1 := by
  induction oa using OracleComp.inductionOn generalizing c with
  | pure a => simp
  | query_bind t k ih =>
    rw [publicHit_query]
    split_ifs
    · exact le_rfl
    · exact E_le_one _ (fun p => ih p.1 p.2)

theorem publicHit_query_target {α : Type} (u : Query)
    (k : BitVec hashBits → OracleComp Spec α) (c : Cache) :
    publicHit u (liftM (Spec.query (.inr u)) >>= k) c = 1 := by
  rw [publicHit_query]
  simp

theorem publicHit_hash_target {α : Type} {n : ℕ} (x : BitVec n)
    (k : BitVec hashBits → OracleComp Spec α) (c : Cache) :
    publicHit ⟨n,x⟩ (hash x >>= k) c = 1 := by
  unfold OptimalOTS.hash
  exact publicHit_query_target _ k c

/-- A hit during the continuation is a hit of the whole public program. Hits
that already occurred in the prefix only strengthen this inequality. -/
theorem publicHit_bind_ge {α β : Type} (u : Query) (oa : OracleComp Spec α)
    (k : α → OracleComp Spec β) (c : Cache) :
    E (run oa c) (fun p => publicHit u (k p.1) p.2) ≤ publicHit u (oa >>= k) c := by
  induction oa using OracleComp.inductionOn generalizing c with
  | pure a => simp [run_pure, E_pure]
  | query_bind t next ih =>
    rw [bind_assoc, publicHit_query]
    split_ifs
    · exact E_le_one _ (fun p => publicHit_le_one u (k p.1) p.2)
    · rw [run_query_bind, E_bind]
      exact E_mono _ (fun p => ih p.1 p.2)

/-- If each selected continuation really queries its chosen input, the selected
input event is bounded by the probability of that input's first public query. -/
theorem publicHit_query_output {α β : Type} (u : Query) (chosen : α → Query)
    (oa : OracleComp Spec α) (k : α → OracleComp Spec β) (c : Cache)
    (hquery : ∀ a, chosen a = u → ∀ d, publicHit u (k a) d = 1) :
    E (run oa c) (fun p => if chosen p.1 = u then 1 else 0) ≤ publicHit u (oa >>= k) c := by
  apply (E_mono (run oa c) (fun p => ?_)).trans (publicHit_bind_ge u oa k c)
  by_cases h : chosen p.1 = u
  · rw [if_pos h, hquery p.1 h p.2]
  · rw [if_neg h]
    exact bot_le

/-- Finite union for a forger's actual selected input, provided its continuation
queries that input. Fixed initial-public-cache and signed-input exclusions may
be put in `allowed`; target class membership is `good`. -/
theorem selected_input_union {D α β : Type} [Fintype D]
    (e : D → Query) (chosen : α → D) (allowed good : D → Prop)
    (oa : OracleComp Spec α) (k : α → OracleComp Spec β) (c : Cache)
    (hquery : ∀ a, ∀ d, publicHit (e (chosen a)) (k a) d = 1) :
    E (run oa c) (fun p => if allowed (chosen p.1) ∧ good (chosen p.1) then 1 else 0) ≤
      ∑ d, if allowed d ∧ good d then publicHit (e d) (oa >>= k) c else 0 := by
  have hpoint (p : α × Cache) :
      (if allowed (chosen p.1) ∧ good (chosen p.1) then (1:ℝ≥0∞) else 0) =
      ∑ d, if allowed d ∧ good d then (if chosen p.1 = d then 1 else 0) else 0 := by
    have hh (d : D) :
        (if allowed d ∧ good d then (if chosen p.1 = d then (1:ℝ≥0∞) else 0) else 0) =
        if chosen p.1 = d then (if allowed d ∧ good d then 1 else 0) else 0 := by
      split_ifs <;> rfl
    simp_rw [hh]
    simp
  calc
    _ = E (run oa c) (fun p => ∑ d, if allowed d ∧ good d then (if chosen p.1 = d then 1 else 0) else 0) := by
      congr 1
      funext p
      exact hpoint p
    _ = ∑ d, E (run oa c) (fun p => if allowed d ∧ good d then (if chosen p.1 = d then 1 else 0) else 0) :=
      expectedValue_finsetSum _ _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro d _
      by_cases hd : allowed d ∧ good d
      · simp only [if_pos hd]
        have hdom : E (run oa c) (fun p => if chosen p.1 = d then 1 else 0) ≤
            E (run oa c) (fun p => if e (chosen p.1) = e d then 1 else 0) := E_mono _ (fun p => by
          by_cases hp : chosen p.1 = d
          · simp [hp]
          · simp [hp])
        apply hdom.trans
        apply publicHit_query_output (e d) (e ∘ chosen) oa k c
        intro a ha d'
        exact ha ▸ hquery a d'
      · simp only [if_neg hd]
        exact E_const_le _ 0

#print axioms publicHit_bind_ge
#print axioms publicHit_query_output
#print axioms selected_input_union

end
end WeightedReplacement
