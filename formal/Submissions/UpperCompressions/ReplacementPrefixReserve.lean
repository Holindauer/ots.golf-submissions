import Submissions.UpperCompressions.ReplacementSupportReserve

/-! A mandatory continuation reserve is unavailable to the public prefix on
every raw query-answer path, not just on average. -/
open OracleSpec OracleComp
open OptimalOTS OptimalOTS.AlgorithmCosts
namespace WeightedReplacement
noncomputable section
open scoped Classical

theorem costAtMost_prefix_reserved {α β : Type} (oa : OracleComp Spec α)
    (k : α → OracleComp Spec β) (R : ℕ)
    (hR : ∀ a b, CostAtMost (k a) b → R ≤ b) :
    ∀ b, CostAtMost (oa >>= k) b → R ≤ b ∧ CostAtMost oa (b-R) := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro b hB
    rw [pure_bind] at hB
    exact ⟨hR a b hB,costAtMost_pure _ _⟩
  | query_bind t f ih =>
    intro b hB
    rw [bind_assoc,costAtMost_query_bind_iff] at hB
    have hs (u : Spec.Range t) := ih u (b-queryCost t) (hB.2 u)
    haveI : Nonempty (Spec.Range t) := by cases t <;> infer_instance
    have hr := (hs (Classical.arbitrary (Spec.Range t))).1
    refine ⟨by omega,?_⟩
    rw [costAtMost_query_bind_iff]
    refine ⟨by omega,fun u => ?_⟩
    simpa only [Nat.sub_sub,Nat.add_comm] using (hs u).2

#print axioms costAtMost_prefix_reserved
end
end WeightedReplacement
