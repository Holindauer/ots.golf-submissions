import Submissions.UpperCompressions.WeightedReserve
import Submissions.UpperCompressions.ReplacementRemainingClock

/-! The all-L syntactic reserve applies to every supported outcome of the
actual shared-cache signer, without a full-support assumption on that cache. -/
open OracleSpec OracleComp OracleComp.EvalDist ENNReal
open OptimalOTS OptimalOTS.WeightedSampling
namespace WeightedReplacement
noncomputable section
open scoped Classical

theorem run_output_mem_support {α : Type} (oa : OracleComp Spec α) :
    ∀ c p, p ∈ support (run oa c) → p.1 ∈ support oa := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro c p hp
    rw [run_pure,support_pure,Set.mem_singleton_iff] at hp
    subst p
    simp
  | query_bind t k ih =>
    intro c p hp
    rw [run_query_bind,support_bind] at hp
    simp only [Set.mem_iUnion] at hp
    obtain ⟨r,_,hp⟩ := hp
    rw [support_bind]
    simp only [Set.mem_iUnion]
    exact ⟨r.1,by simp,ih r.1 r.2 p hp⟩

theorem actual_loop_reserve {M : ℕ} {β : Type} (n : ℕ)
    (decode : BitVec hashBits → Option (Fin M)) (tier : Fin M → ℕ)
    (m : Message) (hc : blockCost (msgBits+n) = 1)
    (k : ℕ) (kont : Option (Winner n M) → OracleComp Spec β) (b : ℕ)
    (hB : CostAtMost (loop n decode tier m k >>= kont) b) :
    k ≤ b ∧ ∀ c p, p ∈ support (run (loop n decode tier m k) c) →
      CostAtMost (kont p.1) (b-k) := by
  obtain ⟨hk,hr⟩ := loop_reserve n decode tier m hc k kont b hB
  exact ⟨hk,fun c p hp => hr p.1 (run_output_mem_support _ c p hp)⟩

#print axioms run_output_mem_support
#print axioms actual_loop_reserve
end
end WeightedReplacement
