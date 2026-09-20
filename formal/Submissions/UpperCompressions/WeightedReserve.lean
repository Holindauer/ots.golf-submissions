import Submissions.UpperCompressions.WeightedSampling
import Submissions.UpperCompressions.Keygen

/-! The all-trial signer reserves its entire paid query budget on every
raw answer path. These are resource statements, not probabilistic claims. -/

open OracleSpec OracleComp
noncomputable section
open scoped Classical

namespace OptimalOTS.WeightedSampling

variable {M : ℕ}

theorem loop_step_budget {β : Type} (n : ℕ)
    (decode : BitVec hashBits → Option (Fin M)) (tier : Fin M → ℕ)
    (m : Message) (k : ℕ) (kont : Option (Winner n M) → OracleComp Spec β)
    (hc : blockCost (msgBits+n) = 1) {b : ℕ}
    (hB : CostAtMost (loop n decode tier m (k+1) >>= kont) b) :
    1 ≤ b ∧ ∀ η w, CostAtMost
      (loop n decode tier m k >>= fun r =>
        kont (best (fun s => tier s.2) (candidate decode η w) r)) (b-1) := by
  rw [loop,bind_assoc,sampleBits] at hB
  have hη := costAtMost_liftM_bind _ _ hB
  have hη' (η : Nonce n) := hη η (by simp)
  have hw (η : Nonce n) : 1 ≤ b ∧ ∀ w, CostAtMost
      (loop n decode tier m k >>= fun r =>
        kont (best (fun s => tier s.2) (candidate decode η w) r)) (b-1) := by
    have hx := hη' η
    rw [bind_assoc,hash,costAtMost_query_bind_iff] at hx
    change blockCost (msgBits+n) ≤ b ∧ ∀ w : BitVec hashBits,
      CostAtMost ((loop n decode tier m k >>= fun r =>
        pure (best (fun s => tier s.2) (candidate decode η w) r)) >>= kont)
        (b-blockCost (msgBits+n)) at hx
    simpa only [hc,bind_assoc,pure_bind] using hx
  exact ⟨(hw 0).1,fun η => (hw η).2⟩

/-- All L hashes are paid before any outcome-dependent continuation.
The guarantee holds for every syntactically possible output, so it also
covers outcomes of a single consistent random oracle. -/
theorem loop_reserve {β : Type} (n : ℕ)
    (decode : BitVec hashBits → Option (Fin M)) (tier : Fin M → ℕ)
    (m : Message) (hc : blockCost (msgBits+n) = 1) :
    ∀ k (kont : Option (Winner n M) → OracleComp Spec β) b,
      CostAtMost (loop n decode tier m k >>= kont) b →
      k ≤ b ∧ ∀ r ∈ support (loop n decode tier m k),
        CostAtMost (kont r) (b-k) := by
  intro k
  induction k with
  | zero =>
    intro kont b hB
    rw [loop,pure_bind] at hB
    refine ⟨Nat.zero_le _, ?_⟩
    intro r hr
    simp only [loop,support_pure,Set.mem_singleton_iff] at hr
    subst r
    simpa using hB
  | succ k ih =>
    intro kont b hB
    obtain ⟨hb,hs⟩ := loop_step_budget n decode tier m k kont hc hB
    have hi (η : Nonce n) (w : BitVec hashBits) := ih
      (fun r => kont (best (fun s => tier s.2) (candidate decode η w) r))
      (b-1) (hs η w)
    have hk := (hi 0 0).1
    refine ⟨by omega, ?_⟩
    intro r hr
    rw [loop,support_bind] at hr
    simp only [Set.mem_iUnion] at hr
    obtain ⟨η,_,hr⟩ := hr
    rw [support_bind] at hr
    simp only [Set.mem_iUnion] at hr
    obtain ⟨w,_,hr⟩ := hr
    rw [support_bind] at hr
    simp only [Set.mem_iUnion] at hr
    obtain ⟨s,hs,hr⟩ := hr
    rw [support_pure,Set.mem_singleton_iff] at hr
    subst r
    have hkont := (hi η w).2 s hs
    simpa only [Nat.sub_sub,show 1+k=k+1 by omega] using hkont

#print axioms loop_step_budget
#print axioms loop_reserve

end OptimalOTS.WeightedSampling
