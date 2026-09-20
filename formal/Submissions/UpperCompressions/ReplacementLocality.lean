import Submissions.UpperCompressions.WeightedSampling
import Submissions.UpperCompressions.WeightedScheme

/-! Cache locality of the actual all-trial signer. Accepted nonwinners remain
allowed in the implementation cache; every insertion is in the signed row. -/

open OracleSpec OracleComp OracleComp.EvalDist ENNReal
noncomputable section
open scoped Classical

namespace OptimalOTS.ReplacementLocality

open WeightedSampling

theorem hash_cache_other {n : ℕ} (x : BitVec n) (c : Cache)
    (p : BitVec hashBits × Cache) (hp : p ∈ support (run (hash x) c))
    (q : Query) (hq : q ≠ ⟨n, x⟩) : p.2 q = c q := by
  unfold OptimalOTS.hash run at hp
  rw [simulateQ_spec_query] at hp
  rcases hc : c ⟨n, x⟩ with _ | w
  · rw [oracleImpl_run_inr_none hc, support_bind] at hp
    simp only [Set.mem_iUnion] at hp
    obtain ⟨w, _, hp⟩ := hp
    rw [support_pure, Set.mem_singleton_iff] at hp
    subst hp
    exact QueryCache.cacheQuery_of_ne _ _ hq
  · rw [oracleImpl_run_inr_some hc, support_pure, Set.mem_singleton_iff] at hp
    subst hp
    rfl

theorem loop_cache_outside_row {M : ℕ} (n : ℕ)
    (decode : BitVec hashBits → Option (Fin M)) (tier : Fin M → ℕ) (m : Message) :
    ∀ k c p, p ∈ support (run (loop n decode tier m k) c) →
      ∀ q : Query, (∀ η : Nonce n, q ≠ ⟨msgBits + n, m ++ η⟩) → p.2 q = c q := by
  intro k
  induction k with
  | zero =>
    intro c p hp q hq
    rw [loop, run_pure, support_pure, Set.mem_singleton_iff] at hp
    subst p
    rfl
  | succ k ih =>
    intro c p hp q hq
    rw [run_loop_succ, support_bind] at hp
    simp only [Set.mem_iUnion] at hp
    obtain ⟨η, _, hp⟩ := hp
    rw [support_bind] at hp
    simp only [Set.mem_iUnion] at hp
    obtain ⟨⟨w,d⟩, hd, hp⟩ := hp
    rw [support_bind] at hp
    simp only [Set.mem_iUnion] at hp
    obtain ⟨⟨r,e⟩, hr, hp⟩ := hp
    rw [support_pure, Set.mem_singleton_iff] at hp
    subst p
    exact (ih d (r,e) hr q hq).trans (hash_cache_other _ c (w,d) hd q (hq η))

theorem loop_new_cache_row {M : ℕ} (n : ℕ)
    (decode : BitVec hashBits → Option (Fin M)) (tier : Fin M → ℕ) (m : Message)
    (k : ℕ) (c : Cache) (p : Option (Winner n M) × Cache)
    (hp : p ∈ support (run (loop n decode tier m k) c))
    (q : Query) (w : BitVec hashBits) (hc : c q = none) (he : p.2 q = some w) :
    ∃ η : Nonce n, q = ⟨msgBits + n, m ++ η⟩ := by
  by_contra h
  have hq : ∀ η : Nonce n, q ≠ ⟨msgBits + n, m ++ η⟩ := by simpa using h
  have ho := loop_cache_outside_row n decode tier m k c p hp q hq
  rw [he, hc] at ho
  cases ho

theorem sign_cache_outside_row {M : ℕ} (S : WeightedScheme.Scheme M)
    (x : S.graph.Assignment) (m : Message) (c : Cache)
    (p : Option WeightedScheme.Signature × Cache) (hp : p ∈ support (run (S.sign x m) c))
    (q : Query) (hq : ∀ η : Nonce 86, q ≠ ⟨msgBits + 86, m ++ η⟩) :
    p.2 q = c q := by
  rw [WeightedScheme.Scheme.sign, run_map, support_map, Set.mem_image] at hp
  obtain ⟨p', hp', rfl⟩ := hp
  exact loop_cache_outside_row 86 S.decode S.tier m signBudget c p' hp' q hq

theorem sign_new_cache_row {M : ℕ} (S : WeightedScheme.Scheme M)
    (x : S.graph.Assignment) (m : Message) (c : Cache)
    (p : Option WeightedScheme.Signature × Cache) (hp : p ∈ support (run (S.sign x m) c))
    (q : Query) (w : BitVec hashBits) (hc : c q = none) (he : p.2 q = some w) :
    ∃ η : Nonce 86, q = ⟨msgBits + 86, m ++ η⟩ := by
  by_contra h
  have hq : ∀ η : Nonce 86, q ≠ ⟨msgBits + 86, m ++ η⟩ := by simpa using h
  have ho := sign_cache_outside_row S x m c p hp q hq
  rw [he, hc] at ho
  cases ho

end OptimalOTS.ReplacementLocality

#print axioms OptimalOTS.ReplacementLocality.loop_new_cache_row
#print axioms OptimalOTS.ReplacementLocality.sign_new_cache_row
