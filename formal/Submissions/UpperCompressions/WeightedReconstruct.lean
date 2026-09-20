import Submissions.UpperCompressions.WideScheme
import Submissions.UpperCompressions.Reconstruct

/-! Every accepted weighted verifier run has its index answer and reconstruction
witness recorded in the final shared-oracle cache. -/

open OracleSpec OracleComp ENNReal
noncomputable section
open scoped Classical

namespace OptimalOTS.WeightedScheme

variable {M : ℕ}

theorem verify_support (S : Scheme M) (pk : PublicKey) (m : Message)
    (σ : Signature) (c : Cache) :
    ∀ p ∈ support (run (S.verify pk m σ) c),
      Cache.Sub c p.2 ∧ (p.1 = true →
        ∃ w, p.2 ⟨msgBits + 86, m ++ σ.1⟩ = some w ∧
          ∃ i : Fin M, S.decode w = some i ∧
            σ.2.length = S.graph.revealBits (S.sets i) ∧
            ∃ y : S.graph.Assignment,
              S.graph.ReconEqs p.2 (S.sets i) (S.graph.decode (S.sets i) σ.2) y ∧
              S.publicKey y = pk) := by
  intro p hp
  unfold Scheme.verify at hp
  rw [run_bind, support_bind] at hp
  simp only [Set.mem_iUnion] at hp
  obtain ⟨⟨w, c₁⟩, hw₁, hp⟩ := hp
  obtain ⟨hsub₁, hw⟩ := Dag.Graph.hash_support (m ++ σ.1) c (w, c₁) hw₁
  cases hi : S.decode w with
  | none =>
    simp only [hi, run_pure, support_pure, Set.mem_singleton_iff] at hp
    subst hp
    exact ⟨hsub₁, fun h => by cases h⟩
  | some i =>
    simp only [hi] at hp
    by_cases hlen : σ.2.length = S.graph.revealBits (S.sets i)
    · rw [if_pos hlen, run_bind, support_bind] at hp
      simp only [Set.mem_iUnion] at hp
      obtain ⟨⟨y, c₂⟩, hy, hp⟩ := hp
      obtain ⟨hsub₂, heq⟩ := S.graph.reconstruct_support _ _ c₁ (y, c₂) hy
      rw [run_pure, support_pure, Set.mem_singleton_iff] at hp
      subst hp
      refine ⟨hsub₁.trans hsub₂, fun hok => ?_⟩
      exact ⟨w, hsub₂ _ _ hw, i, hi, hlen, y, heq, of_decide_eq_true hok⟩
    · rw [if_neg hlen, run_pure, support_pure, Set.mem_singleton_iff] at hp
      subst hp
      exact ⟨hsub₁, fun h => by cases h⟩

end OptimalOTS.WeightedScheme

#print axioms OptimalOTS.WeightedScheme.verify_support
