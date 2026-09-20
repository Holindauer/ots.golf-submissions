import Submissions.UpperCompressions.DualCacheLaw

/-! Supported actual oracle outputs obey the same joint transition as its law. -/
noncomputable section
open OracleSpec OracleComp
open scoped Classical
namespace WeightedDualCache
open WeightedRealExecution WeightedRow.Weights WeightedCacheCounts
variable {D B ι : Type} [DecidableEq D] [Fintype B] [SampleableType B]
  [Fintype ι] [DecidableEq ι]

theorem hash_payoff_support (A G : Finset D) (hAG : A ⊆ G) (decode : B → Option ι)
    (q : D) (cache : (D →ₒ B).QueryCache)
    (f : ℕ → (ι → ℕ) → (ι → ℕ) → ℝ)
    (out : B × (D →ₒ B).QueryCache)
    (hout : out ∈ support (((D →ₒ B).randomOracle q).run cache)) :
    ∃ x : Option ι, f (seen A out.2).card (classCounts G out.2 decode)
        (classCounts A out.2 decode) =
      after f (phase A G q cache) (seen A cache).card
        (classCounts G cache decode) (classCounts A cache decode) x := by
  rw [randomOracle.run_eq] at hout
  cases hc : cache q with
  | some u =>
    simp only [hc, support_pure, Set.mem_singleton_iff] at hout
    subst out
    exact ⟨none,by simp [phase,hc,after]⟩
  | none =>
    simp only [hc,mem_support_bind_iff,support_pure,Set.mem_singleton_iff] at hout
    obtain ⟨u,hu,rfl⟩ := hout
    refine ⟨decode u,?_⟩
    by_cases hqA : q ∈ A
    · have hqG := hAG hqA
      rw [show (seen A (cache.cacheQuery q u)).card=(seen A cache).card+1 from
        seen_card_update A cache q u hqA hc]
      rw [show classCounts G (cache.cacheQuery q u) decode=
        advance (classCounts G cache decode) (decode u) from
        classCounts_update_of_mem G cache decode q u hqG hc]
      rw [show classCounts A (cache.cacheQuery q u) decode=
        advance (classCounts A cache decode) (decode u) from
        classCounts_update_of_mem A cache decode q u hqA hc]
      simp [phase,hc,hqA,after]
    · rw [show seen A (cache.cacheQuery q u)=seen A cache from
        seen_update_of_not_mem A cache q u hqA]
      rw [show classCounts A (cache.cacheQuery q u) decode=classCounts A cache decode from
        classCounts_update_of_not_mem A cache decode q u hqA]
      by_cases hqG : q ∈ G
      · rw [show classCounts G (cache.cacheQuery q u) decode=
          advance (classCounts G cache decode) (decode u) from
          classCounts_update_of_mem G cache decode q u hqG hc]
        simp [phase,hc,hqA,hqG,after]
      · rw [show classCounts G (cache.cacheQuery q u) decode=classCounts G cache decode from
          classCounts_update_of_not_mem G cache decode q u hqG]
        simp [phase,hc,hqA,hqG,after]

theorem protected_payoff_support (A G : Finset D) (hAG : A ⊆ G) (decode : B → Option ι)
    (t : (unifSpec+(D →ₒ B)).Domain) (cache : (D →ₒ B).QueryCache)
    (f : ℕ → (ι → ℕ) → (ι → ℕ) → ℝ)
    (out : (unifSpec+(D →ₒ B)).Range t × (D →ₒ B).QueryCache)
    (hout : out ∈ support ((WeightedDirectCache.protectedImpl (D := D) (B := B) t).run cache)) :
    ∃ x : Option ι, f (seen A out.2).card (classCounts G out.2 decode)
        (classCounts A out.2 decode) =
      after f (protectedPhase A G t cache) (seen A cache).card
        (classCounts G cache decode) (classCounts A cache decode) x := by
  cases t with
  | inl t =>
    change out ∈ support ((liftM (unifSpec.query t) : ProbComp (unifSpec.Range t)) >>=
      fun u => pure (u,cache)) at hout
    obtain ⟨u,hu,hp⟩ := (mem_support_bind_iff _ _ _).1 hout
    simp only [support_pure,Set.mem_singleton_iff] at hp
    subst out
    exact ⟨none,rfl⟩
  | inr q => exact hash_payoff_support A G hAG decode q cache f out hout

#print axioms protected_payoff_support
end WeightedDualCache
