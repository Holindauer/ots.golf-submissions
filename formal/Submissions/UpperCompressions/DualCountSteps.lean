import Submissions.UpperCompressions.DualProtectedLaw

/-! Exact deterministic count increments for every supported primitive answer. -/
noncomputable section
open OracleSpec OracleComp
open scoped Classical
namespace WeightedDualCache
open WeightedCacheCounts WeightedDirectCache
variable {D B : Type} [DecidableEq D] [SampleableType B]

def globalStep : Phase → ℕ | .idle => 0 | _ => 1
def rowStep : Phase → ℕ | .inside => 1 | _ => 0

theorem phase_steps (A G : Finset D) (hAG : A ⊆ G) (q : D)
    (c : (D →ₒ B).QueryCache) :
    globalStep (phase A G q c) = (if fresh G q c then 1 else 0) ∧
      rowStep (phase A G q c) = (if fresh A q c then 1 else 0) := by
  cases hc : c q with
  | some u => simp [phase,fresh,hc,globalStep,rowStep]
  | none =>
    by_cases hA : q∈A
    · simp [phase,fresh,hc,hA,hAG hA,globalStep,rowStep]
    · by_cases hG : q∈G <;> simp [phase,fresh,hc,hA,hG,globalStep,rowStep]

theorem protected_phase_steps (A G : Finset D) (hAG : A ⊆ G)
    (t : (unifSpec+(D →ₒ B)).Domain) (c : (D →ₒ B).QueryCache) :
    globalStep (protectedPhase A G t c) = (if protectedFresh G t c then 1 else 0) ∧
      rowStep (protectedPhase A G t c) = (if protectedFresh A t c then 1 else 0) := by
  cases t with
  | inl t => simp [protectedPhase,protectedFresh,globalStep,rowStep]
  | inr q => exact phase_steps A G hAG q c

theorem hash_seen_count (A : Finset D) (q : D) (c : (D →ₒ B).QueryCache)
    (out : B × (D →ₒ B).QueryCache)
    (hout : out ∈ support (((D →ₒ B).randomOracle q).run c)) :
    (seen A out.2).card = (seen A c).card+(if fresh A q c then 1 else 0) := by
  rw [randomOracle.run_eq] at hout
  cases hc : c q with
  | some u =>
    simp only [hc,support_pure,Set.mem_singleton_iff] at hout
    subst out
    simp [fresh,hc]
  | none =>
    simp only [hc,mem_support_bind_iff,support_pure,Set.mem_singleton_iff] at hout
    obtain ⟨u,hu,rfl⟩ := hout
    by_cases hq : q∈A
    · have hcount : (seen A (c.cacheQuery q u)).card=(seen A c).card+1 :=
        seen_card_update A c q u hq hc
      simpa only [fresh,hq,decide_true,hc,Option.isNone_none,Bool.and_self,ite_true] using hcount
    · rw [show seen A (c.cacheQuery q u)=seen A c from seen_update_of_not_mem A c q u hq]
      simp [fresh,hq]

theorem protected_seen_count (A : Finset D) (t : (unifSpec+(D →ₒ B)).Domain)
    (c : (D →ₒ B).QueryCache) (out : (unifSpec+(D →ₒ B)).Range t × (D →ₒ B).QueryCache)
    (hout : out ∈ support ((protectedImpl (D := D) (B := B) t).run c)) :
    (seen A out.2).card = (seen A c).card+(if protectedFresh A t c then 1 else 0) := by
  cases t with
  | inl t =>
    change out ∈ support ((liftM (unifSpec.query t) : ProbComp (unifSpec.Range t)) >>=
      fun u => pure (u,c)) at hout
    obtain ⟨u,hu,hp⟩ := (mem_support_bind_iff _ _ _).1 hout
    simp only [support_pure,Set.mem_singleton_iff] at hp
    subst out
    simp [protectedFresh]
  | inr q => exact hash_seen_count A q c out hout

theorem actual_seen_count (A : Finset OptimalOTS.Query) (t : OptimalOTS.Spec.Domain)
    (c : OptimalOTS.hashSpec.QueryCache)
    (out : OptimalOTS.Spec.Range t × OptimalOTS.hashSpec.QueryCache)
    (hout : out ∈ support ((OptimalOTS.oracleImpl t).run c)) :
    (seen A out.2).card = (seen A c).card+(if protectedFresh A t c then 1 else 0) := by
  have h := protected_seen_count A t c out
  rw [WeightedProtectedCache.protectedImpl_eq] at h
  exact h hout

#print axioms actual_seen_count
end WeightedDualCache
