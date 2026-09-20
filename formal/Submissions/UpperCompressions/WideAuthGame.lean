import Submissions.UpperCompressions.WideStrongEvents
import Submissions.UpperCompressions.WideAuthSigning
import Submissions.UpperCompressions.WideAuthAssembly

/-! Actual typed strong-forgery continuation and hidden-graph cache coupling.
The remaining alternate-class event includes accepted private signing trials. -/
open OracleSpec OracleComp OracleComp.EvalDist ENNReal
noncomputable section
open scoped Classical
set_option maxRecDepth 10000
attribute [local irreducible] Finset.univ Finset.filter OptimalOTS.WeightedResearch92.classes
namespace OptimalOTS.WeightedConstruction.WideForest
open OptimalOTS.Dag Name

variable (A : forestScheme.toAlgorithm.Adversary)

def stB (pk : PublicKey) (m₁ : Message) (st : A.State)
    (σ : Option WeightedScheme.Signature) : OracleComp Spec Bool := do
  let (m₂, σ₂) ← A.forge st σ
  let ok ← forestScheme.verify pk m₂ σ₂
  return ok && decide (σ.map (fun s => (m₁, s)) ≠ some (m₂, σ₂))

def successValue (p : Bool × Cache) : ℝ≥0∞ := if p.1 = true then 1 else 0

theorem successValue_le_one (p : Bool × Cache) : successValue p ≤ 1 := by
  unfold successValue
  split_ifs <;> simp

theorem stB_success (pk : PublicKey) (m₁ : Message) (st : A.State)
    (σ : Option WeightedScheme.Signature) (c : Cache) (p : Bool × Cache)
    (hp : p ∈ support (run (stB A pk m₁ st σ) c)) (hok : p.1 = true) :
    ∃ m₂ σ₂ c₁, σ.map (fun s => (m₁, s)) ≠ some (m₂, σ₂) ∧
      (true, p.2) ∈ support (run (forestScheme.verify pk m₂ σ₂) c₁) := by
  unfold stB at hp
  rw [run_bind, support_bind] at hp
  simp only [Set.mem_iUnion] at hp
  obtain ⟨⟨⟨m₂, σ₂⟩, c₁⟩, h₁, hp⟩ := hp
  dsimp only at hp
  rw [run_bind, support_bind] at hp
  simp only [Set.mem_iUnion] at hp
  obtain ⟨⟨ok, c₂⟩, h₂, hp⟩ := hp
  rw [run_pure, support_pure, Set.mem_singleton_iff] at hp
  subst p
  simp only [Bool.and_eq_true, decide_eq_true_iff] at hok
  obtain ⟨hok, hne⟩ := hok
  subst ok
  exact ⟨m₂, σ₂, c₁, hne, h₂⟩

theorem stB_events_some (ξ : Rec) (i : Fin WeightedSchedule.M) (η : BitVec 86)
    (m₁ : Message) (st : A.State) (c : Cache) (p : Bool × Cache)
    (hp : p ∈ support (run (stB A (pkOf ξ) m₁ st
      (some (η, revealed (setsName i) ξ))) c)) (hok : p.1 = true) :
    Spr p.2 ξ ∨ Cache.Hits p.2 (fHid (some (setsName i)) ξ) ∨ AlternateClass p.2 (m₁, η) i := by
  obtain ⟨m₂, σ₂, c₁, hne, hv⟩ := stB_success A (pkOf ξ) m₁ st _ c p hp hok
  apply accepted_strong_event ξ i (m₁, η) m₂ σ₂ c₁ p.2 hv
  intro he
  apply hne
  exact congrArg some he.symm

theorem stB_events_none (ξ : Rec) (m₁ : Message) (st : A.State) (c : Cache) (p : Bool × Cache)
    (hp : p ∈ support (run (stB A (pkOf ξ) m₁ st none) c)) (hok : p.1 = true) :
    Spr p.2 ξ ∨ Cache.Hits p.2 (kc ξ) := by
  obtain ⟨m₂, σ₂, c₁, _, hv⟩ := stB_success A (pkOf ξ) m₁ st none c p hp hok
  exact accepted_none_event ξ m₂ σ₂ c₁ p.2 hv

theorem ind_of {p : Prop} (h : p) : ind p = 1 := by rw [ind, if_pos h]
theorem ind_not {p : Prop} (h : ¬ p) : ind p = 0 := by rw [ind, if_neg h]

/-- Remove the hidden graph cache under the actual oracle law, charging its
first query through the checked identical-until-bad theorem. -/
theorem graph_iub (oa : OracleComp Spec Bool) (ξ : Rec) (A? : Option (Finset Name))
    (d d' : Cache) (hd' : IndexExtension d d') (hξ : ¬ Cache.Hits d (kc ξ)) :
    E (run oa (Cache.extend d' (kc ξ))) successValue ≤
      E (run oa (Cache.extend d' (fExp A? ξ)))
        (fun p => if Cache.Hits p.2 (fHid A? ξ) then 1 else successValue p) := by
  have hkc : Cache.extend d' (kc ξ) =
      Cache.extend (Cache.extend d' (fExp A? ξ)) (fHid A? ξ) := by
    rw [Cache.extend_assoc, extend_fExp_fHid]
  have hdisj : Cache.Disjoint (Cache.extend d' (fExp A? ξ)) (fHid A? ξ) := by
    intro q hq
    have hkq : (kc ξ q).isSome := by
      obtain ⟨h, p, hp, _, hqp⟩ := (fHid_isSome_iff _ ξ q).1 hq
      exact (kc_isSome_iff ξ q).2 ⟨h, p, hp, hqp⟩
    rw [Cache.extend_apply, indexExtension_kc_none hd' hξ hkq, Option.none_or]
    exact disjoint_fExp_fHid _ ξ q hq
  rw [hkc]
  exact iub oa (fHid A? ξ) successValue successValue_le_one _ hdisj

/-- Actual forge/verify/strong-check success is bounded by authentication bad
indicators plus the alternate-class event, after hidden graph points are removed. -/
theorem stB_iub_some (ξ : Rec) (i : Fin WeightedSchedule.M) (η : BitVec 86)
    (m₁ : Message) (st : A.State) (d d' : Cache)
    (hd' : IndexExtension d d') (hξ : ¬ Cache.Hits d (kc ξ)) :
    E (run (stB A (pkOf ξ) m₁ st (some (η, revealed (setsName i) ξ)))
      (Cache.extend d' (kc ξ))) successValue ≤
      E (run (stB A (pkOf ξ) m₁ st (some (η, revealed (setsName i) ξ)))
        (Cache.extend d' (fExp (some (setsName i)) ξ)))
        (fun p => ind (Cache.Hits p.2 (fHid (some (setsName i)) ξ)) + ind (Spr p.2 ξ) +
          ind (AlternateClass p.2 (m₁, η) i)) := by
  refine (graph_iub _ ξ (some (setsName i)) d d' hd' hξ).trans ?_
  apply expectedValue_mono_of_support
  intro p hp
  by_cases hh : Cache.Hits p.2 (fHid (some (setsName i)) ξ)
  · rw [if_pos hh, ind_of hh]
    exact le_add_right le_self_add
  · rw [if_neg hh]
    by_cases hok : p.1 = true
    · rw [successValue, if_pos hok]
      rcases stB_events_some A ξ i η m₁ st _ p hp hok with hs | hh' | hi
      · rw [ind_of hs]
        exact le_add_right le_add_self
      · exact absurd hh' hh
      · rw [ind_of hi]
        exact le_add_self
    · rw [successValue, if_neg hok]
      exact zero_le

end OptimalOTS.WeightedConstruction.WideForest
#print axioms OptimalOTS.WeightedConstruction.WideForest.stB_events_some
#print axioms OptimalOTS.WeightedConstruction.WideForest.stB_iub_some
