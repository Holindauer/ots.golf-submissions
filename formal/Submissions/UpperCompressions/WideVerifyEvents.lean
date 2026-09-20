import Submissions.UpperCompressions.WideEvents
import Submissions.UpperCompressions.WeightedReconstruct

/-! Concrete accepted-signature routes for the86-bit weighted verifier.
The remaining same-class, same-payload case belongs to the weighted index event,
including different nonce/message pairs. -/

open OracleSpec OracleComp ENNReal
noncomputable section
open scoped Classical

namespace OptimalOTS.WeightedConstruction.WideForest
open OptimalOTS.Dag Name

/-- The actual verifier's public-key check is low128 at the full256-bit root. -/
theorem accepted_lowPk (ξ : Rec) (y : graph.Assignment)
    (h : forestScheme.publicKey y = pkOf ξ) : lowPk (yv y rh) = pkOf ξ := by
  unfold yv
  rw [lowPk_cast_eq]
  exact h

/-- If signing returned no signature, every accepting verification reaches an
authentication bad event; the index decoder and nonce are the actual new scheme's. -/
theorem accepted_none_event (ξ : Rec) (m : Message) (σ : WeightedScheme.Signature)
    (c d : Cache) (h : (true, d) ∈ support (run (forestScheme.verify (pkOf ξ) m σ) c)) :
    Spr d ξ ∨ Cache.Hits d (kc ξ) := by
  obtain ⟨_, hh⟩ := WeightedScheme.verify_support forestScheme (pkOf ξ) m σ c (true, d) h
  obtain ⟨w, hw, i, hi, hlen, y, hy, hpk⟩ := hh rfl
  exact events_none (isCut_setsName i) hy (accepted_lowPk ξ y hpk)

/-- Given a signed class, an accepted signature either reproduces that class's
honest payload or reaches a hidden-input/spurious-image event. Payload equality
is full129-bit equality, and thus covers same-message altered-payload forgery. -/
theorem accepted_class_cases (ξ : Rec) (signedClass : Fin WeightedSchedule.M)
    (m : Message) (σ : WeightedScheme.Signature) (c d : Cache)
    (h : (true, d) ∈ support (run (forestScheme.verify (pkOf ξ) m σ) c)) :
    ∃ w, d (encQuery (m, σ.1)) = some w ∧
      ∃ i : Fin WeightedSchedule.M, WeightedSchedule.decode w = some i ∧
        ((i = signedClass ∧ σ.2 = graph.encode (fins (setsName signedClass)) (graph.evalRec ξ)) ∨
          Spr d ξ ∨ Cache.Hits d (fHid (some (setsName signedClass)) ξ)) := by
  obtain ⟨_, hh⟩ := WeightedScheme.verify_support forestScheme (pkOf ξ) m σ c (true, d) h
  obtain ⟨w, hw, i, hi, hlen, y, hy, hpk⟩ := hh rfl
  refine ⟨w, hw, i, hi, ?_⟩
  have hacc := accepted_lowPk ξ y hpk
  by_cases hic : i = signedClass
  · subst i
    by_cases hpayload : σ.2 = graph.encode (fins (setsName signedClass)) (graph.evalRec ξ)
    · exact Or.inl ⟨rfl, hpayload⟩
    · exact Or.inr (Or.inl (events_same (isCut_setsName signedClass) hy hacc hlen hpayload))
  · apply Or.inr
    apply events_ne (isCut_setsName signedClass) (isCut_setsName i)
      (by rw [cost_setsName, cost_setsName])
    · exact fun he => hic (setsName_injective he).symm
    · exact hy
    · exact hacc

end OptimalOTS.WeightedConstruction.WideForest

#print axioms OptimalOTS.WeightedConstruction.WideForest.accepted_none_event
#print axioms OptimalOTS.WeightedConstruction.WideForest.accepted_class_cases
