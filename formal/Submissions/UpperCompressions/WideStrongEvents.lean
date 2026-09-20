import Submissions.UpperCompressions.WideVerifyEvents

/-! Endgame event decomposition for strong forgery. The alternate-input event
includes private signing cache insertions; it has no probability bound here. -/

open OracleSpec OracleComp ENNReal
noncomputable section
open scoped Classical
set_option maxRecDepth 10000
attribute [local irreducible] OptimalOTS.WeightedResearch92.classes

namespace OptimalOTS.WeightedConstruction.WideForest
open OptimalOTS.Dag Name

/-- A different message/nonce input with the signed class, wherever the answer
was inserted. In particular, private nonwinning signing trials are retained. -/
def AlternateClass (c : Cache) (signedInput : EncInput) (i : Fin WeightedSchedule.M) : Prop :=
  ∃ u : EncInput, u ≠ signedInput ∧
    ∃ w, c (encQuery u) = some w ∧ WeightedSchedule.decode w = some i

/-- Acceptance of a pair different from the signed pair reaches either graph
authentication badness or an alternate encoding input with the signed class. -/
theorem accepted_strong_event (ξ : Rec) (signedClass : Fin WeightedSchedule.M)
    (signedInput : EncInput) (m : Message) (σ : WeightedScheme.Signature) (c d : Cache)
    (h : (true, d) ∈ support (run (forestScheme.verify (pkOf ξ) m σ) c))
    (hne : (m, σ) ≠ (signedInput.1,
      (signedInput.2, graph.encode (fins (setsName signedClass)) (graph.evalRec ξ)))) :
    Spr d ξ ∨ Cache.Hits d (fHid (some (setsName signedClass)) ξ) ∨
      AlternateClass d signedInput signedClass := by
  obtain ⟨w, hw, i, hi, he | hs | hh⟩ :=
    accepted_class_cases ξ signedClass m σ c d h
  · obtain ⟨rfl, hpayload⟩ := he
    right; right
    refine ⟨(m, σ.1), ?_, w, hw, hi⟩
    intro heq
    apply hne
    have hm : m = signedInput.1 := congrArg (fun u : EncInput => u.1) heq
    have hn : σ.1 = signedInput.2 := congrArg (fun u : EncInput => u.2) heq
    exact Prod.ext hm (Prod.ext hn hpayload)
  · exact Or.inl hs
  · exact Or.inr (Or.inl hh)

end OptimalOTS.WeightedConstruction.WideForest

#print axioms OptimalOTS.WeightedConstruction.WideForest.accepted_strong_event
