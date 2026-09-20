import Submissions.UpperCompressions.WideCachedPayoff
import Submissions.UpperCompressions.WideStrongEvents
import Submissions.UpperCompressions.ReplacementFreshIndex
import Submissions.UpperCompressions.WeightedCacheEvidence

/-! A cached alternate forged input is bounded by the actual selector's replay
payoff. Distinct inputs, rather than cache membership alone, enforce k_i≥2 when
the selected nonce was itself already public. -/
noncomputable section
namespace OptimalOTS.WeightedConstruction.WideCachedRow
open OracleSpec OracleComp OracleComp.EvalDist
open WeightedSchedule WideDomains WideForest WeightedReference WeightedConstants
open WeightedReplacement WeightedCompletion WeightedCacheCounts
open scoped Classical ENNReal
attribute [local irreducible] Finset.univ Finset.filter WeightedResearch92.classes
set_option maxRecDepth 10000

theorem classCount_one (c : Cache) (i : Fin M) (q : Query) (hq : q.1=342)
    (y : BitVec 256) (hc : c q=some y) (hi : decode y=some i) :
    1≤classCounts indexDomain c decode i :=
  WeightedCacheEvidence.one indexDomain c decode i q ((mem_indexDomain q).mpr hq) y hc hi

theorem classCount_two (c : Cache) (i : Fin M) (q q' : Query)
    (hne : q≠q') (hq : q.1=342) (hq' : q'.1=342)
    (y y' : BitVec 256) (hc : c q=some y) (hc' : c q'=some y')
    (hi : decode y=some i) (hi' : decode y'=some i) :
    2≤classCounts indexDomain c decode i :=
  WeightedCacheEvidence.two indexDomain c decode i q q' hne
    ((mem_indexDomain q).mpr hq) ((mem_indexDomain q').mpr hq') y y' hc hc' hi hi'

theorem alternative_replayScore (m : Message) (c : Cache) (η : BitVec 86) (i : Fin M)
    (hconsistent : ∀ y,c (WideForest.encQuery (m,η))=some y → decode y=some i)
    (h : AlternateClass c (m,η) i) : replayScore m c η i=1 := by
  obtain ⟨u,hne,y,hy,hi⟩ := h
  unfold replayScore
  by_cases hη : η∈exposed m c
  · rw [if_pos hη]
    have hs := (Finset.mem_filter.mp hη).2
    cases hc : c (WideForest.encQuery (m,η)) with
    | none => simp [hc] at hs
    | some z =>
      have he : WideForest.encQuery u≠WideForest.encQuery (m,η) := by
        intro he
        exact hne (indexInput_injective 86 he)
      have hk := classCount_two c i (WideForest.encQuery u) (WideForest.encQuery (m,η)) he rfl rfl
        y z hy hc hi (hconsistent z hc)
      exact if_pos hk
  · rw [if_neg hη]
    have hk := classCount_one c i (WideForest.encQuery u) rfl y hy hi
    exact if_neg (by omega)

private def optionEvent {I : Type} (P : I → Prop) : Option I → ℝ≥0∞
  | none => 0
  | some i => if P i then 1 else 0

private theorem optionEvent_le_score {I : Type} (P : I → Prop) (f : I → ℝ)
    (s : Option I) (h : ∀ i, s=some i → P i → f i=1) :
    optionEvent P s ≤ ENNReal.ofReal (WeightedCompletion.score s f) := by
  cases s with
  | none => exact bot_le
  | some i =>
    change (if P i then (1:ℝ≥0∞) else 0) ≤ ENNReal.ofReal (f i)
    by_cases hi : P i
    · rw [if_pos hi,h i rfl hi,ENNReal.ofReal_one]
    · rw [if_neg hi]
      exact bot_le

def alternatePayoff (m : Message) (c : Cache) : Option (WeightedSampling.Winner 86 M) → ℝ≥0∞ :=
  optionEvent (fun r => AlternateClass c (m,r.1) r.2)

@[simp] theorem alternatePayoff_none (m : Message) (c : Cache) :
    alternatePayoff m c none=0 := rfl

@[simp] theorem alternatePayoff_some (m : Message) (c : Cache) (η : BitVec 86) (i : Fin M) :
    alternatePayoff m c (some (η,i))=(if AlternateClass c (m,η) i then 1 else 0) := rfl

attribute [local irreducible] alternatePayoff replayScore optionEvent
theorem alternativePayoff_le (m : Message) (c : Cache)
    (s : Option (WeightedSampling.Winner 86 M))
    (hconsistent : ∀ (η : BitVec 86) (i : Fin M),s=some (η,i) →
      ∀ (y : BitVec 256),c (WideForest.encQuery (m,η))=some y → decode y=some i) :
    alternatePayoff m c s ≤ ENNReal.ofReal
      (WeightedCompletion.score (I := WeightedSampling.Winner 86 M) s
        (fun r : WeightedSampling.Winner 86 M => replayScore m c r.1 r.2)) := by
  unfold alternatePayoff
  exact optionEvent_le_score (fun r => AlternateClass c (m,r.1) r.2)
    (fun r => replayScore m c r.1 r.2) s
    (fun r hs halt => alternative_replayScore m c r.1 r.2 (hconsistent r.1 r.2 hs) halt)

theorem actual_alternative_bound (m : Message) (c : Cache) :
    outE (WeightedSampling.loop 86 decode tier m L) c (alternatePayoff m c) ≤
      ENNReal.ofReal ((99:ℝ)/98*securityWeights.hazard ((2:ℝ)^86)
        (seen (rowDomain m) c).card (classCounts indexDomain c decode)
        (classCounts (rowDomain m) c decode)+tableFailure m c) := by
  apply le_trans (b:=outE (WeightedSampling.loop 86 decode tier m L) c
    (fun s => ENNReal.ofReal (score s (fun r => replayScore m c r.1 r.2))))
  · apply expectedValue_mono_of_support
    intro p hp
    obtain ⟨hsub,hwin⟩ := WeightedSampling.loop_support 86 decode tier m L c p hp
    apply alternativePayoff_le
    intro η i hs y hy
    obtain ⟨z,hz,hzi⟩ := hwin η i hs
    have he : y=z := Option.some.inj ((hsub _ _ hy).symm.trans hz)
    rw [he]
    exact hzi
  · exact actual_replay_bound m c

#print axioms alternative_replayScore
#print axioms actual_alternative_bound
end OptimalOTS.WeightedConstruction.WideCachedRow
