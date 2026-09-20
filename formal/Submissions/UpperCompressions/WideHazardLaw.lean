import Submissions.UpperCompressions.DualProtectedLaw
import Submissions.UpperCompressions.WidePreSign

/-! The concrete row hazard is a function of the actual shared oracle cache.
This file identifies its complete primitive-query distribution. -/
noncomputable section
open OracleSpec OracleComp
open scoped Classical

namespace WeightedDualCache
theorem protectedPhase_inside_witness {D B : Type} [DecidableEq D]
    (A G : Finset D) (t : (unifSpec+(D →ₒ B)).Domain) (c : (D →ₒ B).QueryCache)
    (h : protectedPhase A G t c = .inside) :
    ∃ q : D, c q=none ∧ q∈A := by
  cases t with
  | inl t => simp [protectedPhase] at h
  | inr q =>
    cases hc : c q with
    | some u => simp [protectedPhase,phase,hc] at h
    | none =>
      refine ⟨q,hc,?_⟩
      by_contra hn
      simp only [protectedPhase,phase,hc,Option.isSome_none,Bool.false_eq_true,ite_false,hn] at h
      split_ifs at h
end WeightedDualCache

namespace OptimalOTS.WeightedConstruction.WideHazard
open WeightedSchedule WideDomains WeightedCacheCounts WeightedRow.Weights
open WeightedRealExecution WeightedDualCache WeightedReference WeightedConstants
attribute [local irreducible] Finset.univ Finset.filter

def N : ℝ := 2^86
def rowCount (m : Message) (c : hashSpec.QueryCache) : ℕ :=
  (WeightedCacheCounts.seen (rowDomain m) c).card
def globalCounts (c : hashSpec.QueryCache) : Fin M → ℕ :=
  classCounts indexDomain c decode
def rowCounts (m : Message) (c : hashSpec.QueryCache) : Fin M → ℕ :=
  classCounts (rowDomain m) c decode
def hazard (m : Message) (c : hashSpec.QueryCache) : ℝ :=
  securityWeights.hazard N (rowCount m c) (globalCounts c) (rowCounts m c)
def queryPhase (m : Message) (t : Spec.Domain) (c : hashSpec.QueryCache) : Phase :=
  protectedPhase (rowDomain m) indexDomain t c
def nextHazard (s : Phase) (m : Message) (c : hashSpec.QueryCache) : Option (Fin M) → ℝ :=
  after (securityWeights.hazard N) s (rowCount m c) (globalCounts c) (rowCounts m c)
def delta (s : Phase) (m : Message) (c : hashSpec.QueryCache) (x : Option (Fin M)) : ℝ :=
  nextHazard s m c x-hazard m c

theorem primitive_joint_law (m : Message) (t : Spec.Domain) (c : hashSpec.QueryCache)
    (f : ℕ → (Fin M → ℕ) → (Fin M → ℕ) → ℝ) :
    realEval ((oracleImpl t).run c)
      (fun out => f (rowCount m out.2) (globalCounts out.2) (rowCounts m out.2)) =
    securityWeights.expect (after f (queryPhase m t c) (rowCount m c)
      (globalCounts c) (rowCounts m c)) :=
  WeightedDualCache.actual_query_law securityWeights (rowDomain m) indexDomain
    (row_subset m) decode decoder_law t c f


theorem primitive_delta_law (m : Message) (t : Spec.Domain) (c : hashSpec.QueryCache)
    (f : ℝ → ℝ) :
    realEval ((oracleImpl t).run c) (fun out => f (hazard m out.2-hazard m c)) =
    securityWeights.expect (fun x => f (delta (queryPhase m t c) m c x)) := by
  have h := primitive_joint_law m t c
    (fun r k row => f (securityWeights.hazard N r k row-hazard m c))
  exact h.trans (congrArg securityWeights.expect (after_comp
    (fun z => f (z-hazard m c)) (securityWeights.hazard N)
    (queryPhase m t c) (rowCount m c) (globalCounts c) (rowCounts m c)))


theorem row_le_global (m : Message) (c : hashSpec.QueryCache) (i : Fin M) :
    rowCounts m c i ≤ globalCounts c i := row_class_le_global m c i

theorem rowCount_le (m : Message) (c : hashSpec.QueryCache) : (rowCount m c : ℝ) ≤ N := by
  have h : (rowCount m c : ℝ) ≤ ((2^86 : ℕ) : ℝ) :=
    Nat.cast_le.mpr (seen_row_bound m c)
  exact h.trans_eq (by norm_num [N])


theorem inside_rowCount_succ_le (m : Message) (t : Spec.Domain)
    (c : hashSpec.QueryCache) (h : queryPhase m t c = .inside) :
    (rowCount m c : ℝ)+1 ≤ N := by
  obtain ⟨q,hc,hq⟩ := protectedPhase_inside_witness (rowDomain m) indexDomain t c h
  have hb : (((rowCount m c)+1 : ℕ) : ℝ) ≤ ((2^86 : ℕ) : ℝ) :=
    Nat.cast_le.mpr (fresh_row_succ_bound m c q hq hc)
  have he : (((rowCount m c)+1 : ℕ) : ℝ) = (rowCount m c : ℝ)+1 :=
    (Nat.cast_add (rowCount m c) 1).trans
      (congrArg (fun z : ℝ => (rowCount m c : ℝ)+z) Nat.cast_one)
  exact he.symm.trans_le (hb.trans_eq (by norm_num [N]))

theorem primitive_delta_support (m : Message) (t : Spec.Domain) (c : hashSpec.QueryCache)
    (out : Spec.Range t × hashSpec.QueryCache)
    (hout : out ∈ support ((oracleImpl t).run c)) :
    ∃ x : Option (Fin M), hazard m out.2-hazard m c = delta (queryPhase m t c) m c x := by
  obtain ⟨x,hx⟩ := actual_payoff_support (rowDomain m) indexDomain (row_subset m)
    decode t c (securityWeights.hazard N) out hout
  exact ⟨x,congrArg (fun z => z-hazard m c) hx⟩

#print axioms primitive_delta_law
#print axioms inside_rowCount_succ_le
#print axioms primitive_delta_support
end OptimalOTS.WeightedConstruction.WideHazard
