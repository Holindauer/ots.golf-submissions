import Submissions.UpperCompressions.DualCountSteps
import Submissions.UpperCompressions.ExpectedChargeMaster
import Submissions.UpperCompressions.WideIndexDomains
import Submissions.UpperCompressions.ReplacementFreshIndex

/-! Distinct public inputs are charged to the same actual query stream.
The initial cache contribution is explicit; private sampling queries add no
public input. Repeated hash queries remain paid but cannot increase the count. -/
noncomputable section
open OracleSpec OracleComp OracleComp.EvalDist ENNReal
open scoped Classical
namespace WeightedDualCache
open OptimalOTS WeightedCacheCounts WeightedDirectCache WeightedReplacement
set_option maxHeartbeats 800000
attribute [local irreducible] Finset.univ Finset.filter

theorem expected_seen_le_charge {β : Type} (A : Finset Query)
    (charge : Spec.Domain → ℝ≥0∞)
    (hcharge : ∀ t c, ((if protectedFresh A t c then 1 else 0 : ℕ) : ℝ≥0∞) ≤ charge t)
    (oa : OracleComp Spec β) (c : Cache) :
    E (run oa c) (fun p => ((seen A p.2).card : ℝ≥0∞)) ≤
      ((seen A c).card : ℝ≥0∞) + expectedCharge charge oa c := by
  have hstep (t : Spec.Domain) (d : Cache) :
      E ((oracleImpl t).run d) (fun p => ((seen A p.2).card : ℝ≥0∞)) ≤
        ((seen A d).card : ℝ≥0∞) + 1*charge t := by
    apply (expectedValue_mono_of_support (h := fun _ =>
      ((seen A d).card : ℝ≥0∞) + 1*charge t) ?_).trans (E_const_le _ _)
    intro p hp
    rw [actual_seen_count A t d p hp, Nat.cast_add, one_mul]
    exact add_le_add le_rfl (hcharge t d)
  simpa only [one_mul] using WeightedExpectedCharge.master_expected
    (fun d => ((seen A d).card : ℝ≥0∞)) charge 1 hstep oa c

theorem expected_seen_le_indexPaid {β : Type} (A : Finset Query)
    (isIndex : Spec.Domain → Prop) (hindex : ∀ q∈A, isIndex (.inr q))
    (oa : OracleComp Spec β) (c : Cache) :
    E (run oa c) (fun p => ((seen A p.2).card : ℝ≥0∞)) ≤
      ((seen A c).card : ℝ≥0∞) + expectedCharge (indexPaid isIndex) oa c := by
  apply expected_seen_le_charge A (indexPaid isIndex) _ oa c
  intro t d
  cases t with
  | inl n => simp [protectedFresh]
  | inr q =>
    by_cases h : protectedFresh A (.inr q) d
    · have hq : q∈A := of_decide_eq_true (Bool.and_eq_true_iff.mp h).1
      rw [if_pos h, Nat.cast_one, indexPaid, if_pos (hindex q hq)]
      exact_mod_cast (show 1≤queryCost (.inr q) from le_max_left _ _)
    · simp only [if_neg h, Nat.cast_zero]
      exact bot_le

#print axioms expected_seen_le_indexPaid
end WeightedDualCache

namespace OptimalOTS.WeightedConstruction.WideDomains
open WeightedCacheCounts WeightedReplacement
attribute [local irreducible] Finset.univ Finset.filter

theorem distinct_index_le_expected_paid {β : Type} (oa : OracleComp Spec β)
    (c : Cache) (hf : ∀ q : Query, q.1=342 → c q=none) :
    E (run oa c) (fun p => ((seen indexDomain p.2).card : ℝ≥0∞)) ≤
      expectedCharge (indexPaid (isIndexLength 342)) oa c := by
  have h := WeightedDualCache.expected_seen_le_indexPaid indexDomain (isIndexLength 342)
    (fun q hq => (mem_indexDomain q).mp hq) oa c
  rw [fresh_seen_empty c hf, Finset.card_empty, Nat.cast_zero, zero_add] at h
  exact h

theorem distinct_other_le_expected_paid {β : Type} (oa : OracleComp Spec β)
    (c : Cache) (hf : ∀ q : Query, q.1=342 → c q=none) :
    E (run oa c) (fun p => ((seen indexDomain p.2).card : ℝ≥0∞)) +
      expectedCharge (otherPaid (isIndexLength 342)) oa c ≤
      expectedCharge (fun t => queryCost t) oa c := by
  exact (add_le_add (distinct_index_le_expected_paid oa c hf) le_rfl).trans_eq
    (paid_split (isIndexLength 342) oa c)

theorem distinct_other_remaining_le {β : Type} (oa : OracleComp Spec β)
    (c : Cache) (hf : ∀ q : Query, q.1=342 → c q=none)
    (remaining : β × Cache → ℝ≥0∞) (B : ℝ≥0∞)
    (hB : expectedCharge (fun t => queryCost t) oa c + E (run oa c) remaining ≤ B) :
    E (run oa c) (fun p => ((seen indexDomain p.2).card : ℝ≥0∞)) +
      expectedCharge (otherPaid (isIndexLength 342)) oa c + E (run oa c) remaining ≤ B :=
  (add_le_add (distinct_other_le_expected_paid oa c hf) le_rfl).trans hB

#print axioms distinct_index_le_expected_paid
#print axioms distinct_other_remaining_le
end OptimalOTS.WeightedConstruction.WideDomains
