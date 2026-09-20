import Submissions.UpperCompressions.ReplacementSignedUnion

/-! Remaining-budget accounting after an arbitrary signer distribution. The
index excess and graph base rate use one actual continuation and cache. -/
open OracleSpec OracleComp OracleComp.EvalDist ENNReal
open OptimalOTS
namespace WeightedReplacement
noncomputable section
open scoped Classical BigOperators
local instance (priority := 100000) stagedLocal_ReplacementSignedBudget_1 {α : Type*} : DecidableEq α := Classical.decEq α

theorem index_expectedCharge_le {α : Type} (isIndex : Spec.Domain → Prop)
    (oa : OracleComp Spec α) (c : Cache) (B : ℕ) (hB : CostAtMost oa B) :
    expectedCharge (indexPaid isIndex) oa c ≤ B := by
  have hc : ∀ t, indexPaid isIndex t ≤ (1:ℝ≥0∞)*queryCost t := by
    intro t
    unfold indexPaid
    split_ifs <;> simp
  simpa using expectedCharge_budget (indexPaid isIndex) 1 hc oa B hB c

/-- A fixed signed class's index expenditure is bounded by its joint mass times
the remaining pathwise budget. This preserves the sign event explicitly. -/
theorem signedCharge_remaining {β γ : Type} (p : ProbComp (β × Cache))
    (post : β → OracleComp Spec γ) (b : β) (isIndex : Spec.Domain → Prop)
    (B : ℕ) (hB : CostAtMost (post b) B) :
    signedCharge p post b (indexPaid isIndex) ≤
      E p (fun r => if r.1 = b then (1:ℝ≥0∞) else 0) * B := by
  unfold signedCharge
  calc
    _ ≤ E p (fun r => (if r.1 = b then (1:ℝ≥0∞) else 0) * B) := by
      apply E_mono
      intro r
      by_cases hr : r.1 = b
      · simp only [hr, if_pos, one_mul]
        exact index_expectedCharge_le isIndex (post b) r.2 B hB
      · simp [hr]
    _ = _ := expectedValue_mul_const _ _ _

theorem signed_excess_remaining {β γ : Type} (p : ProbComp (β × Cache))
    (post : β → OracleComp Spec γ) (excess : β → ℝ≥0∞) (isIndex : Spec.Domain → Prop)
    (B : ℕ) (hB : ∀ b, CostAtMost (post b) B) :
    E p (fun r => excess r.1 * expectedCharge (indexPaid isIndex) (post r.1) r.2) ≤
      E p (fun r => excess r.1) * B := by
  calc
    _ ≤ E p (fun r => excess r.1 * B) := E_mono p
      (fun r => mul_le_mul' le_rfl (index_expectedCharge_le isIndex (post r.1) r.2 B (hB r.1)))
    _ = _ := expectedValue_mul_const _ _ _

/-- The class-dependent index rate is a common base plus excess; the graph rate
uses only the common base, so the base portion pays for the total cost once. -/
theorem paid_shared_budget_excess {γ : Type} (isIndex : Spec.Domain → Prop)
    (base extra : ℝ≥0∞) (oa : OracleComp Spec γ) (c : Cache) (B : ℕ)
    (hB : CostAtMost oa B) :
    (base+extra)*expectedCharge (indexPaid isIndex) oa c +
      base*expectedCharge (otherPaid isIndex) oa c ≤ base*B + extra*B := by
  calc
    _ = (base*expectedCharge (indexPaid isIndex) oa c + base*expectedCharge (otherPaid isIndex) oa c) +
        extra*expectedCharge (indexPaid isIndex) oa c := by ring
    _ ≤ base*B + extra*B := add_le_add
      (by simpa using paid_shared_budget isIndex base base oa c B hB)
      (mul_le_mul' le_rfl (index_expectedCharge_le isIndex oa c B hB))

/-- Averaging over the actual signer keeps the expected excess class score,
rather than replacing it by the largest possible class rate. -/
theorem integrated_shared_budget {β γ : Type} (p : ProbComp (β × Cache))
    (post : β → OracleComp Spec γ) (isIndex : Spec.Domain → Prop)
    (base : ℝ≥0∞) (excess : β → ℝ≥0∞) (B : ℕ)
    (hB : ∀ b, CostAtMost (post b) B) :
    E p (fun r => (base+excess r.1)*expectedCharge (indexPaid isIndex) (post r.1) r.2 +
      base*expectedCharge (otherPaid isIndex) (post r.1) r.2) ≤
      base*B + E p (fun r => excess r.1)*B := by
  calc
    _ ≤ E p (fun r => base*B + excess r.1*B) := E_mono p
      (fun r => paid_shared_budget_excess isIndex base (excess r.1) (post r.1) r.2 B (hB r.1))
    _ = E p (fun _ => base*B) + E p (fun r => excess r.1)*B := by
      calc
        _ = E p (fun _ => base*B) + E p (fun r => excess r.1*B) := expectedValue_add p _ _
        _ = _ := congrArg (E p (fun _ => base*B) + ·) (expectedValue_mul_const p _ _)
    _ ≤ _ := add_le_add (E_const_le _ _) le_rfl

/-- A finite family of joint signed events reconstructs the weighted expected
excess without losing correlation between the returned class and its cost. -/
theorem signedCharge_weighted_sum {β γ : Type} [Fintype β] (p : ProbComp (β × Cache))
    (post : β → OracleComp Spec γ) (weight : β → ℝ≥0∞) (charge : Spec.Domain → ℝ≥0∞) :
    (∑ b, weight b * signedCharge p post b charge) =
      E p (fun r => weight r.1*expectedCharge charge (post r.1) r.2) := by
  unfold signedCharge
  have hm (b : β) : weight b * E p (fun r => if r.1 = b then expectedCharge charge (post r.1) r.2 else 0) =
      E p (fun r => weight b * (if r.1 = b then expectedCharge charge (post r.1) r.2 else 0)) := by
    simpa only [mul_comm] using (expectedValue_mul_const p
      (fun r => if r.1 = b then expectedCharge charge (post r.1) r.2 else 0) (weight b)).symm
  simp_rw [hm]
  rw [← expectedValue_finsetSum]
  congr 1
  funext r
  simp only [mul_ite, mul_zero]
  simp

#print axioms signedCharge_remaining
#print axioms signed_excess_remaining
#print axioms integrated_shared_budget
#print axioms signedCharge_weighted_sum
end
end WeightedReplacement
