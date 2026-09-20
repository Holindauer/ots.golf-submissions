import Submissions.UpperCompressions.ReplacementCompletionTail
import Submissions.UpperCompressions.ReplacementEagerPrefix
import Submissions.UpperCompressions.WideTableGood

/-! Concrete mixed72 row-completion failure after the actual adaptive public
prefix. This is the averaged delta term in the cached replay/excess bounds. -/
open OracleSpec OracleComp OracleComp.EvalDist ENNReal
open OptimalOTS
namespace WeightedReplacement
noncomputable section
open scoped Classical
set_option maxRecDepth 10000
open OptimalOTS.WeightedConstruction.WeightedSchedule
local instance (priority := 100000) stagedLocal_ReplacementConcreteCompletion_1 {α : Type*} : DecidableEq α := Classical.decEq α

theorem actual_rowGood_completion_failure {α : Type} (oa : OracleComp Spec α)
    (c : Cache) (hc : ∀ x : BitVec 342, c ⟨342,x⟩ = none) (message : α → Message) :
    E (run oa c) (fun p => ENNReal.ofReal (uniformMean
      (fun g : BitVec 342 → BitVec 256 =>
        if rowGood (decode ∘ cachedRow 86 (message p.1) p.2 g) then (0:ℝ) else 1))) ≤
      (2:ℝ≥0∞)⁻¹^761 := by
  apply (le_trans (b := E (run oa c) (fun p => E ($ᵗ (BitVec (msgBits+86) → BitVec hashBits))
    (fun g => if fullRowBad prefixPredicates (completedTable (msgBits+86) p.2 g) then 1 else 0))))
  · apply E_mono
    intro p
    rw [← E_uniform_ofReal
      (fun g : BitVec 342 → BitVec 256 =>
        if rowGood (decode ∘ cachedRow 86 (message p.1) p.2 g) then (0:ℝ) else 1)
      (fun g => by split_ifs <;> norm_num)]
    apply E_mono
    intro g
    by_cases hr : rowGood (decode ∘ cachedRow 86 (message p.1) p.2 g)
    · simp only [if_pos hr, ENNReal.ofReal_zero]
      exact bot_le
    · have hb : fullRowBad prefixPredicates (completedTable (msgBits+86) p.2 g) := by
        by_contra hn
        apply hr
        exact fullTableGood_row _ hn (message p.1)
      simp only [if_neg hr, ENNReal.ofReal_one, if_pos hb]
      exact le_rfl
  · exact completed_full_bad_probability oa c hc prefixPredicates

#print axioms actual_rowGood_completion_failure
end
end WeightedReplacement
