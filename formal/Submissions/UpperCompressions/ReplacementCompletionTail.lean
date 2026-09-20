import Submissions.UpperCompressions.ReplacementCompletion
import Submissions.UpperCompressions.ReplacementTableGood

/-! Adaptive observed-cache completions inherit the unconditional full-table
tail. No pointwise bound is asserted for a particular adversarial transcript. -/
open OracleSpec OracleComp OracleComp.EvalDist ENNReal
open OptimalOTS
namespace WeightedReplacement
noncomputable section
open scoped Classical
local instance (priority := 100000) stagedLocal_ReplacementCompletionTail_1 {α : Type*} : DecidableEq α := Classical.decEq α
attribute [local irreducible] hashBits msgBits signBudget

def completedTable (b : ℕ) (c : Cache) (g : BitVec b → BitVec hashBits) :
    BitVec b → BitVec hashBits := fun x => (c ⟨b,x⟩).getD (g x)

def readTable (b : ℕ) (c : Cache) : BitVec b → BitVec hashBits :=
  fun x => (c ⟨b,x⟩).getD 0

theorem readTable_preload (b : ℕ) (c : Cache) (g : BitVec b → BitVec hashBits) :
    readTable b ((lengthSlice b).preload c g) = completedTable b c g := by
  funext x
  unfold readTable completedTable QuerySlice.preload
  rw [Cache.extend_apply, lengthSlice_inside]
  cases c ⟨b,x⟩ <;> rfl

theorem preload_complete_initial (b : ℕ) (c : Cache)
    (hc : ∀ x : BitVec b, c ⟨b,x⟩ = none) (g : BitVec b → BitVec hashBits) :
    ∀ x : BitVec b, (lengthSlice b).preload c g ⟨b,x⟩ = some (g x) := by
  intro x
  unfold QuerySlice.preload
  rw [Cache.extend_apply, hc x, lengthSlice_inside]
  rfl

theorem readTable_run_preload {α : Type} (b : ℕ) (oa : OracleComp Spec α)
    (c : Cache) (hc : ∀ x : BitVec b, c ⟨b,x⟩ = none)
    (g : BitVec b → BitVec hashBits) (p : α × Cache)
    (hp : p ∈ support (run oa ((lengthSlice b).preload c g))) :
    readTable b p.2 = g := by
  funext x
  have h := sub_of_mem_support_run oa _ p hp _ _ (preload_complete_initial b c hc g x)
  simp only [readTable, h, Option.getD_some]

/-- Averaging the posterior completion of the actual final public cache cannot
increase any unconditional bad-table probability. The program may be adaptive. -/
theorem completed_bad_probability_le {α : Type} (b : ℕ) (oa : OracleComp Spec α)
    (c : Cache) (hc : ∀ x : BitVec b, c ⟨b,x⟩ = none)
    (bad : (BitVec b → BitVec hashBits) → Prop) :
    E (run oa c) (fun p => E ($ᵗ (BitVec b → BitVec hashBits))
      (fun g => if bad (completedTable b p.2 g) then 1 else 0)) ≤
      E ($ᵗ (BitVec b → BitVec hashBits)) (fun g => if bad g then 1 else 0) := by
  have h := cacheE_finite_completion (lengthSlice b) oa c
    (fun _ d => if bad (readTable b d) then 1 else 0)
  simp only [cacheE, completePayoff, readTable_preload] at h
  rw [h]
  apply E_mono
  intro g
  calc
    _ ≤ E (run oa ((lengthSlice b).preload c g)) (fun _ => if bad g then 1 else 0) := by
      apply expectedValue_mono_of_support
      intro p hp
      rw [readTable_run_preload b oa c hc g p hp]
    _ ≤ _ := E_const_le _ _

/-- All72 prefix deficits over every message row retain the unconditional tail
after any actual adaptive public computation and its observed cache. -/
theorem completed_full_bad_probability {α : Type} (oa : OracleComp Spec α)
    (c : Cache) (hc : ∀ x : BitVec (msgBits+86), c ⟨msgBits+86,x⟩ = none)
    (P : Fin 72 → BitVec hashBits → Prop) :
    E (run oa c) (fun p => E ($ᵗ (BitVec (msgBits+86) → BitVec hashBits))
      (fun g => if fullRowBad P (completedTable (msgBits+86) p.2 g) then 1 else 0)) ≤
        (2:ℝ≥0∞)⁻¹^761 := by
  apply (completed_bad_probability_le (msgBits+86) oa c hc (fullRowBad P)).trans
  convert full_table_bad_probability P using 1
  · rfl
  · congr 1
    funext g
    unfold fullRowBad
    split_ifs <;> rfl

/-- The message row can itself be chosen by the adaptive computation. This
bounds the average conditional completion failure, not each transcript's value. -/
theorem completed_chosen_row_bad_probability {α : Type} (oa : OracleComp Spec α)
    (c : Cache) (hc : ∀ x : BitVec (msgBits+86), c ⟨msgBits+86,x⟩ = none)
    (message : α → Message) (P : Fin 72 → BitVec hashBits → Prop) :
    E (run oa c) (fun p => E ($ᵗ (BitVec (msgBits+86) → BitVec hashBits))
      (fun g => if ∃ j : Fin 72,
        empirical (P j) (fun η : BitVec 86 => completedTable (msgBits+86) p.2 g (message p.1 ++ η)) ≤
          fraction (P j)-1/(100*(2:ℝ)^20) then 1 else 0)) ≤ (2:ℝ≥0∞)⁻¹^761 := by
  apply (le_trans (b := E (run oa c) (fun p => E ($ᵗ (BitVec (msgBits+86) → BitVec hashBits))
    (fun g => if fullRowBad P (completedTable (msgBits+86) p.2 g) then 1 else 0))))
  · apply E_mono
    intro p
    apply E_mono
    intro g
    by_cases hh : ∃ j : Fin 72,
        empirical (P j) (fun η : BitVec 86 => completedTable (msgBits+86) p.2 g (message p.1 ++ η)) ≤
          fraction (P j)-1/(100*(2:ℝ)^20)
    · have hb : fullRowBad P (completedTable (msgBits+86) p.2 g) := by
        obtain ⟨j,hj⟩ := hh
        exact ⟨(message p.1,j),hj⟩
      simp only [if_pos hh, if_pos hb]
      exact le_rfl
    · simp only [if_neg hh]
      exact bot_le
  · exact completed_full_bad_probability oa c hc P

#print axioms completed_bad_probability_le
#print axioms completed_full_bad_probability
#print axioms completed_chosen_row_bad_probability
end
end WeightedReplacement
