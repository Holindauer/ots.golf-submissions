import Submissions.UpperCompressions.WeightedSelectorPayoff

open OracleSpec OracleComp OracleComp.EvalDist ENNReal
open OptimalOTS OptimalOTS.WeightedSampling
noncomputable section
open scoped Classical
namespace WeightedCompletion
open WeightedReplacement

/-- Exact arbitrary nonnegative payoff under the actual all-trials oracle loop,
once its shared oracle row is fixed. Failure has payoff zero. -/
theorem E_loop_fixed_row_score (n M k : ℕ)
    (decode : BitVec hashBits → Option (Fin M)) (tier : Fin M → ℕ) (m : Message)
    (table : Nonce n → BitVec hashBits) (c : Cache)
    (hc : ∀ η, c ⟨msgBits+n,m++η⟩ = some (table η))
    (f : Nonce n → Fin M → ℝ) (hf : ∀ a i, 0 ≤ f a i) :
    E (run (loop n decode tier m k) c)
      (fun p => ENNReal.ofReal (score p.1 (fun r => f r.1 r.2))) =
      ENNReal.ofReal (tableKernel k (decode ∘ table) tier f) := by
  rw [run_loop_fixed_row n decode tier m table c hc, E_map]
  have hn : ∀ xs : List (Nonce n),
      0 ≤ score (selected (decode ∘ table) tier xs) (fun r => f r.1 r.2) := by
    intro xs
    cases selected (decode ∘ table) tier xs with
    | none => exact le_rfl
    | some r => exact hf r.1 r.2
  have h := E_drawList_ofReal n k
    (fun xs => score (selected (decode ∘ table) tier xs) (fun r => f r.1 r.2)) hn
  rw [iid_selected_score] at h
  exact h

end WeightedCompletion
#print axioms WeightedCompletion.E_loop_fixed_row_score
