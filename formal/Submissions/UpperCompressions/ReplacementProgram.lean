import Submissions.UpperCompressions.ReplacementSelector
import Submissions.UpperCompressions.IUB

/-! The exact finite-table law for the actual probabilistic oracle program.
This closes the conversion between finite iid expectations and `ProbComp`.
Full-table versus lazy-table reasoning and adaptive security are separate. -/

open OracleSpec OracleComp OracleComp.EvalDist ENNReal
open OptimalOTS OptimalOTS.WeightedSampling

namespace WeightedReplacement

open scoped Classical

theorem iidMean_nonneg {α : Type*} [Fintype α] (n : ℕ) (g : List α → ℝ)
    (hg : ∀ xs, 0 ≤ g xs) : 0 ≤ iidMean n g := by
  induction n generalizing g with
  | zero => exact hg []
  | succ n ih =>
    change 0 ≤ (∑ a, iidMean n (fun xs => g (a :: xs))) / (Fintype.card α : ℝ)
    exact div_nonneg (Finset.sum_nonneg fun a _ => ih _ (fun xs => hg (a :: xs)))
      (Nat.cast_nonneg _)

theorem ofReal_uniformMean {α : Type*} [Fintype α] [Nonempty α]
    (g : α → ℝ) (hg : ∀ a, 0 ≤ g a) :
    ENNReal.ofReal (uniformMean g) =
      ∑ a, (Fintype.card α : ℝ≥0∞)⁻¹ * ENNReal.ofReal (g a) := by
  have hcard : (0 : ℝ) < Fintype.card α := by exact_mod_cast Fintype.card_pos
  rw [uniformMean, ENNReal.ofReal_div_of_pos hcard,
    ENNReal.ofReal_sum_of_nonneg (fun a _ => hg a), ENNReal.ofReal_natCast,
    div_eq_mul_inv, Finset.sum_mul]
  exact Finset.sum_congr rfl fun a _ => mul_comm _ _

/-- Every nonnegative real payoff has the same expectation in the executable
private draw program and the explicitly normalized finite iid sample space. -/
theorem E_drawList_ofReal (n k : ℕ) (g : List (Nonce n) → ℝ)
    (hg : ∀ xs, 0 ≤ g xs) :
    E (drawList n k) (fun xs => ENNReal.ofReal (g xs)) =
      ENNReal.ofReal (iidMean k g) := by
  induction k generalizing g with
  | zero => simp [drawList, E_pure, iidMean]
  | succ k ih =>
    rw [drawList, E_bind]
    simp only [E_bind, E_pure]
    rw [E_uniform, iidMean,
      ofReal_uniformMean _ (fun a => iidMean_nonneg k _ (fun xs => hg (a :: xs)))]
    apply Finset.sum_congr rfl
    intro a ha
    rw [ih _ (fun xs => hg (a :: xs))]

/-- The actual all-L oracle loop, conditioned only by fixing its complete table,
returns each accepted nonce with exactly the common tier kernel divided by N. -/
theorem E_loop_fixed_row_target (n M k : ℕ)
    (decode : BitVec hashBits → Option (Fin M)) (tier : Fin M → ℕ) (m : Message)
    (table : Nonce n → BitVec hashBits) (c : Cache)
    (hc : ∀ η, c ⟨msgBits+n,m++η⟩ = some (table η))
    (v : Nonce n) (i : Fin M) (hv : decode (table v) = some i) :
    E (run (loop n decode tier m k) c)
      (fun p => if p.1 = some (v,i) then 1 else 0) =
      ENNReal.ofReal (kernel k
        (fraction (weakRank tier i ∘ decode ∘ table))
        (fraction (strictRank tier i ∘ decode ∘ table)) / Fintype.card (Nonce n)) := by
  rw [run_loop_fixed_row n decode tier m table c hc, E_map]
  have hprob := iid_tagged_table_probability (decode ∘ table) tier v i hv k
  have he := E_drawList_ofReal n k
    (fun xs => if select (fun p : Nonce n × Fin M => tier p.2)
      (xs.map fun a => (fun j => (a,j)) <$> decode (table a)) = some (v,i)
      then (1 : ℝ) else 0)
    (fun _ => by split_ifs <;> norm_num)
  have hp : (iidMean k fun xs => if select (fun p : Nonce n × Fin M => tier p.2)
      (xs.map fun a => (fun j => (a,j)) <$> decode (table a)) = some (v,i)
      then (1 : ℝ) else 0) =
      kernel k (fraction (weakRank tier i ∘ decode ∘ table))
        (fraction (strictRank tier i ∘ decode ∘ table)) / Fintype.card (Nonce n) := by
    convert hprob using 1
    congr 1
    funext xs
    simp only [Function.comp_apply]
    split_ifs <;> rfl
  rw [hp] at he
  simp only [candidate, Function.comp_apply, apply_ite,
    ENNReal.ofReal_one, ENNReal.ofReal_zero] at he ⊢
  convert he using 1
  congr 1

#print axioms E_drawList_ofReal
#print axioms E_loop_fixed_row_target

end WeightedReplacement
