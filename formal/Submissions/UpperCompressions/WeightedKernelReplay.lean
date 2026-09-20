import Submissions.UpperCompressions.WeightedReplay
import Submissions.UpperCompressions.WeightedProgramPayoff

/-! Integrate the exact first-minimum kernel with unconditional row completion.
This supplies replay and excess bounds from the pointwise kernel envelope, with
no conditioning on the good-table event. -/
noncomputable section
open scoped BigOperators Classical
namespace WeightedCompletion
open WeightedReplacement
variable {Ω D I : Type} [Fintype Ω] [Nonempty Ω] [Fintype D] [Nonempty D]
  [Fintype I] [DecidableEq D] [DecidableEq I]

theorem tableKernel_reference_le (n : ℕ) (R : Finset D)
    (table : Ω → D → Option I) (tier : I → ℕ) (p g fKnown fFresh : I → ℝ)
    (hK : ∀ i, 0 ≤ fKnown i) (hF : ∀ i, 0 ≤ fFresh i) (F : ℝ) (ω : Ω)
    (hk : ∀ i, kernel n (fraction (weakRank tier i ∘ table ω))
      (fraction (strictRank tier i ∘ table ω)) ≤ F * (g i / p i)) :
    tableKernel n (table ω) tier (fun a i => if a ∈ R then fKnown i else fFresh i) ≤
      F * referencePayoff R table p g fKnown fFresh ω := by
  unfold tableKernel referencePayoff
  rw [← mul_div_assoc, Finset.mul_sum]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  apply Finset.sum_le_sum
  intro a _
  cases ht : table ω a with
  | none => simp [score, ht]
  | some i =>
    simp only [score, ht, Option.map_some, Option.getD_some]
    by_cases ha : a ∈ R
    · rw [if_pos ha, if_pos ha]
      exact (mul_le_mul_of_nonneg_right (hk i) (hK i)).trans_eq (by ring)
    · rw [if_neg ha, if_neg ha]
      exact (mul_le_mul_of_nonneg_right (hk i) (hF i)).trans_eq (by ring)

/-- Actual first-minimum replay probability, averaged over the original table
completion law, is bounded by the clipped public replay hazard plus the bad tail. -/
theorem replay_kernel_bound (w : WeightedRow.Weights I) (n : ℕ) (tier : I → ℕ)
    (R : Finset D) (fixed : D → Option I) (table : Ω → D → Option I) (k : I → ℕ)
    (hknown : ∀ ω a, a ∈ R → table ω a = fixed a)
    (hfresh : ∀ a, a ∉ R → ∀ i,
      uniformMean (fun ω => if table ω a = some i then 1 else 0) = w.p i)
    (Good : Ω → Prop) (F δ : ℝ) (hF : 0 ≤ F)
    (hkernel : ∀ ω, Good ω → ∀ i, kernel n
      (fraction (weakRank tier i ∘ table ω)) (fraction (strictRank tier i ∘ table ω)) ≤
        F * (w.g i / w.p i))
    (hbad : uniformMean (fun ω => if Good ω then 0 else 1) ≤ δ) :
    uniformMean (fun ω => tableKernel n (table ω) tier (fun a i =>
      if a ∈ R then (if 2 ≤ k i then 1 else 0) else (if k i = 0 then 0 else 1))) ≤
      F * w.hazard (Fintype.card D) R.card k (rowCount R fixed) + δ := by
  apply replay_bound w R fixed table k hknown hfresh Good _ F δ hF
  · intro ω hg
    exact tableKernel_reference_le n R table tier w.p w.g _ _
      (fun i => by split_ifs <;> norm_num) (fun i => by split_ifs <;> norm_num) F ω (hkernel ω hg)
  · intro ω
    apply tableKernel_le n (table ω) tier _ 1 zero_le_one
    intro a i
    split_ifs <;> norm_num
  · exact hbad

/-- Post-sign excess payoff for the same actual selector and completion law. -/
theorem excess_kernel_bound (w : WeightedRow.Weights I) (n : ℕ) (tier : I → ℕ)
    (R : Finset D) (fixed : D → Option I) (table : Ω → D → Option I)
    (hknown : ∀ ω a, a ∈ R → table ω a = fixed a)
    (hfresh : ∀ a, a ∉ R → ∀ i,
      uniformMean (fun ω => if table ω a = some i then 1 else 0) = w.p i)
    (e : I → ℝ) (he : ∀ i, 0 ≤ e i) (emax : ℝ) (hemax : 0 ≤ emax) (hesc : ∀ i, e i ≤ emax)
    (Good : Ω → Prop) (F δ : ℝ) (hF : 0 ≤ F)
    (hkernel : ∀ ω, Good ω → ∀ i, kernel n
      (fraction (weakRank tier i ∘ table ω)) (fraction (strictRank tier i ∘ table ω)) ≤
        F * (w.g i / w.p i))
    (hbad : uniformMean (fun ω => if Good ω then 0 else 1) ≤ δ) :
    uniformMean (fun ω => tableKernel n (table ω) tier (fun _ i => e i)) ≤
      F * ((1-(R.card : ℝ)/Fintype.card D) * (∑ i, w.g i * e i) +
        (∑ i, (rowCount R fixed i : ℝ) * (w.g i/w.p i * e i)) / Fintype.card D) + emax * δ := by
  apply excess_bound w R fixed table hknown hfresh e he Good _ F emax δ hF hemax
  · intro ω hg
    simpa only [ite_self] using
      tableKernel_reference_le n R table tier w.p w.g e e he he F ω (hkernel ω hg)
  · intro ω
    exact tableKernel_le n (table ω) tier (fun _ i => e i) emax hemax (fun _ i => hesc i)
  · exact hbad

end WeightedCompletion
#print axioms WeightedCompletion.replay_kernel_bound
#print axioms WeightedCompletion.excess_kernel_bound
