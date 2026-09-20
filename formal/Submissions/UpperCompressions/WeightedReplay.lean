import Submissions.UpperCompressions.WeightedCompletion

/-! Exact finite-completion formulas for replay and the post-sign excess payoff.
Good remains a joint event; fresh-coordinate marginals are unconditional. -/
noncomputable section
open scoped BigOperators Classical
namespace WeightedCompletion
open WeightedReplacement
variable {Ω D I : Type*} [Fintype Ω] [Nonempty Ω] [Fintype D] [Nonempty D]
  [Fintype I] [DecidableEq D] [DecidableEq I]

/-- Kernel-envelope reference payoff, with different scores at exposed and
unexposed candidate nonces. Failure contributes zero. -/
def referencePayoff (R : Finset D) (table : Ω → D → Option I)
    (p g fKnown fFresh : I → ℝ) (ω : Ω) : ℝ :=
  (∑ a : D, if a ∈ R then score (table ω a) (fun i => g i / p i * fKnown i)
    else score (table ω a) (fun i => g i / p i * fFresh i)) / Fintype.card D

theorem referencePayoff_nonneg (R : Finset D) (table : Ω → D → Option I)
    (p g fKnown fFresh : I → ℝ) (hp : ∀ i, 0 < p i) (hg : ∀ i, 0 ≤ g i)
    (hK : ∀ i, 0 ≤ fKnown i) (hF : ∀ i, 0 ≤ fFresh i) (ω : Ω) :
    0 ≤ referencePayoff R table p g fKnown fFresh ω := by
  apply div_nonneg _ (Nat.cast_nonneg _)
  apply Finset.sum_nonneg
  intro a _
  cases ht : table ω a with
  | none => simp [score, ht]
  | some i =>
    simp only [score, ht, Option.map_some, Option.getD_some]
    split_ifs
    · exact mul_nonneg (div_nonneg (hg i) (hp i).le) (hK i)
    · exact mul_nonneg (div_nonneg (hg i) (hp i).le) (hF i)

theorem referencePayoff_mean (R : Finset D) (fixed : D → Option I)
    (table : Ω → D → Option I) (p g fKnown fFresh : I → ℝ) (hp : ∀ i, 0 < p i)
    (hknown : ∀ ω a, a ∈ R → table ω a = fixed a)
    (hfresh : ∀ a, a ∉ R → ∀ i,
      uniformMean (fun ω => if table ω a = some i then 1 else 0) = p i) :
    uniformMean (referencePayoff R table p g fKnown fFresh) =
      (1-(R.card : ℝ)/Fintype.card D) * (∑ i, g i * fFresh i) +
        (∑ i, (rowCount R fixed i : ℝ) * (g i / p i * fKnown i)) / Fintype.card D := by
  have hN : (Fintype.card D : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hc := completion_score R fixed table p (fun i => g i / p i * fKnown i)
    (fun i => g i / p i * fFresh i) hknown hfresh
  have hs : (∑ i, p i * (g i / p i * fFresh i)) = ∑ i, g i * fFresh i := by
    apply Finset.sum_congr rfl
    intro i _
    field_simp [(hp i).ne']
  rw [hs] at hc
  have hdiv (f : Ω → ℝ) (n : ℝ) : uniformMean (fun ω => f ω / n) = uniformMean f / n := by
    unfold uniformMean
    rw [← Finset.sum_div]
    ring
  unfold referencePayoff
  rw [hdiv, hc]
  field_simp
  ring

/-- Exact expected public replay reference, excluding the chosen cached entry
itself: fresh candidates require k_i>0, cached candidates require k_i≥2. -/
theorem replay_reference_mean (w : WeightedRow.Weights I)
    (R : Finset D) (fixed : D → Option I) (table : Ω → D → Option I) (k : I → ℕ)
    (hknown : ∀ ω a, a ∈ R → table ω a = fixed a)
    (hfresh : ∀ a, a ∉ R → ∀ i,
      uniformMean (fun ω => if table ω a = some i then 1 else 0) = w.p i) :
    uniformMean (referencePayoff R table w.p w.g
      (fun i => if 2 ≤ k i then 1 else 0) (fun i => if k i = 0 then 0 else 1)) =
      w.hazard (Fintype.card D) R.card k (rowCount R fixed) := by
  rw [referencePayoff_mean R fixed table w.p w.g _ _ w.p_pos hknown hfresh]
  unfold WeightedRow.Weights.hazard WeightedRow.Weights.seen WeightedRow.Weights.bad
  congr 1
  · congr 1
    apply Finset.sum_congr rfl
    intro i _
    split_ifs <;> simp
  · congr 1
    apply Finset.sum_congr rfl
    intro i _
    split_ifs <;> simp <;> ring

/-- Replay bound using the pointwise good-table kernel envelope. This theorem
retains an explicit exact sampler-payoff premise until the program adapter is supplied. -/
theorem replay_bound (w : WeightedRow.Weights I)
    (R : Finset D) (fixed : D → Option I) (table : Ω → D → Option I) (k : I → ℕ)
    (hknown : ∀ ω a, a ∈ R → table ω a = fixed a)
    (hfresh : ∀ a, a ∉ R → ∀ i,
      uniformMean (fun ω => if table ω a = some i then 1 else 0) = w.p i)
    (Good : Ω → Prop) (replay : Ω → ℝ) (F δ : ℝ) (hF : 0 ≤ F)
    (hkernel : ∀ ω, Good ω → replay ω ≤ F * referencePayoff R table w.p w.g
      (fun i => if 2 ≤ k i then 1 else 0) (fun i => if k i = 0 then 0 else 1) ω)
    (hmax : ∀ ω, replay ω ≤ 1)
    (hbad : uniformMean (fun ω => if Good ω then 0 else 1) ≤ δ) :
    uniformMean replay ≤ F * w.hazard (Fintype.card D) R.card k (rowCount R fixed) + δ := by
  have h := joint_good_bound Good replay _ F 1 δ hF zero_le_one
    (referencePayoff_nonneg R table w.p w.g _ _ w.p_pos w.g_nonneg
      (fun i => by split_ifs <;> norm_num) (fun i => by split_ifs <;> norm_num))
    hkernel hmax hbad
  rw [replay_reference_mean w R fixed table k hknown hfresh, one_mul] at h
  exact h

/-- Excess-payoff bound, with the same unconditional fresh-coordinate averaging. -/
theorem excess_bound (w : WeightedRow.Weights I)
    (R : Finset D) (fixed : D → Option I) (table : Ω → D → Option I)
    (hknown : ∀ ω a, a ∈ R → table ω a = fixed a)
    (hfresh : ∀ a, a ∉ R → ∀ i,
      uniformMean (fun ω => if table ω a = some i then 1 else 0) = w.p i)
    (e : I → ℝ) (he : ∀ i, 0 ≤ e i) (Good : Ω → Prop)
    (payoff : Ω → ℝ) (F emax δ : ℝ) (hF : 0 ≤ F) (hemax : 0 ≤ emax)
    (hkernel : ∀ ω, Good ω → payoff ω ≤ F * referencePayoff R table w.p w.g e e ω)
    (hmax : ∀ ω, payoff ω ≤ emax)
    (hbad : uniformMean (fun ω => if Good ω then 0 else 1) ≤ δ) :
    uniformMean payoff ≤ F * ((1-(R.card : ℝ)/Fintype.card D) * (∑ i, w.g i * e i) +
      (∑ i, (rowCount R fixed i : ℝ) * (w.g i/w.p i * e i)) / Fintype.card D) + emax * δ := by
  have h := joint_good_bound Good payoff _ F emax δ hF hemax
    (referencePayoff_nonneg R table w.p w.g e e w.p_pos w.g_nonneg he he)
    hkernel hmax hbad
  rw [referencePayoff_mean R fixed table w.p w.g e e w.p_pos hknown hfresh] at h
  exact h

end WeightedCompletion
#print axioms WeightedCompletion.replay_reference_mean
#print axioms WeightedCompletion.replay_bound
#print axioms WeightedCompletion.excess_bound
