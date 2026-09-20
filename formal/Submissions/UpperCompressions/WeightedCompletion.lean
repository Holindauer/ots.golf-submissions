import Submissions.UpperCompressions.WideSecurityData
import Submissions.UpperCompressions.ReplacementConcentration

/-! Averaging a partially exposed row under its original completion law.
Only unconditional fresh-coordinate marginals are used; no Good conditioning. -/
noncomputable section
open scoped BigOperators Classical
namespace WeightedCompletion
open WeightedReplacement
variable {Ω D I : Type*} [Fintype Ω] [Nonempty Ω] [Fintype D] [Nonempty D]
  [Fintype I] [DecidableEq D] [DecidableEq I]

def score (x : Option I) (f : I → ℝ) : ℝ := (x.map f).getD 0

theorem score_expand (x : Option I) (f : I → ℝ) :
    score x f = ∑ i, if x = some i then f i else 0 := by
  cases x with
  | none => simp [score]
  | some i => simp [score, eq_comm]

theorem mean_sum {ι : Type*} (s : Finset ι) (f : ι → Ω → ℝ) :
    uniformMean (fun ω => ∑ i ∈ s, f i ω) = ∑ i ∈ s, uniformMean (f i) := by
  unfold uniformMean
  rw [Finset.sum_comm, Finset.sum_div]

theorem mean_mul (a : ℝ) (f : Ω → ℝ) :
    uniformMean (fun ω => a * f ω) = a * uniformMean f := by
  unfold uniformMean
  rw [← Finset.mul_sum]
  ring

theorem mean_score (x : Ω → Option I) (p f : I → ℝ)
    (hm : ∀ i, uniformMean (fun ω => if x ω = some i then 1 else 0) = p i) :
    uniformMean (fun ω => score (x ω) f) = ∑ i, p i * f i := by
  simp only [score_expand]
  rw [mean_sum]
  apply Finset.sum_congr rfl
  intro i _
  have he : (fun ω => if x ω = some i then f i else 0) =
      fun ω => (if x ω = some i then 1 else 0) * f i := by
    funext ω
    split_ifs <;> simp
  rw [he, uniformMean_mul_const, hm]

def rowCount (R : Finset D) (fixed : D → Option I) (i : I) : ℕ :=
  (R.filter fun a => fixed a = some i).card

theorem known_score (R : Finset D) (fixed : D → Option I) (f : I → ℝ) :
    (∑ a ∈ R, score (fixed a) f) = ∑ i, (rowCount R fixed i : ℝ) * f i := by
  simp only [score_expand]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_filter]
  simp only [rowCount, Finset.sum_const, nsmul_eq_mul]

/-- Keep the good-table indicator joint with the payoff, then discard it only
from a nonnegative reference term. The bad-table tail is charged separately. -/
theorem joint_good_bound (Good : Ω → Prop) (X Y : Ω → ℝ) (F C δ : ℝ)
    (hF : 0 ≤ F) (hC : 0 ≤ C) (hY : ∀ ω, 0 ≤ Y ω)
    (hgood : ∀ ω, Good ω → X ω ≤ F * Y ω)
    (hmax : ∀ ω, X ω ≤ C)
    (hbad : uniformMean (fun ω => if Good ω then 0 else 1) ≤ δ) :
    uniformMean X ≤ F * uniformMean Y + C * δ := by
  have hpoint : ∀ ω, X ω ≤ F * Y ω + C * (if Good ω then 0 else 1) := by
    intro ω
    by_cases hg : Good ω
    · simpa only [if_pos hg, mul_zero, add_zero] using hgood ω hg
    · rw [if_neg hg, mul_one]
      exact (hmax ω).trans (le_add_of_nonneg_left (mul_nonneg hF (hY ω)))
  have h := uniformMean_mono X _ hpoint
  rw [uniformMean_add, mean_mul, mean_mul] at h
  exact h.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left hbad hC))

/-- Exact row expectation: exposed coordinates keep their values, while every
unexposed coordinate has its original one-coordinate marginal. Correlations
between unexposed coordinates are not excluded or conditioned away. -/
theorem completion_score (R : Finset D) (fixed : D → Option I)
    (table : Ω → D → Option I) (p fKnown fFresh : I → ℝ)
    (hknown : ∀ ω a, a ∈ R → table ω a = fixed a)
    (hfresh : ∀ a, a ∉ R → ∀ i,
      uniformMean (fun ω => if table ω a = some i then 1 else 0) = p i) :
    uniformMean (fun ω => ∑ a : D,
      if a ∈ R then score (table ω a) fKnown else score (table ω a) fFresh) =
      (∑ i, (rowCount R fixed i : ℝ) * fKnown i) +
        ((Fintype.card D : ℝ) - R.card) * ∑ i, p i * fFresh i := by
  rw [mean_sum]
  have he : ∀ a : D, uniformMean (fun ω =>
      if a ∈ R then score (table ω a) fKnown else score (table ω a) fFresh) =
      if a ∈ R then score (fixed a) fKnown else ∑ i, p i * fFresh i := by
    intro a
    by_cases ha : a ∈ R
    · simp only [if_pos ha, hknown _ a ha, uniformMean_const]
    · simp only [if_neg ha]
      exact mean_score (fun ω => table ω a) p fFresh (hfresh a ha)
  simp only [he]
  rw [← Finset.sum_add_sum_compl R]
  have hR : (∑ a ∈ R, if a ∈ R then score (fixed a) fKnown else ∑ i, p i * fFresh i) =
      ∑ a ∈ R, score (fixed a) fKnown :=
    Finset.sum_congr rfl fun a ha => if_pos ha
  have hc : (∑ a ∈ Rᶜ, if a ∈ R then score (fixed a) fKnown else ∑ i, p i * fFresh i) =
      ((Fintype.card D : ℝ)-R.card) * ∑ i, p i * fFresh i := by
    have he' : (∑ a ∈ Rᶜ, if a ∈ R then score (fixed a) fKnown else ∑ i, p i * fFresh i) =
        ∑ _a ∈ Rᶜ, ∑ i, p i * fFresh i :=
      Finset.sum_congr rfl fun a ha => if_neg (Finset.mem_compl.mp ha)
    rw [he', Finset.sum_const, nsmul_eq_mul, Finset.card_compl]
    rw [Nat.cast_sub (Finset.card_le_univ R)]
  rw [hR, known_score, hc]

end WeightedCompletion
#print axioms WeightedCompletion.joint_good_bound
#print axioms WeightedCompletion.completion_score
