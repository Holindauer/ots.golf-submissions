import Submissions.UpperCompressions.WeightedMoments
noncomputable section
open scoped Classical BigOperators
namespace WeightedRow.Weights
variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Change the observed score while preserving the actual class distribution. -/
def withScore (w : WeightedRow.Weights ι) (g : ι → ℝ) (hg : ∀ i, 0 ≤ g i) :
    WeightedRow.Weights ι where
  p := w.p
  g := g
  p_pos := w.p_pos
  g_nonneg := hg
  mass_le_one := w.mass_le_one

@[simp] theorem withScore_classMass (w : WeightedRow.Weights ι)
    (g : ι → ℝ) (hg : ∀ i, 0 ≤ g i) (x : Option ι) :
    (w.withScore g hg).classMass x = w.classMass x := by cases x <;> rfl

/-- Prefix-count score. Rejection contributes zero, as in the shared decoder. -/
def prefixWeights (w : WeightedRow.Weights ι) (C : Finset ι) : WeightedRow.Weights ι :=
  w.withScore (fun i => if i ∈ C then 1 else 0) (fun i => by split_ifs <;> norm_num)

theorem prefix_weight_bound (w : WeightedRow.Weights ι) (C : Finset ι) (i : ι) :
    (w.prefixWeights C).g i ≤ 1 := by
  change (if i ∈ C then (1:ℝ) else 0) ≤ 1
  split_ifs <;> norm_num

private theorem indicator_sum (C : Finset ι) (f : ι → ℝ) :
    (∑ i, f i*(if i ∈ C then 1 else 0)) = ∑ i ∈ C, f i := by
  simp only [mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_filter]
  simp

theorem prefix_mean (w : WeightedRow.Weights ι) (C : Finset ι) :
    (w.prefixWeights C).mean = ∑ i ∈ C, w.p i := by
  exact indicator_sum C w.p

theorem prefix_score (w : WeightedRow.Weights ι) (C : Finset ι) (k : ι → ℕ) :
    (w.prefixWeights C).score k = ∑ i ∈ C, (k i:ℝ) := by
  exact indicator_sum C (fun i => (k i:ℝ))

/-- Lower-tail M1 is exactly the empirical accepted-prefix deficit. -/
theorem prefix_deficit (w : WeightedRow.Weights ι) (C : Finset ι) (q : ℕ) (k : ι → ℕ) :
    -(w.prefixWeights C).M1 q k = (∑ i ∈ C, w.p i)*(q:ℝ)-∑ i ∈ C, (k i:ℝ) := by
  rw [M1, prefix_score, prefix_mean]
  ring

#print axioms withScore_classMass
#print axioms prefix_deficit
end WeightedRow.Weights
