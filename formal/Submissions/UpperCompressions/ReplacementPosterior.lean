import Submissions.UpperCompressions.ReplacementKernel

/-! One-coordinate Bayes bound for a signed first-minimum nonce. This module does
not condition on any global Good event. The prior weights may be arbitrary
nonnegative finite weights; the bound is invariant under their normalization.
Connecting fixed-coordinate tables to an adaptive oracle filtration is separate. -/

namespace WeightedReplacement

open scoped Classical

noncomputable def weightedMass {α : Type*} [Fintype α]
    (weight : α → ℝ) (event : α → Prop) : ℝ :=
  ∑ a, if event a then weight a else 0

theorem weightedMass_nonneg {α : Type*} [Fintype α]
    (weight : α → ℝ) (event : α → Prop) (hw : ∀ a, 0 ≤ weight a) :
    0 ≤ weightedMass weight event := by
  apply Finset.sum_nonneg
  intro a ha
  split_ifs <;> simp [hw]

/-- A constant target likelihood and a no-smaller likelihood throughout a
survival event bound the posterior by prior target mass / prior survival mass. -/
theorem finite_bayes_likelihood_bound {α : Type*} [Fintype α]
    (weight likelihood : α → ℝ) (target survival : α → Prop) (c : ℝ)
    (hw : ∀ a, 0 ≤ weight a) (hl : ∀ a, 0 ≤ likelihood a)
    (htarget : ∀ a, target a → likelihood a = c)
    (hsurvival : ∀ a, survival a → c ≤ likelihood a)
    (hmass : 0 < weightedMass weight survival)
    (hden : 0 < ∑ a, weight a * likelihood a) :
    (∑ a, if target a then weight a * likelihood a else 0) /
        (∑ a, weight a * likelihood a) ≤
      weightedMass weight target / weightedMass weight survival := by
  have hnum : (∑ a, if target a then weight a * likelihood a else 0) =
      weightedMass weight target * c := by
    rw [weightedMass, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro a ha
    by_cases ht : target a
    · simp [ht, htarget a ht]
    · simp [ht]
  have hlow : weightedMass weight survival * c ≤ ∑ a, weight a * likelihood a := by
    rw [weightedMass, Finset.sum_mul]
    apply Finset.sum_le_sum
    intro a ha
    by_cases hs : survival a
    · simp only [if_pos hs]
      exact mul_le_mul_of_nonneg_left (hsurvival a hs) (hw a)
    · simp only [if_neg hs, zero_mul]
      exact mul_nonneg (hw a) (hl a)
  rw [hnum]
  apply (div_le_div_iff₀ hden hmass).2
  calc
    (weightedMass weight target * c) * weightedMass weight survival =
        weightedMass weight target * (weightedMass weight survival * c) := by ring
    _ ≤ weightedMass weight target * (∑ a, weight a * likelihood a) :=
      mul_le_mul_of_nonneg_left hlow (weightedMass_nonneg weight target hw)

/-- The unknown coordinate contributes δ to A when weakly worse and to B when
strictly worse. A and B contain only the other fixed nonce coordinates. -/
noncomputable def coordinateLikelihood {α : Type*} (L : ℕ) (A B δ N : ℝ)
    (weak strict : α → Prop) (a : α) : ℝ :=
  kernel L (A + if weak a then δ else 0) (B + if strict a then δ else 0) / N

theorem coordinateLikelihood_nonneg {α : Type*} (L : ℕ) (A B δ N : ℝ)
    (weak strict : α → Prop) (hA : 0 ≤ A) (hB : 0 ≤ B) (hδ : 0 ≤ δ)
    (hN : 0 ≤ N) (a : α) :
    0 ≤ coordinateLikelihood L A B δ N weak strict a := by
  unfold coordinateLikelihood
  apply div_nonneg _ hN
  apply kernel_nonneg
  · split_ifs <;> linarith
  · split_ifs <;> linarith

theorem coordinateLikelihood_same {α : Type*} (L : ℕ) (A B δ N : ℝ)
    (weak strict : α → Prop) (a : α) (hw : weak a) (hs : ¬ strict a) :
    coordinateLikelihood L A B δ N weak strict a = kernel L (A+δ) B / N := by
  simp [coordinateLikelihood, hw, hs]

/-- Changing the unknown nonce from the signed tier to a higher tier or rejection
cannot reduce the signed target's likelihood. Equal-tier answers have equal likelihood. -/
theorem coordinateLikelihood_survival {α : Type*} (L : ℕ) (A B δ N : ℝ)
    (weak strict : α → Prop) (hA : 0 ≤ A) (hB : 0 ≤ B) (hδ : 0 ≤ δ)
    (hN : 0 ≤ N) (a : α) (hw : weak a) :
    kernel L (A+δ) B / N ≤ coordinateLikelihood L A B δ N weak strict a := by
  unfold coordinateLikelihood
  rw [if_pos hw]
  apply div_le_div_of_nonneg_right _ hN
  apply kernel_mono L (add_nonneg hA hδ) hB le_rfl
  split_ifs <;> linarith

/-- Bayes posterior bound for one unknown coordinate, pointwise in all other
fixed table entries. The target event is any particular class in the signed tier.
There is no conditioning on a concentration/Good event. -/
theorem coordinate_posterior_bound {α : Type*} [Fintype α]
    (L : ℕ) (A B δ N : ℝ) (weight : α → ℝ) (target weak strict : α → Prop)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hδ : 0 ≤ δ) (hN : 0 ≤ N)
    (hw : ∀ a, 0 ≤ weight a) (ht : ∀ a, target a → weak a ∧ ¬ strict a)
    (hmass : 0 < weightedMass weight weak)
    (hden : 0 < ∑ a, weight a * coordinateLikelihood L A B δ N weak strict a) :
    (∑ a, if target a then
        weight a * coordinateLikelihood L A B δ N weak strict a else 0) /
      (∑ a, weight a * coordinateLikelihood L A B δ N weak strict a) ≤
        weightedMass weight target / weightedMass weight weak := by
  apply finite_bayes_likelihood_bound weight _ target weak (kernel L (A+δ) B / N)
    hw (coordinateLikelihood_nonneg L A B δ N weak strict hA hB hδ hN)
  · intro a ha
    exact coordinateLikelihood_same L A B δ N weak strict a (ht a ha).1 (ht a ha).2
  · exact coordinateLikelihood_survival L A B δ N weak strict hA hB hδ hN
  · exact hmass
  · exact hden

#print axioms finite_bayes_likelihood_bound
#print axioms coordinateLikelihood_survival
#print axioms coordinate_posterior_bound

end WeightedReplacement
