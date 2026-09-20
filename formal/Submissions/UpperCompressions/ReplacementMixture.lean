import Submissions.UpperCompressions.ReplacementCoordinate

/-! The posterior bound survives arbitrary coordinate-independent evidence and
finite mixtures over all other coordinates. Individual mixture components may
have zero signing likelihood; only the aggregate conditioning event must have
positive probability. No Good-event conditioning is used. -/

namespace WeightedReplacement

open scoped Classical

noncomputable def mixedLikelihood {Z Ω : Type} [Fintype Z]
    (latent evidence : Z → ℝ) (likelihood : Z → Ω → ℝ) (y : Ω) : ℝ :=
  ∑ z, (latent z * evidence z) * likelihood z y

/-- A Bayes likelihood comparison is stable under arbitrary nonnegative evidence
independent of the unknown coordinate, and under mixing all other coordinates.
Zero-likelihood components need no separate conditioning or division. -/
theorem finite_bayes_evidence_mixture_bound {Z Ω : Type} [Fintype Z] [Fintype Ω]
    (weight : Ω → ℝ) (latent evidence : Z → ℝ) (likelihood : Z → Ω → ℝ)
    (target survival : Ω → Prop) (c : Z → ℝ)
    (hw : ∀ y, 0 ≤ weight y) (hz : ∀ z, 0 ≤ latent z) (he : ∀ z, 0 ≤ evidence z)
    (hl : ∀ z y, 0 ≤ likelihood z y)
    (ht : ∀ z y, target y → likelihood z y = c z)
    (hs : ∀ z y, survival y → c z ≤ likelihood z y)
    (hmass : 0 < weightedMass weight survival)
    (hden : 0 < ∑ y, weight y * mixedLikelihood latent evidence likelihood y) :
    (∑ y, if target y then weight y * mixedLikelihood latent evidence likelihood y else 0) /
      (∑ y, weight y * mixedLikelihood latent evidence likelihood y) ≤
      weightedMass weight target / weightedMass weight survival := by
  apply finite_bayes_likelihood_bound weight (mixedLikelihood latent evidence likelihood)
    target survival (∑ z, (latent z * evidence z) * c z) hw
  · intro y
    exact Finset.sum_nonneg fun z _ => mul_nonneg (mul_nonneg (hz z) (he z)) (hl z y)
  · intro y hy
    apply Finset.sum_congr rfl
    intro z hz'
    rw [ht z y hy]
  · intro y hy
    apply Finset.sum_le_sum
    intro z hz'
    exact mul_le_mul_of_nonneg_left (hs z y hy) (mul_nonneg (hz z) (he z))
  · exact hmass
  · exact hden

/-- Kernel specialization: other-coordinate endpoints and evidence may vary with
the latent state, while the unknown answer retains the same prior. -/
theorem coordinate_evidence_mixture_bound {Z Ω : Type} [Fintype Z] [Fintype Ω]
    (L : ℕ) (A B : Z → ℝ) (δ N : ℝ) (weight : Ω → ℝ)
    (latent evidence : Z → ℝ) (target weak strict : Ω → Prop)
    (hA : ∀ z, 0 ≤ A z) (hB : ∀ z, 0 ≤ B z) (hδ : 0 ≤ δ) (hN : 0 ≤ N)
    (hw : ∀ y, 0 ≤ weight y) (hz : ∀ z, 0 ≤ latent z) (he : ∀ z, 0 ≤ evidence z)
    (ht : ∀ y, target y → weak y ∧ ¬ strict y)
    (hmass : 0 < weightedMass weight weak)
    (hden : 0 < ∑ y, weight y * mixedLikelihood latent evidence
      (fun z => coordinateLikelihood L (A z) (B z) δ N weak strict) y) :
    (∑ y, if target y then weight y * mixedLikelihood latent evidence
        (fun z => coordinateLikelihood L (A z) (B z) δ N weak strict) y else 0) /
      (∑ y, weight y * mixedLikelihood latent evidence
        (fun z => coordinateLikelihood L (A z) (B z) δ N weak strict) y) ≤
      weightedMass weight target / weightedMass weight weak := by
  apply finite_bayes_evidence_mixture_bound weight latent evidence _ target weak
    (fun z => kernel L (A z + δ) (B z) / N) hw hz he
  · intro z
    exact coordinateLikelihood_nonneg L (A z) (B z) δ N weak strict (hA z) (hB z) hδ hN
  · intro z y hy
    exact coordinateLikelihood_same L (A z) (B z) δ N weak strict y (ht y hy).1 (ht y hy).2
  · intro z
    exact coordinateLikelihood_survival L (A z) (B z) δ N weak strict (hA z) (hB z) hδ hN
  · exact hmass
  · exact hden

#print axioms finite_bayes_evidence_mixture_bound
#print axioms coordinate_evidence_mixture_bound

end WeightedReplacement
