import Mathlib

/-! Algebraic kernel for the iid-nonce, first-minimum weighted signer.
This module proves polynomial identities and bounds only. The finite random-sampling
law and the full OTS security argument remain separate obligations. -/

namespace WeightedReplacement

/-- The divided-difference polynomial, with no division or unequal-endpoint hypothesis. -/
def kernel (L : ℕ) (A B : ℝ) : ℝ :=
  ∑ k ∈ Finset.range L, A^k * B^(L-1-k)

@[simp] theorem kernel_zero (A B : ℝ) : kernel 0 A B = 0 := by simp [kernel]
@[simp] theorem kernel_one (A B : ℝ) : kernel 1 A B = 1 := by simp [kernel]

theorem kernel_nonneg (L : ℕ) {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) :
    0 ≤ kernel L A B := by
  unfold kernel
  exact Finset.sum_nonneg fun k hk => mul_nonneg (pow_nonneg hA _) (pow_nonneg hB _)

/-- Monotonicity in both survival probabilities, including equal endpoints. -/
theorem kernel_mono (L : ℕ) {A B A' B' : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hAA : A ≤ A') (hBB : B ≤ B') : kernel L A B ≤ kernel L A' B' := by
  unfold kernel
  apply Finset.sum_le_sum
  intro k hk
  exact mul_le_mul (pow_le_pow_left₀ hA hAA k)
    (pow_le_pow_left₀ hB hBB (L-1-k)) (pow_nonneg hB _) (pow_nonneg (hA.trans hAA) _)

/-- Every term has degree L-1; the identity also covers L=0. -/
theorem kernel_scale (L : ℕ) (c A B : ℝ) :
    kernel L (c*A) (c*B) = c^(L-1)*kernel L A B := by
  unfold kernel
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hk' : k < L := Finset.mem_range.mp hk
  have he : k+(L-1-k)=L-1 := by omega
  rw [mul_pow, mul_pow]
  calc
    (c^k*A^k)*(c^(L-1-k)*B^(L-1-k))
        = (c^k*c^(L-1-k))*(A^k*B^(L-1-k)) := by ring
    _ = c^(L-1)*(A^k*B^(L-1-k)) := by rw [← pow_add, he]

/-- Difference of powers with no positivity or strictness assumptions. -/
theorem sub_mul_kernel (L : ℕ) (A B : ℝ) :
    (A-B)*kernel L A B = A^L-B^L := by
  exact (Commute.all A B).mul_geom_sum₂ L

/-- Reversing time in the first-minimum position sum leaves the kernel unchanged. -/
theorem kernel_symm (L : ℕ) (A B : ℝ) : kernel L A B = kernel L B A := by
  exact geom_sum₂_comm A B L

/-- This is the sum of the first-minimum position probabilities after removing 1/N.
Earlier positions must have tier strictly above the winner, later positions may tie. -/
theorem first_minimum_sum (L : ℕ) (A B : ℝ) :
    (∑ t ∈ Finset.range L, B^t*A^(L-1-t)) = kernel L A B :=
  kernel_symm L B A

/-- Tier winning mass is its tier probability times the common kernel. -/
theorem tier_mass (L : ℕ) (A B Q : ℝ) (hQ : Q=A-B) :
    Q*kernel L A B = A^L-B^L := by rw [hQ]; exact sub_mul_kernel L A B

/-- Compare arbitrary nonnegative empirical endpoints to scaled reference endpoints. -/
theorem kernel_le_scaled (L : ℕ) {Ah Bh A B c : ℝ}
    (hAh : 0 ≤ Ah) (hBh : 0 ≤ Bh) (hA : Ah ≤ c*A) (hB : Bh ≤ c*B) :
    kernel L Ah Bh ≤ c^(L-1)*kernel L A B := by
  exact (kernel_mono L hAh hBh hA hB).trans_eq (kernel_scale L c A B)

/-- An additive prefix-deficit bound becomes one common multiplicative envelope.
Here z is a positive lower bound on both reference survival endpoints. -/
theorem kernel_additive_envelope (L : ℕ) {Ah Bh A B z delta : ℝ}
    (hAh : 0 ≤ Ah) (hBh : 0 ≤ Bh) (hz : 0 < z) (hd : 0 ≤ delta)
    (hzA : z ≤ A) (hzB : z ≤ B) (hA : Ah ≤ A+delta) (hB : Bh ≤ B+delta) :
    kernel L Ah Bh ≤ (1+delta/z)^(L-1)*kernel L A B := by
  have hdz : 0 ≤ delta/z := div_nonneg hd hz.le
  have hAz : delta ≤ (delta/z)*A := by
    have hh := mul_le_mul_of_nonneg_left hzA hdz
    have he : (delta/z)*z=delta := div_mul_cancel₀ delta hz.ne'
    linarith
  have hBz : delta ≤ (delta/z)*B := by
    have hh := mul_le_mul_of_nonneg_left hzB hdz
    have he : (delta/z)*z=delta := div_mul_cancel₀ delta hz.ne'
    linarith
  apply kernel_le_scaled L hAh hBh
  · nlinarith
  · nlinarith

/-- Nonempty-tier division recovers the usual difference quotient exactly. -/
theorem kernel_eq_div (L : ℕ) {A B : ℝ} (hAB : A ≠ B) :
    kernel L A B = (A^L-B^L)/(A-B) := by
  apply (eq_div_iff (sub_ne_zero.mpr hAB)).2
  rw [mul_comm]
  exact sub_mul_kernel L A B

#print axioms kernel_mono
#print axioms kernel_scale
#print axioms sub_mul_kernel
#print axioms kernel_symm
#print axioms first_minimum_sum
#print axioms kernel_additive_envelope
#print axioms kernel_eq_div

end WeightedReplacement
