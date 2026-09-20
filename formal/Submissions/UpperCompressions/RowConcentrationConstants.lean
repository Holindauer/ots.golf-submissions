import Mathlib
noncomputable section
namespace WeightedEmpirical

/-- The same very conservative variance bound suffices for all row statistics.
Use G=1 for prefix indicators and G=Lκ for weighted row scores. -/
theorem mixed_row_exponent (G : ℝ) (hG : 0 < G) :
    let N : ℝ := 2^86
    let L : ℝ := 2^20
    let a := G*N/(100*L)
    let v := G^2*N
    0 < a ∧ 0 < v ∧ (2^30:ℝ) ≤ a^2/(2*(v+G*a/3)) := by
  dsimp only
  refine ⟨by positivity, by positivity, ?_⟩
  apply (le_div_iff₀ (by positivity)).2
  norm_num
  nlinarith [sq_pos_of_pos hG]

/-- Turn a deliberately loose exponential margin into a binary bound. -/
theorem exp_neg_pow30_le : Real.exp (-(2^30:ℝ)) ≤ ((2:ℝ)^1024)⁻¹ := by
  have he : (2:ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1:ℝ)]
  have hp : (2:ℝ)^1024 ≤ (Real.exp 1)^1024 := pow_le_pow_left₀ (by norm_num) he 1024
  rw [← Real.exp_nat_mul, mul_one] at hp
  have hc : (1024:ℝ) ≤ 2^30 := by norm_num
  have hb := hp.trans (Real.exp_le_exp.mpr hc)
  rw [Real.exp_neg]
  exact (inv_le_inv₀ (Real.exp_pos _) (by positivity)).2 hb

/-- A 256-bit message-row union over 72 prefix tests and two weighted scores,
plus the global-score event, still fits within 2^-512. No time-prefix factor. -/
theorem mixed_row_union_margin :
    (74*(2^256:ℝ)+1)*Real.exp (-(2^30:ℝ)) ≤ ((2:ℝ)^512)⁻¹ := by
  have hm := mul_le_mul_of_nonneg_left exp_neg_pow30_le
    (show 0 ≤ 74*(2^256:ℝ)+1 by positivity)
  have hbase : (75:ℝ) ≤ 2^256 := by norm_num
  have hfactor : 74*(2^256:ℝ)+1 ≤ (2:ℝ)^512 := by
    calc
      74*(2^256:ℝ)+1 ≤ ((2:ℝ)^256)^2 := by nlinarith
      _ = (2:ℝ)^512 := by rw [← pow_mul]
  apply hm.trans
  calc
    (74*(2^256:ℝ)+1)*((2:ℝ)^1024)⁻¹ ≤ (2:ℝ)^512*((2:ℝ)^1024)⁻¹ := by gcongr
    _ = ((2:ℝ)^512)⁻¹ := by
      rw [show (1024:ℕ) = 512+512 from rfl, pow_add]
      field_simp

#print axioms mixed_row_exponent
#print axioms exp_neg_pow30_le
#print axioms mixed_row_union_margin
end WeightedEmpirical
