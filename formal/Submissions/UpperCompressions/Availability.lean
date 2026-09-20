import Mathlib
namespace WeightedAvailability
attribute [local irreducible] Nat.choose

lemma quartic_binomial_lower (x : ℝ) (hx : 0 ≤ x) (n : ℕ) (hn : 4 ≤ n) :
    1 + (n:ℝ)*x + (n.choose 2:ℝ)*x^2 + (n.choose 3:ℝ)*x^3 +
      (n.choose 4:ℝ)*x^4 ≤ (1+x)^n := by
  have hs : Finset.range 5 ⊆ Finset.range (n+1) := Finset.range_mono (by omega)
  have h := Finset.sum_le_sum_of_subset_of_nonneg (f := fun i =>
    x^i*(1:ℝ)^(n-i)*(n.choose i:ℝ)) hs (by intro i hi hni; positivity)
  rw [← add_pow] at h
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, one_pow,
    mul_one, Nat.choose_zero_right, Nat.choose_one_right, Nat.cast_one,
    zero_add, pow_one] at h
  simpa only [add_comm, add_left_comm, add_assoc, mul_comm] using h

lemma linear_binomial_lower (x : ℝ) (hx : 0 ≤ x) (n : ℕ) (hn : 1 ≤ n) :
    1+(n:ℝ)*x ≤ (1+x)^n := by
  have hs : Finset.range 2 ⊆ Finset.range (n+1) := Finset.range_mono (by omega)
  have h := Finset.sum_le_sum_of_subset_of_nonneg (f := fun i =>
    x^i*(1:ℝ)^(n-i)*(n.choose i:ℝ)) hs (by intro i hi hni; positivity)
  rw [← add_pow] at h
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, one_pow,
    mul_one, Nat.choose_zero_right, Nat.choose_one_right, Nat.cast_one,
    zero_add, pow_one] at h
  simpa only [add_comm, mul_comm] using h

lemma choose_two : Nat.choose 8192 2 = 33550336 := by rw [Nat.choose_two_right]
lemma choose_three : Nat.choose 8192 3 = 91592417280 := by
  have h := Nat.choose_succ_right_eq 8192 2
  norm_num [choose_two] at h
  omega
lemma choose_four : Nat.choose 8192 4 = 187512576276480 := by
  have h := Nat.choose_succ_right_eq 8192 3
  norm_num [choose_three] at h
  omega

lemma reciprocal_block : (256:ℝ)/127 ≤ (1+8999/104848601)^8192 := by
  have h := quartic_binomial_lower (8999/104848601) (by norm_num) 8192 (by norm_num)
  rw [choose_two, choose_three, choose_four] at h
  have hc : (256:ℝ)/127 ≤ 1+(8192:ℝ)*(8999/104848601)+
      33550336*(8999/104848601)^2+91592417280*(8999/104848601)^3+
      187512576276480*(8999/104848601)^4 := by norm_num
  exact hc.trans h

lemma block : (1-(8999:ℝ)/104857600)^8192 ≤ 127/256 := by
  have hn : 0 ≤ (1-(8999:ℝ)/104857600)^8192 := by positivity
  have hp : (1-(8999:ℝ)/104857600)^8192*(1+8999/104848601)^8192=1 := by
    have hb : (1-(8999:ℝ)/104857600)*(1+8999/104848601)=1 := by norm_num
    rw [← mul_pow, hb, one_pow]
  have h := mul_le_mul_of_nonneg_left reciprocal_block hn
  rw [hp] at h
  have hv := (le_div_iff₀ (by norm_num : (0:ℝ) < 256/127)).2 h
  simpa only [one_div_div] using hv

lemma extra_half : ((127:ℝ)/128)^128 ≤ 1/2 := by
  have h := linear_binomial_lower ((1:ℝ)/127) (by norm_num) 128 (by norm_num)
  have hlo : (2:ℝ) ≤ (1+1/127)^128 := by linarith
  have hn : 0 ≤ ((127:ℝ)/128)^128 := by positivity
  have hp : ((127:ℝ)/128)^128*(1+1/127)^128=1 := by
    have hb : ((127:ℝ)/128)*(1+1/127)=1 := by norm_num
    rw [← mul_pow, hb, one_pow]
  have hmul := mul_le_mul_of_nonneg_left hlo hn
  rw [hp] at hmul
  linarith

/-- Complete-row empirical acceptance slack leaves half the failure budget.
This is arithmetic, not yet the actual replacement signer's availability proof. -/
theorem empirical_failure :
    (1-(8999:ℝ)/104857600)^(2^20:ℕ) ≤ ((2:ℝ)^129)⁻¹ := by
  have he : (2^20:ℕ)=8192*128 := by norm_num
  rw [he, pow_mul]
  calc
    ((1-(8999:ℝ)/104857600)^8192)^128 ≤ ((127:ℝ)/256)^128 :=
      pow_le_pow_left₀ (by positivity) block 128
    _ = ((1:ℝ)/2)^128*((127:ℝ)/128)^128 := by rw [← mul_pow]; norm_num
    _ ≤ ((1:ℝ)/2)^128*(1/2) := mul_le_mul_of_nonneg_left extra_half (by positivity)
    _ = ((2:ℝ)^129)⁻¹ := by norm_num

#print axioms empirical_failure
end WeightedAvailability
