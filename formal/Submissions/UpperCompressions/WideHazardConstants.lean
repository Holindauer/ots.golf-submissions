import Submissions.UpperCompressions.WeightedBudgetClosure
import Submissions.UpperCompressions.RowConcentrationConstants

/-! Numerical closure for the predictable large-budget hazard variance. -/
noncomputable section
namespace WeightedHazardConstants
open WeightedReference WeightedConstants

def d : ℝ := (L:ℝ)*kappa/2+2*(L:ℝ)/(2:ℝ)^86

theorem d_pos : 0<d := by norm_num [d,L,kappa]

theorem large_exponent (B : ℝ) (hB : (2:ℝ)^86/10 ≤ B) :
    let a := (7:ℝ)/100*kappa*B
    let v := (182:ℝ)/100*d*kappa*B
    (2048:ℝ) ≤ a^2/(2*(v+d*a/3)) := by
  dsimp only
  have hBpos : 0<B := lt_of_lt_of_le (by norm_num) hB
  have hden : 0<2*((182:ℝ)/100*d*kappa*B+d*((7:ℝ)/100*kappa*B)/3) := by
    have := d_pos
    have : 0<kappa := by norm_num [kappa]
    positivity
  apply (le_div_iff₀ hden).2
  have hlinear : 2048*(2*((182:ℝ)/100*d*kappa+d*((7:ℝ)/100*kappa)/3)) ≤
      ((7:ℝ)/100*kappa)^2*B := by
    norm_num [d,L,kappa] at *
    linarith
  have h := mul_le_mul_of_nonneg_right hlinear hBpos.le
  nlinarith

theorem exp_neg_2048 : Real.exp (-(2048:ℝ)) ≤ ((2:ℝ)^2048)⁻¹ := by
  have he : (2:ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1:ℝ)]
  have hp : (2:ℝ)^2048 ≤ (Real.exp 1)^2048 := pow_le_pow_left₀ (by norm_num) he 2048
  rw [← Real.exp_nat_mul,mul_one] at hp
  rw [Real.exp_neg]
  exact (inv_le_inv₀ (Real.exp_pos _) (by positivity)).2 hp

theorem message_union_margin :
    (2:ℝ)^256*Real.exp (-(2048:ℝ)) ≤ ((2:ℝ)^1792)⁻¹ := by
  have h := mul_le_mul_of_nonneg_left exp_neg_2048 (show (0:ℝ)≤2^256 by positivity)
  apply h.trans_eq
  rw [show (2048:ℕ)=256+1792 from rfl,pow_add]
  field_simp

/-- Both actual adaptive-state and hazard-union exceptions remain negligible. -/
theorem all_exception_margin (B : ℝ) (hB : 995 ≤ B) (hcap : B ≤ (2:ℝ)^127) :
    ((2:ℝ)^512)⁻¹+((2:ℝ)^1792)⁻¹+(1+B)*((2:ℝ)^761)⁻¹ ≤ kappa*B/1000 := by
  have hinv (n k : ℕ) (h : k ≤ n) : ((2:ℝ)^n)⁻¹ ≤ ((2:ℝ)^k)⁻¹ := by
    apply (inv_le_inv₀ (by positivity) (by positivity)).mpr
    exact pow_le_pow_right₀ (by norm_num) h
  have h1 := hinv 512 256 (by decide)
  have h2 := hinv 1792 256 (by decide)
  have h3 := hinv 761 384 (by decide)
  have hp : 0≤1+B := by linarith
  have hb : 1+B ≤ (2:ℝ)^128 := by linarith
  have hterm := mul_le_mul h3 hb hp (show (0:ℝ)≤((2:ℝ)^384)⁻¹ by positivity)
  have he : ((2:ℝ)^384)⁻¹*(2:ℝ)^128=((2:ℝ)^256)⁻¹ := by
    rw [show (384:ℕ)=256+128 from rfl,pow_add]
    field_simp
  rw [he,mul_comm _ (1+B)] at hterm
  have hsmall : 3*((2:ℝ)^256)⁻¹ ≤ kappa*995/1000 := by norm_num [kappa]
  have hfinal := mul_le_mul_of_nonneg_left hB (show 0≤kappa/1000 by norm_num [kappa])
  linarith


#print axioms large_exponent
#print axioms message_union_margin
#print axioms all_exception_margin
end WeightedHazardConstants
