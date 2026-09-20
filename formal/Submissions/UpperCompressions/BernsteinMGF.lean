import Mathlib

/-! One-step Bernstein exponential moments from explicit positive expectation.
This file does not assert a stochastic-process concentration or OTS theorem. -/

noncomputable section
namespace WeightedMGF

open scoped BigOperators

/-- The exponential tail after degree one is dominated by a geometric series
with ratio x/3. -/
theorem factorial_geometric (n : ℕ) : 2 * 3^n ≤ (n+2).factorial := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [show n+1+2 = (n+2)+1 by omega, Nat.factorial_succ, pow_succ]
    calc
      2*(3^n*3) = 3*(2*3^n) := by ring
      _ ≤ (n+2+1)*(n+2).factorial := Nat.mul_le_mul (by omega) ih

/-- Scalar Bernstein remainder bound, including negative increments. -/
theorem exp_bernstein (x b : ℝ) (hb : 0 ≤ b) (hb3 : b < 3)
    (hxb : |x| ≤ b) :
    Real.exp x ≤ 1+x+x^2/(2*(1-b/3)) := by
  have hf := Real.summable_pow_div_factorial x
  have htail : Summable (fun n : ℕ => x^(n+2)/((n+2).factorial : ℝ)) :=
    (summable_nat_add_iff 2).2 hf
  have hgeo : HasSum (fun n : ℕ => (b/3)^n) (1-b/3)⁻¹ :=
    hasSum_geometric_of_lt_one (by positivity) (by linarith)
  have hterm (n : ℕ) : x^(n+2)/((n+2).factorial : ℝ) ≤ (x^2/2)*(b/3)^n := by
    have hxp : x^n ≤ b^n :=
      (le_abs_self _).trans ((abs_pow x n).le.trans (pow_le_pow_left₀ (abs_nonneg _) hxb n))
    have hnum : x^(n+2) ≤ x^2*b^n := by
      have hp := mul_le_mul_of_nonneg_right hxp (sq_nonneg x)
      simpa only [pow_add, mul_comm] using hp
    have hfact : (2:ℝ)*3^n ≤ (n+2).factorial := by exact_mod_cast factorial_geometric n
    have hd : (0:ℝ) < 2*3^n := by positivity
    calc
      x^(n+2)/((n+2).factorial : ℝ) ≤ (x^2*b^n)/((n+2).factorial : ℝ) :=
        div_le_div_of_nonneg_right hnum (by positivity)
      _ ≤ (x^2*b^n)/(2*3^n) :=
        div_le_div_of_nonneg_left (by positivity) hd hfact
      _ = (x^2/2)*(b/3)^n := by rw [div_pow]; ring
  have ht := htail.tsum_le_tsum hterm (hgeo.summable.mul_left (x^2/2))
  rw [tsum_mul_left, hgeo.tsum_eq] at ht
  have hid : Real.exp x = 1+x+∑' n : ℕ, x^(n+2)/((n+2).factorial : ℝ) := by
    rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
    have hp := hf.sum_add_tsum_nat_add 2
    simpa [Finset.sum_range_succ] using hp.symm
  rw [hid]
  have heq : (x^2/2)*(1-b/3)⁻¹ = x^2/(2*(1-b/3)) := by
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  rw [heq] at ht
  linarith

variable {Ω : Type*}

@[simp] theorem expect_mul (E : (Ω → ℝ) →ₗ[ℝ] ℝ) (a : ℝ) (f : Ω → ℝ) :
    E (fun ω => a*f ω) = a*E f := by
  change E (a • f) = a • E f
  exact E.map_smul a f

@[simp] theorem expect_add (E : (Ω → ℝ) →ₗ[ℝ] ℝ) (f g : Ω → ℝ) :
    E (fun ω => f ω+g ω) = E f+E g := E.map_add f g

@[simp] theorem expect_const (E : (Ω → ℝ) →ₗ[ℝ] ℝ)
    (hnorm : E (fun _ => 1) = 1) (a : ℝ) : E (fun _ => a) = a := by
  have hx := expect_mul E a (fun _ => 1)
  simpa [hnorm] using hx

/-- Exact Bernstein one-step MGF, under explicit zero-mean, second-moment,
and bounded-increment hypotheses. -/
theorem centered_mgf
    (E : (Ω → ℝ) →ₗ[ℝ] ℝ)
    (hmono : ∀ f g, (∀ ω, f ω ≤ g ω) → E f ≤ E g)
    (hnorm : E (fun _ => 1) = 1)
    (X : Ω → ℝ) (θ J v : ℝ)
    (hθ : 0 ≤ θ) (hJ : 0 ≤ J) (hθJ : θ*J < 3)
    (hbound : ∀ ω, |X ω| ≤ J)
    (hmean : E X = 0) (hsecond : E (fun ω => (X ω)^2) ≤ v) :
    E (fun ω => Real.exp (θ*X ω)) ≤
      Real.exp (θ^2*v/(2*(1-θ*J/3))) := by
  have hden : 0 < 2*(1-θ*J/3) := by linarith
  have hpoint (ω : Ω) : Real.exp (θ*X ω) ≤
      1+θ*X ω+(θ^2/(2*(1-θ*J/3)))*(X ω)^2 := by
    have hb : |θ*X ω| ≤ θ*J := by
      rw [abs_mul, abs_of_nonneg hθ]
      exact mul_le_mul_of_nonneg_left (hbound ω) hθ
    have hx := exp_bernstein (θ*X ω) (θ*J) (mul_nonneg hθ hJ) hθJ hb
    convert hx using 1 <;> ring
  have havg := hmono _ _ hpoint
  simp only [expect_add, expect_const E hnorm, expect_mul, hmean, mul_zero, add_zero] at havg
  have hvariance := mul_le_mul_of_nonneg_left hsecond
    (show 0 ≤ θ^2/(2*(1-θ*J/3)) by positivity)
  have hlinear : E (fun ω => Real.exp (θ*X ω)) ≤ 1+θ^2*v/(2*(1-θ*J/3)) := by
    calc
      E (fun ω => Real.exp (θ*X ω)) ≤ 1+(θ^2/(2*(1-θ*J/3)))*v := by linarith
      _ = _ := by ring
  exact hlinear.trans (by simpa only [add_comm] using Real.add_one_le_exp (θ^2*v/(2*(1-θ*J/3))))

@[simp] theorem expect_sub (E : (Ω → ℝ) →ₗ[ℝ] ℝ) (f g : Ω → ℝ) :
    E (fun ω => f ω-g ω) = E f-E g := E.map_sub f g

/-- The bounded nonnegative increment form used by the clipped-row hazard.
The mean and variance bounds follow from 0 ≤ U ≤ J; they are not additional
unverified probabilistic hypotheses. -/
theorem nonnegative_centered_mgf
    (E : (Ω → ℝ) →ₗ[ℝ] ℝ)
    (hmono : ∀ f g, (∀ ω, f ω ≤ g ω) → E f ≤ E g)
    (hnorm : E (fun _ => 1) = 1)
    (U : Ω → ℝ) (θ J : ℝ)
    (hθ : 0 ≤ θ) (hJ : 0 ≤ J) (hθJ : θ*J < 3)
    (hU0 : ∀ ω, 0 ≤ U ω) (hUJ : ∀ ω, U ω ≤ J) :
    E (fun ω => Real.exp (θ*(U ω-E U))) ≤
      Real.exp (θ^2*(J*E U)/(2*(1-θ*J/3))) := by
  have hμ0 : 0 ≤ E U := by
    have hx := hmono (fun _ => 0) U hU0
    simpa only [expect_const E hnorm] using hx
  have hμJ : E U ≤ J := by
    have hx := hmono U (fun _ => J) hUJ
    simpa only [expect_const E hnorm] using hx
  have hbound (ω : Ω) : |U ω-E U| ≤ J := by
    rw [abs_le]
    constructor <;> linarith [hU0 ω, hUJ ω]
  have hmean : E (fun ω => U ω-E U) = 0 := by
    rw [expect_sub, expect_const E hnorm, sub_self]
  have hsqpt (ω : Ω) : (U ω)^2 ≤ J*U ω := by
    nlinarith [hU0 ω, hUJ ω]
  have hsq := hmono _ _ hsqpt
  rw [expect_mul] at hsq
  have hid : E (fun ω => (U ω-E U)^2) =
      E (fun ω => (U ω)^2)+(-2*E U)*E U+(E U)^2 := by
    have hf : (fun ω => (U ω-E U)^2) =
        (fun ω => (U ω)^2+(-2*E U)*U ω+(E U)^2) := by funext ω; ring
    rw [hf, expect_add, expect_add, expect_mul, expect_const E hnorm]
  have hvariance : E (fun ω => (U ω-E U)^2) ≤ J*E U := by
    rw [hid]
    nlinarith [sq_nonneg (E U)]
  exact centered_mgf E hmono hnorm (fun ω => U ω-E U) θ J (J*E U)
    hθ hJ hθJ hbound hmean hvariance

/-- Exponentially compensated one-step expectation. This is the local
supermartingale inequality; chaining conditional kernels is a separate step. -/
theorem compensated_mgf
    (E : (Ω → ℝ) →ₗ[ℝ] ℝ)
    (hmono : ∀ f g, (∀ ω, f ω ≤ g ω) → E f ≤ E g)
    (hnorm : E (fun _ => 1) = 1)
    (X : Ω → ℝ) (θ J v : ℝ)
    (hθ : 0 ≤ θ) (hJ : 0 ≤ J) (hθJ : θ*J < 3)
    (hbound : ∀ ω, |X ω| ≤ J)
    (hmean : E X = 0) (hsecond : E (fun ω => (X ω)^2) ≤ v) :
    E (fun ω => Real.exp (θ*X ω-θ^2*v/(2*(1-θ*J/3)))) ≤ 1 := by
  let b := θ^2*v/(2*(1-θ*J/3))
  have hx := centered_mgf E hmono hnorm X θ J v hθ hJ hθJ hbound hmean hsecond
  have hm := mul_le_mul_of_nonneg_left hx (Real.exp_nonneg (-b))
  have hf : (fun ω => Real.exp (θ*X ω-b)) =
      (fun ω => Real.exp (-b)*Real.exp (θ*X ω)) := by
    funext ω
    rw [sub_eq_add_neg, Real.exp_add, mul_comm]
  change E (fun ω => Real.exp (θ*X ω-b)) ≤ 1
  rw [hf, expect_mul]
  calc
    Real.exp (-b)*E (fun ω => Real.exp (θ*X ω)) ≤ Real.exp (-b)*Real.exp b := hm
    _ = 1 := by rw [← Real.exp_add]; simp

#print axioms factorial_geometric
#print axioms exp_bernstein
#print axioms centered_mgf
#print axioms nonnegative_centered_mgf
#print axioms compensated_mgf

end WeightedMGF
