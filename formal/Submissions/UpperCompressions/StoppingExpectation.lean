import Mathlib

/-! Bounded-stopping expectation algebra for the weighted-index research.
The expectation is an explicitly assumed normalized positive linear functional.
Zero stopped means and the stopped second moment are hypotheses, NOT optional
stopping or oracle-filtration theorems. No signature-security claim is exported. -/

noncomputable section
namespace WeightedStopping

variable {Ω : Type*}

@[simp] theorem expect_mul (E : (Ω → ℝ) →ₗ[ℝ] ℝ) (a : ℝ) (f : Ω → ℝ) :
    E (fun ω => a * f ω) = a * E f := by
  change E (a • f) = a • E f
  exact E.map_smul a f

@[simp] theorem expect_add (E : (Ω → ℝ) →ₗ[ℝ] ℝ) (f g : Ω → ℝ) :
    E (fun ω => f ω + g ω) = E f + E g := E.map_add f g

@[simp] theorem expect_const (E : (Ω → ℝ) →ₗ[ℝ] ℝ)
    (hnorm : E (fun _ => 1) = 1) (a : ℝ) : E (fun _ => a) = a := by
  have hx := expect_mul E a (fun _ => 1)
  simpa [hnorm] using hx

theorem abs_young (x T : ℝ) (hT : 0 < T) : |x| ≤ T + x^2/(4*T) := by
  have hs := sq_nonneg (|x|-2*T)
  have ha : |x|^2 = x^2 := sq_abs x
  have hp : 0 < 4*T := by positivity
  calc
    |x| ≤ (T*(4*T)+x^2)/(4*T) := (le_div_iff₀ hp).2 (by nlinarith)
    _ = T+x^2/(4*T) := by field_simp

/-- The sole covariance estimate uses positivity and the stopped second moment;
no independence of the stopping time and the observed score is assumed. -/
theorem covariance_young
    (E : (Ω → ℝ) →ₗ[ℝ] ℝ)
    (hmono : ∀ f g, (∀ ω, f ω ≤ g ω) → E f ≤ E g)
    (hnorm : E (fun _ => 1) = 1)
    (τ M : Ω → ℝ) (K V T : ℝ) (hK : 0 ≤ K) (hT : 0 < T)
    (hτ0 : ∀ ω, 0 ≤ τ ω) (hτK : ∀ ω, τ ω ≤ K)
    (hsecond : E (fun ω => M ω ^ 2) ≤ V) :
    E (fun ω => τ ω * M ω) ≤ K * (T + V/(4*T)) := by
  have hpt (ω : Ω) : τ ω * M ω ≤ K*T + (K/(4*T))*(M ω)^2 := by
    calc
      τ ω * M ω ≤ τ ω * |M ω| :=
        mul_le_mul_of_nonneg_left (le_abs_self _) (hτ0 ω)
      _ ≤ K * |M ω| := mul_le_mul_of_nonneg_right (hτK ω) (abs_nonneg _)
      _ ≤ K * (T + (M ω)^2/(4*T)) :=
        mul_le_mul_of_nonneg_left (abs_young (M ω) T hT) hK
      _ = K*T + (K/(4*T))*(M ω)^2 := by ring
  have havg := hmono _ _ hpt
  rw [expect_add, expect_const E hnorm, expect_mul] at havg
  have hc : 0 ≤ K/(4*T) := by positivity
  have hv := mul_le_mul_of_nonneg_left hsecond hc
  calc
    E (fun ω => τ ω * M ω) ≤ K*T + (K/(4*T))*V := by linarith
    _ = K*(T+V/(4*T)) := by ring

/-- Chord bound for the deterministic part, expressed as a per-budget rate. -/
theorem endpoint (h d N K q : ℝ) (hh : 0 ≤ h) (hN : 0 < N)
    (hq : 0 ≤ q) (hqK : q ≤ K) :
    h*q + h*q*(q-1)/N + d*(K-q) ≤
      K * max d (h*(1+(K-1)/N)) := by
  let c := max d (h*(1+(K-1)/N))
  have hgap : 0 ≤ h*q*(K-q)/N := by positivity
  have hchord : h*q+h*q*(q-1)/N ≤ h*(1+(K-1)/N)*q := by
    ring_nf at hgap ⊢
    linarith
  have hpre := mul_le_mul_of_nonneg_right (le_max_right d (h*(1+(K-1)/N))) hq
  have hpost := mul_le_mul_of_nonneg_right (le_max_left d (h*(1+(K-1)/N)))
    (sub_nonneg.mpr hqK)
  nlinarith

/-- Main expectation bound. Its martingale hypotheses must be supplied by the
actual adaptive oracle experiment; this theorem proves only their algebraic
consequence, with the stopping covariance retained explicitly. -/
theorem stopped_payoff
    (E : (Ω → ℝ) →ₗ[ℝ] ℝ)
    (hmono : ∀ f g, (∀ ω, f ω ≤ g ω) → E f ≤ E g)
    (hnorm : E (fun _ => 1) = 1)
    (τ S P : Ω → ℝ) (C h d N K V T : ℝ)
    (hC : 0 ≤ C) (hh : 0 ≤ h) (hN : 0 < N) (hK : 0 ≤ K) (hT : 0 < T)
    (hτ0 : ∀ ω, 0 ≤ τ ω) (hτK : ∀ ω, τ ω ≤ K)
    (hmean1 : E (fun ω => S ω - h*τ ω) = 0)
    (hmean2 : E (fun ω => P ω - τ ω*S ω + h*τ ω*(τ ω+1)/2) = 0)
    (hsecond : E (fun ω => (S ω - h*τ ω)^2) ≤ V) :
    E (fun ω => C*(S ω+2*P ω/N)+d*(K-τ ω)) ≤
      K*max d (C*h*(1+(K-1)/N)) + (2*C*K/N)*(T+V/(4*T)) := by
  let M₁ : Ω → ℝ := fun ω => S ω - h*τ ω
  let M₂ : Ω → ℝ := fun ω => P ω - τ ω*S ω + h*τ ω*(τ ω+1)/2
  let R := K*max d (C*h*(1+(K-1)/N))
  have hpoint (ω : Ω) : C*(S ω+2*P ω/N)+d*(K-τ ω) ≤
      R + C*M₁ ω + (2*C/N)*(τ ω*M₁ ω) + (2*C/N)*M₂ ω := by
    have hend := endpoint (C*h) d N K (τ ω) (mul_nonneg hC hh) hN (hτ0 ω) (hτK ω)
    have hid : C*(S ω+2*P ω/N)+d*(K-τ ω) =
      (C*h*τ ω+C*h*τ ω*(τ ω-1)/N+d*(K-τ ω)) +
      C*M₁ ω+(2*C/N)*(τ ω*M₁ ω)+(2*C/N)*M₂ ω := by
      dsimp [M₁, M₂]
      ring
    rw [hid]
    dsimp [R]
    linarith
  have havg := hmono _ _ hpoint
  simp only [expect_add, expect_const E hnorm, expect_mul] at havg
  have hm1 : E M₁ = 0 := hmean1
  have hm2 : E M₂ = 0 := hmean2
  rw [hm1, hm2] at havg
  have hcov := covariance_young E hmono hnorm τ M₁ K V T hK hT hτ0 hτK hsecond
  have hcoef : 0 ≤ 2*C/N := by positivity
  have hc := mul_le_mul_of_nonneg_left hcov hcoef
  dsimp [R] at havg
  calc
    E (fun ω => C*(S ω+2*P ω/N)+d*(K-τ ω)) ≤
      K*max d (C*h*(1+(K-1)/N))+(2*C/N)*(K*(T+V/(4*T))) := by
        simp only [expect_add, expect_mul]
        linarith
    _ = _ := by ring

/-- Explicit mixed72 nonce constants. This scalar fact does not establish the
schedule's h or gmax bounds; those are hypotheses in its application. -/
theorem mixed72_young_coefficient :
    (2*(99/98 : ℝ)/4096 + (512*(99/98 : ℝ)/5)*((2:ℝ)^20/(2:ℝ)^86)) < 1/1000 := by
  norm_num

/-- Symbolic bound reducing the mixed72 covariance correction to its
nonce/sample-size coefficient. All moment and budget estimates are explicit. -/
theorem covariance_coefficient (C κ K N L g h : ℝ)
    (hC : 0 ≤ C) (hκ : 0 < κ) (hK : 0 ≤ K) (hN : 0 < N)
    (hL : 0 ≤ L) (hg : 0 ≤ g) (hh : 0 ≤ h)
    (hKN : K ≤ N/10) (hgmax : g ≤ L*κ/2) (hhmean : h ≤ κ) :
    (2*C*K/N)*(κ*N/4096+(K*g*h)/(4*(κ*N/4096))) ≤
      κ*K*(2*C/4096+(512*C/5)*(L/N)) := by
  have hv : K*g*h ≤ (N/10)*(L*κ/2)*κ := by
    have hkg : K*g ≤ (N/10)*(L*κ/2) :=
      mul_le_mul hKN hgmax hg (by positivity)
    exact mul_le_mul hkg hhmean hh (by positivity)
  have hden : 0 < 4*(κ*N/4096) := by positivity
  have hvdiv := div_le_div_of_nonneg_right hv hden.le
  have hcoeff : 0 ≤ 2*C*K/N := by positivity
  have hfull := mul_le_mul_of_nonneg_left
    (add_le_add_left hvdiv (κ*N/4096)) hcoeff
  calc
    (2*C*K/N)*(κ*N/4096+(K*g*h)/(4*(κ*N/4096))) ≤
      (2*C*K/N)*(κ*N/4096+((N/10)*(L*κ/2)*κ)/(4*(κ*N/4096))) := by simpa only [add_comm] using hfull
    _ = κ*K*(2*C/4096+(512*C/5)*(L/N)) := by
      field_simp
      <;> ring

/-- The mixed72 covariance error is at most one thousandth of κ times budget.
The concrete powers are the nonce count and number of signing draws. -/
theorem mixed72_covariance (C κ K g h : ℝ)
    (hC : 0 ≤ C) (hCmax : C ≤ 99/98) (hκ : 0 < κ) (hK : 0 ≤ K)
    (hg : 0 ≤ g) (hh : 0 ≤ h)
    (hKN : K ≤ (2:ℝ)^86/10) (hgmax : g ≤ (2:ℝ)^20*κ/2) (hhmean : h ≤ κ) :
    (2*C*K/(2:ℝ)^86)*(κ*(2:ℝ)^86/4096+
      (K*g*h)/(4*(κ*(2:ℝ)^86/4096))) ≤ κ*K/1000 := by
  have hx := covariance_coefficient C κ K ((2:ℝ)^86) ((2:ℝ)^20) g h
    hC hκ hK (by positivity) (by positivity) hg hh hKN hgmax hhmean
  have hfirst : 2*C/4096 ≤ 2*(99/98 : ℝ)/4096 := by linarith
  have hsecond : (512*C/5)*((2:ℝ)^20/(2:ℝ)^86) ≤
      (512*(99/98 : ℝ)/5)*((2:ℝ)^20/(2:ℝ)^86) :=
    mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  have hcoeff := (add_le_add hfirst hsecond).trans mixed72_young_coefficient.le
  have htotal := mul_le_mul_of_nonneg_left hcoeff (mul_nonneg hκ.le hK)
  calc
    _ ≤ κ*K*(2*C/4096+(512*C/5)*((2:ℝ)^20/(2:ℝ)^86)) := hx
    _ ≤ κ*K*(1/1000) := htotal
    _ = _ := by ring

/-- Endpoint plus explicit covariance error for the mixed72 budget branch.
No stopping theorem is assumed implicitly: both zero means and the second
moment inequality appear in this statement. -/
theorem stopped_mixed72_payoff
    (E : (Ω → ℝ) →ₗ[ℝ] ℝ)
    (hmono : ∀ f g, (∀ ω, f ω ≤ g ω) → E f ≤ E g)
    (hnorm : E (fun _ => 1) = 1)
    (τ S P : Ω → ℝ) (C h d κ K g : ℝ)
    (hC : 0 ≤ C) (hCmax : C ≤ 99/98) (hh : 0 ≤ h) (hκ : 0 < κ)
    (hK : 0 ≤ K) (hg : 0 ≤ g) (hKN : K ≤ (2:ℝ)^86/10)
    (hgmax : g ≤ (2:ℝ)^20*κ/2) (hhmean : h ≤ κ)
    (hτ0 : ∀ ω, 0 ≤ τ ω) (hτK : ∀ ω, τ ω ≤ K)
    (hmean1 : E (fun ω => S ω - h*τ ω) = 0)
    (hmean2 : E (fun ω => P ω - τ ω*S ω + h*τ ω*(τ ω+1)/2) = 0)
    (hsecond : E (fun ω => (S ω - h*τ ω)^2) ≤ K*g*h) :
    E (fun ω => C*(S ω+2*P ω/(2:ℝ)^86)+d*(K-τ ω)) ≤
      K*max d (11*C*h/10) + κ*K/1000 := by
  have hN : 0 < (2:ℝ)^86 := by positivity
  have hT : 0 < κ*(2:ℝ)^86/4096 := by positivity
  have hx := stopped_payoff E hmono hnorm τ S P C h d ((2:ℝ)^86) K
    (K*g*h) (κ*(2:ℝ)^86/4096) hC hh hN hK hT hτ0 hτK
    hmean1 hmean2 hsecond
  have hc := mixed72_covariance C κ K g h hC hCmax hκ hK hg hh hKN hgmax hhmean
  have hratio : (K-1)/(2:ℝ)^86 ≤ 1/10 := (div_le_iff₀ hN).2 (by linarith)
  have hpre : C*h*(1+(K-1)/(2:ℝ)^86) ≤ 11*C*h/10 := by
    have hm := mul_le_mul_of_nonneg_left hratio (mul_nonneg hC hh)
    nlinarith
  have hend := mul_le_mul_of_nonneg_left (max_le_max_left d hpre) hK
  exact hx.trans (add_le_add hend hc)

/-- A uniform pre-signing authentication charge is absorbed by the continuation
rate when alpha ≤ d. This is deterministic algebra only. -/
theorem pre_authentication_domination (α d K q u : ℝ)
    (hα : α ≤ d) (hu : 0 ≤ u) :
    α*u+d*(K-q-u) ≤ d*(K-q) := by
  have hx := mul_le_mul_of_nonneg_right hα hu
  nlinarith

#print axioms covariance_young
#print axioms endpoint
#print axioms stopped_payoff
#print axioms mixed72_young_coefficient
#print axioms covariance_coefficient
#print axioms mixed72_covariance
#print axioms stopped_mixed72_payoff
#print axioms pre_authentication_domination

end WeightedStopping
