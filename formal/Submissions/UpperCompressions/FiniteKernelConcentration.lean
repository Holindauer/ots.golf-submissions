import Mathlib

/-! Finite-horizon concentration algebra for explicit probability kernels.
A state may contain the complete adaptive transcript. A concrete random-oracle
experiment still has to provide these kernels and prove the step hypotheses. -/

noncomputable section
namespace WeightedKernel

variable {S : Type*}

/-- A sequence of normalized positive expectation functionals, one per state.
For finite S these can be ordinary finite probability sums. -/
abbrev Kernels (S : Type*) := ℕ → S → ((S → ℝ) →ₗ[ℝ] ℝ)

/-- Expected terminal payoff after n steps beginning at time t in state s. -/
def iterate (K : Kernels S) : ℕ → ℕ → S → ((S → ℝ) →ₗ[ℝ] ℝ)
  | 0, _, s => LinearMap.proj s
  | n+1, t, s => (K t s).comp (LinearMap.pi (fun s' => iterate K n (t+1) s'))

@[simp] theorem iterate_zero (K : Kernels S) (t : ℕ) (s : S) (f : S → ℝ) :
    iterate K 0 t s f = f s := rfl

@[simp] theorem iterate_succ (K : Kernels S) (n t : ℕ) (s : S) (f : S → ℝ) :
    iterate K (n+1) t s f = K t s (fun s' => iterate K n (t+1) s' f) := rfl

theorem iterate_mono (K : Kernels S)
    (hmono : ∀ t s f g, (∀ s', f s' ≤ g s') → K t s f ≤ K t s g)
    (n t : ℕ) (s : S) (f g : S → ℝ) (hfg : ∀ s', f s' ≤ g s') :
    iterate K n t s f ≤ iterate K n t s g := by
  induction n generalizing t s with
  | zero => exact hfg s
  | succ n ih =>
    simp only [iterate_succ]
    exact hmono t s _ _ (fun s' => ih (t+1) s')

theorem iterate_one (K : Kernels S) (hnorm : ∀ t s, K t s (fun _ => 1) = 1)
    (n t : ℕ) (s : S) : iterate K n t s (fun _ => 1) = 1 := by
  induction n generalizing t s with
  | zero => rfl
  | succ n ih =>
    simp only [iterate_succ]
    have hf : (fun s' => iterate K n (t+1) s' (fun _ => 1)) = (fun _ => 1) := by
      funext s'; exact ih (t+1) s'
    rw [hf, hnorm]

/-- Local supermartingale inequalities telescope for arbitrary adaptive
state-dependent kernels. No independence of states or increments is assumed. -/
theorem iterate_supermartingale (K : Kernels S)
    (hmono : ∀ t s f g, (∀ s', f s' ≤ g s') → K t s f ≤ K t s g)
    (Z : ℕ → S → ℝ) (hstep : ∀ t s, K t s (Z (t+1)) ≤ Z t s)
    (n t : ℕ) (s : S) : iterate K n t s (Z (t+n)) ≤ Z t s := by
  induction n generalizing t s with
  | zero => simp
  | succ n ih =>
    rw [iterate_succ]
    have hx : K t s (fun s' => iterate K n (t+1) s' (Z (t+(n+1)))) ≤
        K t s (Z (t+1)) := by
      apply hmono t s
      intro s'
      simpa only [show t+(n+1) = (t+1)+n by omega] using ih (t+1) s'
    exact hx.trans (hstep t s)

@[simp] theorem expect_mul (E : (S → ℝ) →ₗ[ℝ] ℝ) (a : ℝ) (f : S → ℝ) :
    E (fun s => a*f s) = a*E f := by
  change E (a • f) = a • E f
  exact E.map_smul a f

/-- A local compensated-MGF bound implies drift of the exponential potential.
The compensator c is predictable in the current state. -/
theorem exponential_step
    (E : (S → ℝ) →ₗ[ℝ] ℝ) (z a θ c : ℝ) (X : S → ℝ)
    (hmgf : E (fun s => Real.exp (θ*X s-c)) ≤ 1) :
    E (fun s => Real.exp (θ*(z+X s)-(a+c))) ≤ Real.exp (θ*z-a) := by
  have hf : (fun s => Real.exp (θ*(z+X s)-(a+c))) =
      (fun s => Real.exp (θ*z-a)*Real.exp (θ*X s-c)) := by
    funext s
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hf, expect_mul]
  simpa only [mul_one] using
    mul_le_mul_of_nonneg_left hmgf (Real.exp_nonneg (θ*z-a))

/-- Exponential Markov bound from a checked terminal potential expectation.
This can be used on a first-hit absorbing state to avoid a time union bound;
the absorbing construction itself must still be supplied by the caller. -/
theorem exponential_tail
    (E : (S → ℝ) →ₗ[ℝ] ℝ)
    (hmono : ∀ f g, (∀ s, f s ≤ g s) → E f ≤ E g)
    (bad : S → Prop) [DecidablePred bad]
    (Z : S → ℝ) (b : ℝ)
    (hbad : ∀ s, bad s → b ≤ Z s)
    (hmgf : E (fun s => Real.exp (Z s)) ≤ 1) :
    E (fun s => if bad s then 1 else 0) ≤ Real.exp (-b) := by
  have hpt (s : S) : Real.exp b * (if bad s then (1:ℝ) else 0) ≤ Real.exp (Z s) := by
    by_cases hs : bad s
    · simp only [if_pos hs, mul_one]
      exact Real.exp_le_exp.mpr (hbad s hs)
    · simp only [if_neg hs, mul_zero]
      exact Real.exp_nonneg _
  have hx := (hmono _ _ hpt).trans hmgf
  rw [expect_mul] at hx
  have hm := mul_le_mul_of_nonneg_left hx (Real.exp_nonneg (-b))
  have he : Real.exp (-b)*Real.exp b = 1 := by rw [← Real.exp_add]; simp
  rw [← mul_assoc, he, one_mul, mul_one] at hm
  exact hm

/-- Bernstein's optimized scalar exponent. -/
theorem optimized_exponent (a v J : ℝ) (ha : 0 < a) (hv : 0 < v) (hJ : 0 ≤ J) :
    let θ := a/(v+J*a/3)
    0 < θ ∧ θ*J < 3 ∧
      θ*a-θ^2*v/(2*(1-θ*J/3)) = a^2/(2*(v+J*a/3)) := by
  dsimp
  have hd : 0 < v+J*a/3 := by positivity
  have hθ : 0 < a/(v+J*a/3) := div_pos ha hd
  have hθJ : a/(v+J*a/3)*J < 3 := by
    rw [div_mul_eq_mul_div]
    apply (div_lt_iff₀ hd).2
    nlinarith
  refine ⟨hθ, hθJ, ?_⟩
  have hrem : 1-a/(v+J*a/3)*J/3 ≠ 0 := by linarith
  field_simp
  <;> ring

/-- Terminal Bernstein/Freedman tail from the exponential potential bound.
The variance proxy W may be random; the event includes W ≤ v. -/
theorem freedman_tail
    (E : (S → ℝ) →ₗ[ℝ] ℝ)
    (hmono : ∀ f g, (∀ s, f s ≤ g s) → E f ≤ E g)
    (bad : S → Prop) [DecidablePred bad]
    (Z W : S → ℝ) (a v J : ℝ) (ha : 0 < a) (hv : 0 < v) (hJ : 0 ≤ J)
    (hZ : ∀ s, bad s → a ≤ Z s) (hW : ∀ s, bad s → W s ≤ v)
    (hmgf : ∀ θ, 0 < θ → θ*J < 3 →
      E (fun s => Real.exp (θ*Z s-θ^2*W s/(2*(1-θ*J/3)))) ≤ 1) :
    E (fun s => if bad s then 1 else 0) ≤ Real.exp (-a^2/(2*(v+J*a/3))) := by
  let θ := a/(v+J*a/3)
  obtain ⟨hθ, hθJ, heq⟩ := optimized_exponent a v J ha hv hJ
  change 0 < θ at hθ
  change θ*J < 3 at hθJ
  change θ*a-θ^2*v/(2*(1-θ*J/3)) = a^2/(2*(v+J*a/3)) at heq
  have hcoef : 0 ≤ θ^2/(2*(1-θ*J/3)) := by
    apply div_nonneg (sq_nonneg θ)
    linarith
  have hbad (s : S) (hs : bad s) :
      a^2/(2*(v+J*a/3)) ≤ θ*Z s-θ^2*W s/(2*(1-θ*J/3)) := by
    have hz := mul_le_mul_of_nonneg_left (hZ s hs) hθ.le
    have hw := mul_le_mul_of_nonneg_left (hW s hs) hcoef
    calc
      _ = θ*a-θ^2*v/(2*(1-θ*J/3)) := heq.symm
      _ ≤ θ*Z s-(θ^2/(2*(1-θ*J/3)))*W s := by
        have heqv : θ^2*v/(2*(1-θ*J/3)) = (θ^2/(2*(1-θ*J/3)))*v := by ring
        rw [heqv]
        linarith
      _ = _ := by ring
  have hx := exponential_tail E hmono bad
    (fun s => θ*Z s-θ^2*W s/(2*(1-θ*J/3)))
    (a^2/(2*(v+J*a/3))) hbad (hmgf θ hθ hθJ)
  simpa only [neg_div] using hx

/-- Chaining state-dependent exponential drift gives a finite-horizon
Freedman tail. The caller supplies actual kernel drift, initialization, and the
terminal event interpretation. -/
theorem finite_kernel_freedman
    (K : Kernels S)
    (hmono : ∀ t s f g, (∀ s', f s' ≤ g s') → K t s f ≤ K t s g)
    (Z W : ℕ → S → ℝ) (s₀ : S) (n : ℕ) (a v J : ℝ)
    (ha : 0 < a) (hv : 0 < v) (hJ : 0 ≤ J)
    (hZ0 : Z 0 s₀ = 0) (hW0 : W 0 s₀ = 0)
    (hstep : ∀ θ, 0 < θ → θ*J < 3 → ∀ t s,
      K t s (fun s' => Real.exp (θ*Z (t+1) s'-θ^2*W (t+1) s'/(2*(1-θ*J/3)))) ≤
        Real.exp (θ*Z t s-θ^2*W t s/(2*(1-θ*J/3))))
    (bad : S → Prop) [DecidablePred bad]
    (hZ : ∀ s, bad s → a ≤ Z n s) (hW : ∀ s, bad s → W n s ≤ v) :
    iterate K n 0 s₀ (fun s => if bad s then 1 else 0) ≤
      Real.exp (-a^2/(2*(v+J*a/3))) := by
  apply freedman_tail (iterate K n 0 s₀) (iterate_mono K hmono n 0 s₀)
    bad (Z n) (W n) a v J ha hv hJ hZ hW
  intro θ hθ hθJ
  have hx := iterate_supermartingale K hmono
    (fun t s => Real.exp (θ*Z t s-θ^2*W t s/(2*(1-θ*J/3))))
    (hstep θ hθ hθJ) n 0 s₀
  simpa only [zero_add, hZ0, hW0, mul_zero, zero_div, sub_zero, Real.exp_zero] using hx

#print axioms iterate_mono
#print axioms iterate_one
#print axioms iterate_supermartingale
#print axioms exponential_step
#print axioms exponential_tail
#print axioms optimized_exponent
#print axioms freedman_tail
#print axioms finite_kernel_freedman

end WeightedKernel
