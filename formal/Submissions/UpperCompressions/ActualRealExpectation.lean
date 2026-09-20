import Mathlib
import OptimalOTS.Model
import VCVio.EvalDist.Expectation

/-! Signed finite expectation for actual ProbComp programs. Defined by their
uniform-query syntax, with exact bind laws and a proved ENNReal semantic bridge.
No integrability or execution-law equality is supplied as a hypothesis. -/

noncomputable section
open OracleSpec OracleComp OracleComp.EvalDist
open scoped Classical ENNReal BigOperators
namespace WeightedRealExecution

set_option maxHeartbeats 800000
variable {α β : Type}

/-- The real expectation functional of a finite private-randomness program. -/
def realEval (oa : ProbComp α) : (α → ℝ) →ₗ[ℝ] ℝ :=
  OracleComp.construct (fun a => LinearMap.proj a)
    (fun q _ rec => (Fintype.card (unifSpec.Range q):ℝ)⁻¹ • ∑ u, rec u) oa

@[simp] theorem realEval_pure (a : α) (f : α → ℝ) : realEval (pure a) f = f a := by
  simp [realEval]

@[simp] theorem realEval_query_bind (q : unifSpec.Domain)
    (k : unifSpec.Range q → ProbComp α) (f : α → ℝ) :
    realEval ((liftM (unifSpec.query q) : ProbComp (unifSpec.Range q)) >>= k) f =
      (Fintype.card (unifSpec.Range q):ℝ)⁻¹ * ∑ u, realEval (k u) f := by
  simp [realEval, LinearMap.sum_apply]

/-- The real tower property follows from actual ProbComp syntax. -/
theorem realEval_bind (oa : ProbComp α) (k : α → ProbComp β) (f : β → ℝ) :
    realEval (oa >>= k) f = realEval oa (fun a => realEval (k a) f) := by
  induction oa using OracleComp.inductionOn with
  | pure a => simp
  | query_bind q next ih =>
    rw [bind_assoc, realEval_query_bind, realEval_query_bind]
    congr 1
    apply Finset.sum_congr rfl
    intro u _
    exact ih u

/-- Positivity may be restricted to outputs in the actual computation support. -/
theorem realEval_mono_of_support (oa : ProbComp α) (f g : α → ℝ)
    (hfg : ∀ a ∈ support oa, f a ≤ g a) : realEval oa f ≤ realEval oa g := by
  induction oa using OracleComp.inductionOn with
  | pure a => simpa using hfg a (by simp)
  | query_bind q next ih =>
    rw [realEval_query_bind, realEval_query_bind]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Finset.sum_le_sum
    intro u _
    apply ih u
    intro a ha
    apply hfg a
    exact (mem_support_bind_iff _ _ _).2 ⟨u, by simp, ha⟩

theorem realEval_mono (oa : ProbComp α) (f g : α → ℝ)
    (hfg : ∀ a, f a ≤ g a) : realEval oa f ≤ realEval oa g :=
  realEval_mono_of_support oa f g (fun a _ => hfg a)

theorem realEval_nonneg (oa : ProbComp α) (f : α → ℝ) (hf : ∀ a, 0 ≤ f a) :
    0 ≤ realEval oa f := by
  have hx := realEval_mono oa (fun _ => 0) f hf
  change realEval oa (0 : α → ℝ) ≤ realEval oa f at hx
  rw [(realEval oa).map_zero] at hx
  exact hx

@[simp] theorem realEval_const (oa : ProbComp α) (c : ℝ) : realEval oa (fun _ => c) = c := by
  induction oa using OracleComp.inductionOn with
  | pure a => simp
  | query_bind q next ih =>
    rw [realEval_query_bind]
    simp only [ih, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have hn : (Fintype.card (unifSpec.Range q):ℝ) ≠ 0 := by positivity
    field_simp

@[simp] theorem realEval_add (oa : ProbComp α) (f g : α → ℝ) :
    realEval oa (fun a => f a+g a) = realEval oa f+realEval oa g := (realEval oa).map_add _ _

@[simp] theorem realEval_sub (oa : ProbComp α) (f g : α → ℝ) :
    realEval oa (fun a => f a-g a) = realEval oa f-realEval oa g := (realEval oa).map_sub _ _

@[simp] theorem realEval_mul (oa : ProbComp α) (c : ℝ) (f : α → ℝ) :
    realEval oa (fun a => c*f a) = c*realEval oa f := by
  change realEval oa (c • f) = c • realEval oa f
  exact (realEval oa).map_smul c f

theorem realEval_le_const_of_support (oa : ProbComp α) (f : α → ℝ) (c : ℝ)
    (hf : ∀ a ∈ support oa, f a ≤ c) : realEval oa f ≤ c := by
  simpa using realEval_mono_of_support oa f (fun _ => c) hf

/-- Exact agreement with VCVio's ENNReal expectation for nonnegative payoffs. -/
theorem ofReal_realEval (oa : ProbComp α) (f : α → ℝ) (hf : ∀ a, 0 ≤ f a) :
    ENNReal.ofReal (realEval oa f) = expectedValue oa (fun a => ENNReal.ofReal (f a)) := by
  induction oa using OracleComp.inductionOn with
  | pure a => simp
  | query_bind q next ih =>
    rw [realEval_query_bind, expectedValue_bind]
    have hc : 0 < (Fintype.card (unifSpec.Range q):ℝ) := by positivity
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_inv_of_pos hc]
    rw [ENNReal.ofReal_sum_of_nonneg (fun u _ => realEval_nonneg (next u) f hf)]
    simp_rw [ih]
    rw [expectedValue_def, tsum_fintype]
    simp only [probOutput_query, ENNReal.ofReal_natCast, Finset.mul_sum]

variable {ι : Type} {spec : OracleSpec ι} {S : Type}

/-- Signed local drift lifts directly through actual stateful OracleComp execution. -/
theorem realEval_simulate_le
    (impl : QueryImpl spec (StateT S ProbComp)) (Φ : S → ℝ)
    (hstep : ∀ q s, realEval ((impl q).run s) (fun out => Φ out.2) ≤ Φ s)
    (oa : OracleComp spec α) (s : S) :
    realEval ((simulateQ impl oa).run s) (fun out => Φ out.2) ≤ Φ s := by
  induction oa using OracleComp.inductionOn generalizing s with
  | pure a => simp
  | query_bind q next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    rw [realEval_bind]
    have hc : ∀ out : spec.Range q × S,
        realEval ((simulateQ impl (next out.1)).run out.2) (fun out => Φ out.2) ≤ Φ out.2 :=
      fun out => ih out.1 out.2
    exact (realEval_mono ((impl q).run s) _ _ hc).trans (hstep q s)

/-- Exact signed martingale expectation, requiring only primitive-query drift. -/
theorem realEval_simulate_eq
    (impl : QueryImpl spec (StateT S ProbComp)) (Φ : S → ℝ)
    (hstep : ∀ q s, realEval ((impl q).run s) (fun out => Φ out.2) = Φ s)
    (oa : OracleComp spec α) (s : S) :
    realEval ((simulateQ impl oa).run s) (fun out => Φ out.2) = Φ s := by
  induction oa using OracleComp.inductionOn generalizing s with
  | pure a => simp
  | query_bind q next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    rw [realEval_bind]
    have hf : (fun out : spec.Range q × S =>
        realEval ((simulateQ impl (next out.1)).run out.2) (fun out => Φ out.2)) =
        (fun out => Φ out.2) := by
      funext out
      exact ih out.1 out.2
    rw [hf, hstep]

#print axioms realEval_bind
#print axioms realEval_mono_of_support
#print axioms realEval_const
#print axioms ofReal_realEval
#print axioms realEval_simulate_le
#print axioms realEval_simulate_eq

end WeightedRealExecution
