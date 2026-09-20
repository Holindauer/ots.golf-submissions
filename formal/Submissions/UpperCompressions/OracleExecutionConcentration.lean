import Submissions.UpperCompressions.FirstHitFreedman
import OptimalOTS.Model
import VCVio.EvalDist.Expectation

/-! Concentration induction over actual OracleComp stateful simulation.
The expectedValue and probability are VCVio's genuine distribution semantics,
not a newly assumed execution law. Concrete one-query drift is still required. -/

noncomputable section
open OracleSpec OracleComp OracleComp.EvalDist
open scoped Classical ENNReal
namespace WeightedOracleExecution

set_option maxHeartbeats 800000

variable {ι : Type} {spec : OracleSpec ι} {S α : Type}

/-- An actual stateful oracle implementation preserves a nonnegative potential
in expectation through any OracleComp program if each primitive query does so.
Free private queries need no budget or count assumption. -/
theorem expected_simulate_le
    (impl : QueryImpl spec (StateT S ProbComp)) (Φ : S → ℝ≥0∞)
    (hstep : ∀ q s, expectedValue ((impl q).run s) (fun out => Φ out.2) ≤ Φ s)
    (oa : OracleComp spec α) (s : S) :
    expectedValue ((simulateQ impl oa).run s) (fun out => Φ out.2) ≤ Φ s := by
  induction oa using OracleComp.inductionOn generalizing s with
  | pure x => simp
  | query_bind q k ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    rw [expectedValue_bind]
    have hcont : ∀ out : spec.Range q × S,
        expectedValue ((simulateQ impl (k out.1)).run out.2) (fun out => Φ out.2) ≤ Φ out.2 :=
      fun out => ih out.1 out.2
    exact (expectedValue_mono ((impl q).run s) hcont).trans (hstep q s)

open WeightedFirstHit

variable [spec.Inhabited]

/-- Instrument the actual implementation with the checked first-hit classifier.
After stopping, dummy answers let the finite program finish while the recorded
state and clock remain fixed. No original oracle query is executed after stop. -/
def stoppedImpl (impl : QueryImpl spec (StateT S ProbComp))
    (hit kill : ℕ → S → Prop) : QueryImpl spec (StateT (StoppedState hit kill) ProbComp) :=
  fun q st => if st.status = .active then do
    let (answer, s') ← (impl q).run st.value
    return (answer, classify hit kill (st.clock+1) s')
  else pure (default, st)

@[simp] theorem stoppedImpl_run
    (impl : QueryImpl spec (StateT S ProbComp)) (hit kill : ℕ → S → Prop)
    (q : spec.Domain) (st : StoppedState hit kill) :
    ((stoppedImpl impl hit kill) q).run st =
      if st.status = .active then (do
        let (answer, s') ← (impl q).run st.value
        return (answer, classify hit kill (st.clock+1) s'))
      else pure (default, st) := rfl

/-- Local drift is needed only on active states; stopping freezes the potential. -/
theorem expected_stopped_step_le
    (impl : QueryImpl spec (StateT S ProbComp)) (hit kill : ℕ → S → Prop)
    (Φ : ℕ → S → ℝ≥0∞)
    (hstep : ∀ q t s, ¬hit t s → ¬kill t s →
      expectedValue ((impl q).run s) (fun out => Φ (t+1) out.2) ≤ Φ t s)
    (q : spec.Domain) (st : StoppedState hit kill) :
    expectedValue (((stoppedImpl impl hit kill) q).run st)
      (fun out => Φ out.2.clock out.2.value) ≤ Φ st.clock st.value := by
  change expectedValue (if st.status = .active then _ else _) _ ≤ _
  split_ifs with hs
  · rw [expectedValue_bind]
    simpa only [expectedValue_pure, classify_clock, classify_value] using
      hstep q st.clock st.value (st.safe hs).1 (st.safe hs).2
  · simp

/-- The stopped potential bound is now about the actual VCVio simulation law. -/
theorem expected_stopped_simulate_le
    (impl : QueryImpl spec (StateT S ProbComp)) (hit kill : ℕ → S → Prop)
    (Φ : ℕ → S → ℝ≥0∞)
    (hstep : ∀ q t s, ¬hit t s → ¬kill t s →
      expectedValue ((impl q).run s) (fun out => Φ (t+1) out.2) ≤ Φ t s)
    (oa : OracleComp spec α) (s : S) :
    expectedValue ((simulateQ (stoppedImpl impl hit kill) oa).run (classify hit kill 0 s))
      (fun out => Φ out.2.clock out.2.value) ≤ Φ 0 s := by
  have hx := expected_simulate_le (stoppedImpl impl hit kill)
    (fun st => Φ st.clock st.value)
    (expected_stopped_step_le impl hit kill Φ hstep) oa (classify hit kill 0 s)
  simpa only [classify_clock, classify_value] using hx

/-- Exponential Markov for the actual finite probability semantics. -/
theorem actual_exponential_tail (oa : ProbComp α) (bad : α → Prop)
    (Z : α → ℝ) (b : ℝ) (hbad : ∀ x, bad x → b ≤ Z x)
    (hmgf : expectedValue oa (fun x => ENNReal.ofReal (Real.exp (Z x))) ≤ 1) :
    Pr[bad | oa] ≤ ENNReal.ofReal (Real.exp (-b)) := by
  let c := ENNReal.ofReal (Real.exp (-b))
  have hcost (x : α) (hx : bad x) :
      1 ≤ ENNReal.ofReal (Real.exp (Z x)) * c := by
    dsimp [c]
    rw [← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]
    have he : (1:ℝ) ≤ Real.exp (Z x + -b) := by
      rw [Real.one_le_exp_iff]
      linarith [hbad x hx]
    exact_mod_cast ENNReal.ofReal_le_ofReal he
  have hp := probEvent_le_tsum_probOutput_mul_cost oa bad
    (fun x => ENNReal.ofReal (Real.exp (Z x))*c) hcost
  change Pr[bad | oa] ≤ expectedValue oa (fun x => ENNReal.ofReal (Real.exp (Z x))*c) at hp
  rw [expectedValue_mul_const] at hp
  apply hp.trans
  calc
    expectedValue oa (fun x => ENNReal.ofReal (Real.exp (Z x)))*c ≤ 1*c := by gcongr
    _ = c := one_mul c

/-- Actual OracleComp maximal Freedman bound under primitive-query drift.
The probability is that the instrumented concrete simulation ever records a
hit before killing. Free and paid queries are both part of the syntax; only the
caller-supplied variance proxy is charged to the paid-query budget. -/
theorem actual_stopped_freedman
    (impl : QueryImpl spec (StateT S ProbComp)) (oa : OracleComp spec α)
    (Z W : ℕ → S → ℝ) (s₀ : S) (a v J : ℝ)
    (ha : 0 < a) (hv : 0 < v) (hJ : 0 ≤ J)
    (hZ0 : Z 0 s₀ = 0) (hW0 : W 0 s₀ = 0)
    (hit kill : ℕ → S → Prop)
    (hstep : ∀ θ, 0 < θ → θ*J < 3 → ∀ q t s, ¬hit t s → ¬kill t s →
      expectedValue ((impl q).run s)
        (fun out => ENNReal.ofReal (Real.exp (θ*Z (t+1) out.2-θ^2*W (t+1) out.2/(2*(1-θ*J/3))))) ≤
        ENNReal.ofReal (Real.exp (θ*Z t s-θ^2*W t s/(2*(1-θ*J/3)))))
    (hZ : ∀ t s, hit t s → a ≤ Z t s) (hW : ∀ t s, hit t s → W t s ≤ v) :
    Pr[fun out => out.2.status = .hit |
      (simulateQ (stoppedImpl impl hit kill) oa).run (classify hit kill 0 s₀)] ≤
        ENNReal.ofReal (Real.exp (-a^2/(2*(v+J*a/3)))) := by
  let θ := a/(v+J*a/3)
  obtain ⟨hθ, hθJ, heq⟩ := WeightedKernel.optimized_exponent a v J ha hv hJ
  change 0 < θ at hθ
  change θ*J < 3 at hθJ
  change θ*a-θ^2*v/(2*(1-θ*J/3)) = a^2/(2*(v+J*a/3)) at heq
  let F : ℕ → S → ℝ := fun t s => θ*Z t s-θ^2*W t s/(2*(1-θ*J/3))
  have hmgf := expected_stopped_simulate_le impl hit kill
    (fun t s => ENNReal.ofReal (Real.exp (F t s))) (hstep θ hθ hθJ) oa s₀
  have hinit : ENNReal.ofReal (Real.exp (F 0 s₀)) = 1 := by simp [F, hZ0, hW0]
  rw [hinit] at hmgf
  have hcoef : 0 ≤ θ^2/(2*(1-θ*J/3)) := by
    apply div_nonneg (sq_nonneg θ)
    linarith
  have hbad (out : α × StoppedState hit kill) (hs : out.2.status = .hit) :
      a^2/(2*(v+J*a/3)) ≤ F out.2.clock out.2.value := by
    have hh := out.2.valid hs
    have hz := mul_le_mul_of_nonneg_left (hZ _ _ hh) hθ.le
    have hw := mul_le_mul_of_nonneg_left (hW _ _ hh) hcoef
    have heqv : θ^2*v/(2*(1-θ*J/3)) = (θ^2/(2*(1-θ*J/3)))*v := by ring
    have heqw : θ^2*W out.2.clock out.2.value/(2*(1-θ*J/3)) =
        (θ^2/(2*(1-θ*J/3)))*W out.2.clock out.2.value := by ring
    dsimp [F]
    rw [← heq, heqv, heqw]
    linarith
  have hx := actual_exponential_tail
    ((simulateQ (stoppedImpl impl hit kill) oa).run (classify hit kill 0 s₀))
    (fun out => out.2.status = .hit) (fun out => F out.2.clock out.2.value)
    (a^2/(2*(v+J*a/3))) hbad hmgf
  simpa only [neg_div] using hx

/-- A real-valued state quantity whose per-query increase is charged to `cost`
is bounded pathwise by the program's structural query budget. -/
theorem state_bound_of_query_budget
    (impl : QueryImpl spec (StateT S ProbComp)) (V : S → ℝ)
    (cost : spec.Domain → ℕ) (c : ℝ) (hc : 0 ≤ c)
    (hstep : ∀ q s out, out ∈ support ((impl q).run s) →
      V out.2 ≤ V s+c*(cost q : ℝ))
    (oa : OracleComp spec α) (B : ℕ)
    (hbudget : oa.IsQueryBound B (fun q b => cost q ≤ b) (fun q b => b-cost q))
    (s : S) (out : α × S) (hout : out ∈ support ((simulateQ impl oa).run s)) :
    V out.2 ≤ V s+c*(B:ℝ) := by
  induction oa using OracleComp.inductionOn generalizing B s out with
  | pure x =>
    have he : out = (x,s) := by simpa using hout
    subst out
    have hnonneg : 0 ≤ c*(B:ℝ) := by positivity
    exact le_add_of_nonneg_right hnonneg
  | query_bind q k ih =>
    obtain ⟨hcost, hrest⟩ := hbudget
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at hout
    obtain ⟨mid, hmid, hout⟩ := hout
    have hnext := ih mid.1 (B-cost q) (hrest mid.1) mid.2 out hout
    have hlocal := hstep q s mid hmid
    have hsum : ((B-cost q : ℕ):ℝ)+(cost q:ℝ) = (B:ℝ) := by
      exact_mod_cast Nat.sub_add_cancel hcost
    nlinarith

/-- Specialization to the protected cost model: private sampling has cost zero,
while every hash, including a cache hit, keeps its complete compression cost. -/
theorem state_bound_of_protected_budget
    {S α : Type} (impl : QueryImpl OptimalOTS.Spec (StateT S ProbComp))
    (V : S → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (hstep : ∀ q s out, out ∈ support ((impl q).run s) →
      V out.2 ≤ V s+c*(OptimalOTS.queryCost q : ℝ))
    (oa : OracleComp OptimalOTS.Spec α) (B : ℕ) (hbudget : OptimalOTS.CostAtMost oa B)
    (s : S) (out : α × S) (hout : out ∈ support ((simulateQ impl oa).run s)) :
    V out.2 ≤ V s+c*(B:ℝ) :=
  state_bound_of_query_budget impl V OptimalOTS.queryCost c hc hstep oa B hbudget s out hout

/-- An explicit early-stopping interpreter using the actual query
implementation. Its Boolean result records a hit before kill, including the
initial state and the state after the last primitive query. -/
def firstHitRun (impl : QueryImpl spec (StateT S ProbComp))
    (hit kill : ℕ → S → Prop) (oa : OracleComp spec α) : ℕ → S → ProbComp Bool :=
  OracleComp.construct
    (fun _ t s => pure (decide (hit t s)))
    (fun q _ rec t s => if hit t s then pure true else if kill t s then pure false else do
      let (answer, s') ← (impl q).run s
      rec answer (t+1) s') oa

@[simp] theorem firstHitRun_pure
    (impl : QueryImpl spec (StateT S ProbComp)) (hit kill : ℕ → S → Prop)
    (x : α) (t : ℕ) (s : S) :
    firstHitRun impl hit kill (pure x) t s = pure (decide (hit t s)) := by
  simp [firstHitRun]

@[simp] theorem firstHitRun_query_bind
    (impl : QueryImpl spec (StateT S ProbComp)) (hit kill : ℕ → S → Prop)
    (q : spec.Domain) (k : spec.Range q → OracleComp spec α) (t : ℕ) (s : S) :
    firstHitRun impl hit kill ((liftM (spec.query q) : OracleComp spec (spec.Range q)) >>= k) t s =
      if hit t s then pure true else if kill t s then pure false else (do
        let (answer, s') ← (impl q).run s
        firstHitRun impl hit kill (k answer) (t+1) s') := by
  simp [firstHitRun]

/-- Once stopped, the remaining real OracleComp syntax is interpreted with
deterministic dummy answers, and its recorded state is exactly unchanged. -/
theorem stopped_simulate_of_stop
    (impl : QueryImpl spec (StateT S ProbComp)) (hit kill : ℕ → S → Prop)
    (oa : OracleComp spec α) (st : StoppedState hit kill) (hstop : st.status ≠ .active) :
    (simulateQ (stoppedImpl impl hit kill) oa).run st =
      pure (evalWithAnswerFn (fun _ => default) oa, st) := by
  induction oa using OracleComp.inductionOn with
  | pure x => simp
  | query_bind q k ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    change ((if st.status = .active then _ else pure (default, st)) >>= _) = _
    rw [if_neg hstop]
    simp only [pure_bind]
    rw [ih]
    congr 1

/-- The instrumented simulation's hit flag has exactly the early-interpreter
probability. This removes any assumed link between stopping and execution. -/
theorem prob_stopped_hit_eq_firstHitRun
    (impl : QueryImpl spec (StateT S ProbComp)) (hit kill : ℕ → S → Prop)
    (oa : OracleComp spec α) (t : ℕ) (s : S) :
    Pr[fun out => out.2.status = .hit |
      (simulateQ (stoppedImpl impl hit kill) oa).run (classify hit kill t s)] =
      Pr[= true | firstHitRun impl hit kill oa t s] := by
  induction oa using OracleComp.inductionOn generalizing t s with
  | pure x =>
    by_cases hh : hit t s
    · simp [hh]
    · by_cases hk : kill t s <;> simp [classify, hh, hk]
  | query_bind q k ih =>
    by_cases hh : hit t s
    · rw [stopped_simulate_of_stop _ _ _ _ _ (by simp [hh])]
      simp [hh]
    · by_cases hk : kill t s
      · rw [stopped_simulate_of_stop _ _ _ _ _ (by simp [hh, hk])]
        simp [hh, hk]
      · rw [firstHitRun_query_bind, if_neg hh, if_neg hk]
        simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
        simp only [stoppedImpl_run, classify_status_active _ _ _ _ hh hk, if_true,
          classify_clock, classify_value]
        simp only [classify_clock, classify_value, bind_assoc, pure_bind]
        rw [probEvent_bind_eq_tsum, probOutput_bind_eq_tsum]
        apply tsum_congr
        intro out
        congr 1
        exact ih out.1 (t+1) out.2

#print axioms expected_simulate_le
#print axioms expected_stopped_step_le
#print axioms expected_stopped_simulate_le
#print axioms actual_exponential_tail
#print axioms actual_stopped_freedman
#print axioms state_bound_of_query_budget
#print axioms state_bound_of_protected_budget
#print axioms stopped_simulate_of_stop
#print axioms prob_stopped_hit_eq_firstHitRun

end WeightedOracleExecution
