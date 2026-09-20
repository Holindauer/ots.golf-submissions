import Submissions.UpperCompressions.OracleExecutionConcentration

/-! Time-uniform linear-boundary concentration for actual OracleComp execution.
The counter may ignore private queries and cache hits. No union over time is used. -/
noncomputable section
open OracleSpec OracleComp OracleComp.EvalDist
open scoped Classical ENNReal
namespace WeightedOracleExecution
open WeightedFirstHit

set_option maxHeartbeats 800000
variable {ι S α : Type} {spec : OracleSpec ι} [spec.Inhabited]

theorem actual_linear_boundary
    (impl : QueryImpl spec (StateT S ProbComp)) (counter : S → ℕ) (Z : S → ℝ)
    (θ c δ Q : ℝ) (hθ : 0 ≤ θ) (hδ : 0 ≤ δ) (hc : c ≤ θ*δ/2)
    (hstep : ∀ t s, expectedValue ((impl t).run s)
      (fun out => ENNReal.ofReal (Real.exp (θ*Z out.2-c*(counter out.2:ℝ)))) ≤
        ENNReal.ofReal (Real.exp (θ*Z s-c*(counter s:ℝ))))
    (oa : OracleComp spec α) (s₀ : S) (hq0 : counter s₀ = 0) (hZ0 : Z s₀ = 0) :
    let hit := fun (_ : ℕ) (s : S) => δ*max (counter s:ℝ) Q ≤ Z s
    let kill := fun (_ : ℕ) (_ : S) => False
    Pr[fun out => out.2.status = .hit |
      (simulateQ (stoppedImpl impl hit kill) oa).run (classify hit kill 0 s₀)] ≤
      ENNReal.ofReal (Real.exp (-(θ*δ*Q/2))) := by
  dsimp only
  let hit := fun (_ : ℕ) (s : S) => δ*max (counter s:ℝ) Q ≤ Z s
  let kill := fun (_ : ℕ) (_ : S) => False
  let F : ℕ → S → ℝ := fun _ s => θ*Z s-c*(counter s:ℝ)
  have hlocal : ∀ t n s, ¬hit n s → ¬kill n s →
      expectedValue ((impl t).run s) (fun out => ENNReal.ofReal (Real.exp (F (n+1) out.2))) ≤
        ENNReal.ofReal (Real.exp (F n s)) := fun t _ s _ _ => hstep t s
  have hmgf := expected_stopped_simulate_le impl hit kill
    (fun n s => ENNReal.ofReal (Real.exp (F n s))) hlocal oa s₀
  have hinit : ENNReal.ofReal (Real.exp (F 0 s₀)) = 1 := by simp [F, hq0, hZ0]
  rw [hinit] at hmgf
  apply actual_exponential_tail
    ((simulateQ (stoppedImpl impl hit kill) oa).run (classify hit kill 0 s₀))
    (fun out => out.2.status = .hit)
    (fun out => F out.2.clock out.2.value) (θ*δ*Q/2) _ hmgf
  intro out hout
  have hh := out.2.valid hout
  change δ*max (counter out.2.value:ℝ) Q ≤ Z out.2.value at hh
  have hθδ : 0 ≤ θ*δ := mul_nonneg hθ hδ
  have hsum : (counter out.2.value:ℝ)+Q ≤ 2*max (counter out.2.value:ℝ) Q := by
    linarith [le_max_left (counter out.2.value:ℝ) Q, le_max_right (counter out.2.value:ℝ) Q]
  have hx := mul_le_mul_of_nonneg_left hsum hθδ
  have hy := mul_le_mul_of_nonneg_left hh hθ
  have hz := mul_le_mul_of_nonneg_right hc (Nat.cast_nonneg (counter out.2.value) : (0:ℝ) ≤ _)
  dsimp only [F]
  nlinarith

#print axioms actual_linear_boundary
end WeightedOracleExecution
