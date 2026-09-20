import Submissions.UpperCompressions.ActualRealExpectation
import Submissions.UpperCompressions.WeightedMoments
import Submissions.UpperCompressions.OracleExecutionConcentration

/-! Stopped moments in actual OracleComp execution from an explicit one-query
observable law. The law must still be instantiated for the shared cache and
concrete decoder; no stopped means or second moments are assumed. -/

noncomputable section
open OracleSpec OracleComp
open scoped Classical BigOperators
namespace WeightedActualMoments
open WeightedRealExecution WeightedRow.Weights WeightedOracleExecution

set_option maxHeartbeats 800000

variable {ι S α : Type} [Fintype ι] [DecidableEq ι]

/-- All three moment hypotheses needed by the small-budget proof, derived from
actual execution and the fresh-class query law. The terminal fresh-query count
may depend arbitrarily on prior observations and private randomness. -/
theorem actual_stopped_moments
    (w : WeightedRow.Weights ι)
    (impl : QueryImpl OptimalOTS.Spec (StateT S ProbComp))
    (qCount : S → ℕ) (counts : S → (ι → ℕ))
    (fresh : OptimalOTS.Spec.Domain → S → Bool)
    (hlaw : ∀ t s (f : ℕ → (ι → ℕ) → ℝ),
      realEval ((impl t).run s) (fun out => f (qCount out.2) (counts out.2)) =
        w.expect (fun x => f (step (fresh t s) (qCount s) (counts s) x).1
          (step (fresh t s) (qCount s) (counts s) x).2))
    (hcount : ∀ t s out, out ∈ support ((impl t).run s) →
      qCount out.2 ≤ qCount s+OptimalOTS.queryCost t)
    (G : ℝ) (hG : 0 ≤ G) (hg : ∀ i, w.g i ≤ G)
    (oa : OracleComp OptimalOTS.Spec α) (B : ℕ) (hbudget : OptimalOTS.CostAtMost oa B)
    (s₀ : S) (hq0 : qCount s₀ = 0) (hk0 : counts s₀ = fun _ => 0) :
    realEval ((simulateQ impl oa).run s₀) (fun out => w.M1 (qCount out.2) (counts out.2)) = 0 ∧
    realEval ((simulateQ impl oa).run s₀) (fun out => w.M2 (qCount out.2) (counts out.2)) = 0 ∧
    realEval ((simulateQ impl oa).run s₀) (fun out => (w.M1 (qCount out.2) (counts out.2))^2) ≤
      (B:ℝ)*G*w.mean := by
  have hM10 : w.M1 (qCount s₀) (counts s₀) = 0 := by simp [M1, score, hq0, hk0]
  have hM20 : w.M2 (qCount s₀) (counts s₀) = 0 := by simp [M2, score, pairScore, hq0, hk0]
  have hmean1 : ∀ t s,
      realEval ((impl t).run s) (fun out => w.M1 (qCount out.2) (counts out.2)) =
        w.M1 (qCount s) (counts s) := by
    intro t s
    rw [hlaw]
    exact w.M1_step_mean (fresh t s) (qCount s) (counts s)
  have hmean2 : ∀ t s,
      realEval ((impl t).run s) (fun out => w.M2 (qCount out.2) (counts out.2)) =
        w.M2 (qCount s) (counts s) := by
    intro t s
    rw [hlaw]
    exact w.M2_step_mean (fresh t s) (qCount s) (counts s)
  have hfirst := realEval_simulate_eq impl (fun s => w.M1 (qCount s) (counts s)) hmean1 oa s₀
  have hsecond := realEval_simulate_eq impl (fun s => w.M2 (qCount s) (counts s)) hmean2 oa s₀
  rw [hM10] at hfirst
  rw [hM20] at hsecond
  refine ⟨hfirst, hsecond, ?_⟩
  have hcompstep : ∀ t s,
      realEval ((impl t).run s)
        (fun out => (w.M1 (qCount out.2) (counts out.2))^2-G*w.mean*(qCount out.2:ℝ)) ≤
          (w.M1 (qCount s) (counts s))^2-G*w.mean*(qCount s:ℝ) := by
    intro t s
    rw [hlaw t s (fun q k => (w.M1 q k)^2-G*w.mean*(q:ℝ))]
    exact w.M1_step_square_compensated (fresh t s) G hG hg (qCount s) (counts s)
  have hcomp := realEval_simulate_le impl
    (fun s => (w.M1 (qCount s) (counts s))^2-G*w.mean*(qCount s:ℝ)) hcompstep oa s₀
  rw [hM10, hq0] at hcomp
  simp only [Nat.cast_zero, mul_zero, zero_pow, sub_zero] at hcomp
  rw [realEval_sub, realEval_mul] at hcomp
  have hcountR : ∀ t s out, out ∈ support ((impl t).run s) →
      (qCount out.2:ℝ) ≤ (qCount s:ℝ)+1*(OptimalOTS.queryCost t:ℝ) := by
    intro t s out hout
    norm_num only [one_mul]
    exact_mod_cast hcount t s out hout
  have hpath : ∀ out ∈ support ((simulateQ impl oa).run s₀), (qCount out.2:ℝ) ≤ (B:ℝ) := by
    intro out hout
    have hx := state_bound_of_protected_budget impl (fun s => (qCount s:ℝ)) 1
      zero_le_one hcountR oa B hbudget s₀ out hout
    simpa only [hq0, Nat.cast_zero, zero_add, one_mul] using hx
  have hqmean := realEval_le_const_of_support ((simulateQ impl oa).run s₀)
    (fun out => (qCount out.2:ℝ)) B hpath
  have hh : 0 ≤ w.mean := by
    unfold mean
    exact Finset.sum_nonneg (fun i _ => mul_nonneg (w.p_pos i).le (w.g_nonneg i))
  have hb := mul_le_mul_of_nonneg_left hqmean (mul_nonneg hG hh)
  nlinarith

#print axioms actual_stopped_moments

end WeightedActualMoments
