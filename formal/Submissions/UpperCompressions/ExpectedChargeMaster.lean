import Submissions.UpperCompressions.ReplacementPublicCost
import Submissions.UpperCompressions.WideAuthCoupling

/-! Expected-cost potential induction for the actual shared-cache interpreter.
The charge is accumulated on the original query stream, including cache hits. -/
open OracleSpec OracleComp OracleComp.EvalDist ENNReal
noncomputable section
open scoped Classical
namespace WeightedExpectedCharge
open OptimalOTS OptimalOTS.Dag WeightedReplacement
set_option maxHeartbeats 800000

/-- Local additive drift charges the actual expected primitive-query cost,
without replacing its expectation by the whole pathwise budget. -/
theorem master_expected {α : Type} (Φ : Cache → ℝ≥0∞)
    (charge : Spec.Domain → ℝ≥0∞) (r : ℝ≥0∞)
    (hstep : ∀ t c, E ((oracleImpl t).run c) (fun p => Φ p.2) ≤ Φ c+r*charge t)
    (oa : OracleComp Spec α) (c : Cache) :
    E (run oa c) (fun p => Φ p.2) ≤ Φ c+r*expectedCharge charge oa c := by
  induction oa using OracleComp.inductionOn generalizing c with
  | pure a => simp [run_pure, E_pure]
  | query_bind t k ih =>
    rw [run_query_bind, E_bind, expectedCharge_query]
    calc
      _ ≤ E ((oracleImpl t).run c) (fun p => Φ p.2+r*expectedCharge charge (k p.1) p.2) :=
        E_mono _ (fun p => ih p.1 p.2)
      _ = E ((oracleImpl t).run c) (fun p => Φ p.2)+
          r*E ((oracleImpl t).run c) (fun p => expectedCharge charge (k p.1) p.2) := by
        simp only [E, expectedValue_def, mul_add, ENNReal.tsum_add]
        rw [← ENNReal.tsum_mul_left]
        congr 1
        apply tsum_congr
        intro p
        ring
      _ ≤ (Φ c+r*charge t)+r*E ((oracleImpl t).run c)
          (fun p => expectedCharge charge (k p.1) p.2) := add_le_add (hstep t c) le_rfl
      _ = _ := by ring

#print axioms master_expected
end WeightedExpectedCharge
