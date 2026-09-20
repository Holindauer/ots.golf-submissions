import Submissions.UpperCompressions.ExpectedChargeMaster

/-! Exact accounting across actual public/private phases of a shared-cache
OracleComp program. No pathwise budget is spent a second time at a phase split. -/
open OracleSpec OracleComp OracleComp.EvalDist ENNReal
noncomputable section
open scoped Classical
namespace WeightedReplacement
open OptimalOTS
set_option maxHeartbeats 800000

theorem expectedCharge_bind {α β : Type} (charge : Spec.Domain → ℝ≥0∞)
    (oa : OracleComp Spec α) (k : α → OracleComp Spec β) (c : Cache) :
    expectedCharge charge (oa >>= k) c = expectedCharge charge oa c +
      E (run oa c) (fun p => expectedCharge charge (k p.1) p.2) := by
  induction oa using OracleComp.inductionOn generalizing c with
  | pure a => simp [run_pure, E_pure]
  | query_bind t next ih =>
    rw [bind_assoc, expectedCharge_query]
    simp_rw [ih]
    rw [expectedCharge_query, run_query_bind, E_bind]
    simp only [E, expectedValue_def, mul_add, ENNReal.tsum_add]
    ring

theorem expectedCharge_bind_pure {α β : Type} (charge : Spec.Domain → ℝ≥0∞)
    (oa : OracleComp Spec α) (f : α → β) (c : Cache) :
    expectedCharge charge (oa >>= fun a => pure (f a)) c = expectedCharge charge oa c := by
  rw [expectedCharge_bind]
  simp [E, expectedValue_def]

theorem expectedCharge_map {α β : Type} (charge : Spec.Domain → ℝ≥0∞)
    (oa : OracleComp Spec α) (f : α → β) (c : Cache) :
    expectedCharge charge (f <$> oa) c = expectedCharge charge oa c := by
  rw [map_eq_bind_pure_comp]
  exact expectedCharge_bind_pure charge oa f c

/-- The separate phase expectations recombine to precisely the original
program's cost, with each continuation starting at the real terminal cache. -/
theorem expectedCharge_three_phases {α β γ : Type} (charge : Spec.Domain → ℝ≥0∞)
    (pre : OracleComp Spec α) (middle : α → OracleComp Spec β)
    (post : α → β → OracleComp Spec γ) (c : Cache) :
    expectedCharge charge (pre >>= fun a => middle a >>= post a) c =
      expectedCharge charge pre c + E (run pre c) (fun p =>
        expectedCharge charge (middle p.1) p.2 +
          E (run (middle p.1) p.2) (fun q => expectedCharge charge (post p.1 q.1) q.2)) := by
  rw [expectedCharge_bind]
  apply congrArg (expectedCharge charge pre c + ·)
  congr 1
  funext p
  exact expectedCharge_bind charge _ _ _

#print axioms expectedCharge_bind
#print axioms expectedCharge_map
#print axioms expectedCharge_three_phases
end WeightedReplacement
