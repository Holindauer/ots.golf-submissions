import Submissions.UpperCompressions.WideHazardClock
import Submissions.UpperCompressions.WideHazardConstants

/-! Actual stopped clipped-hazard concentration for one message row. -/
noncomputable section
open OracleSpec OracleComp OracleComp.EvalDist
open scoped Classical ENNReal
namespace OptimalOTS.WeightedConstruction.WideHazard
open WeightedSchedule WideDomains WeightedRow.Weights WeightedRealExecution WeightedDualCache
open WeightedReference WeightedConstants WeightedOracleExecution WeightedFirstHit
attribute [local irreducible] Finset.univ Finset.filter queryPhase

def hit (B : ℕ) (m : Message) : ℕ → hashSpec.QueryCache → Prop := fun _ c =>
  (globalCount c:ℝ)≤B ∧ (7/100)*kappa*(B:ℝ)≤Z m c
def kill : ℕ → hashSpec.QueryCache → Prop := fun _ c => ¬WideEmpirical.Good c

theorem ZW_initial (m : Message) (c : hashSpec.QueryCache)
    (hf : ∀ q : Query,q.1=342 → c q=none) : Z m c=0 ∧ W m c=0 := by
  obtain ⟨hq,hk⟩ := WidePreSign.index_initial c hf
  obtain ⟨hr,hrow⟩ := WideConcentration.row_initial m c hf
  have hq' : globalCount c=0 := hq
  have hr' : rowCount m c=0 := hr
  have hk' : globalCounts c=fun _=>0 := hk
  constructor
  · simp [Z,hazard,WeightedRow.Weights.hazard,WeightedRow.Weights.seen,
      WeightedRow.Weights.bad,hq',hk']
  · simp [W,hq',hr']

theorem stopped_large_bound {β : Type} (B : ℕ) (hB : N/10≤(B:ℝ))
    (m : Message) (oa : OracleComp Spec β) (c : hashSpec.QueryCache)
    (hf : ∀ q : Query,q.1=342 → c q=none) :
    Pr[fun out => out.2.status=.hit |
      (simulateQ (stoppedImpl oracleImpl (hit B m) kill) oa).run
        (classify (hit B m) kill 0 c)] ≤ ENNReal.ofReal (Real.exp (-(2048:ℝ))) := by
  have hb : (0:ℝ)<B := lt_of_lt_of_le (by norm_num [N]) hB
  have hk : (0:ℝ)<kappa := by norm_num [kappa]
  have hd : (0:ℝ)<jumpBound := by norm_num [jumpBound,L,kappa,N]
  obtain ⟨hz0,hw0⟩ := ZW_initial m c hf
  have h := actual_stopped_freedman oracleImpl oa (fun _ => Z m) (fun _ => W m) c
    ((7/100)*kappa*(B:ℝ)) ((182/100)*jumpBound*kappa*(B:ℝ)) jumpBound
    (by positivity) (by positivity) hd.le hz0 hw0 (hit B m) kill
    (by
      intro θ hθ hθJ t n d _ hgood
      exact actual_potential_step m t d (by simpa only [kill,not_not] using hgood)
        θ hθ.le hθJ)
    (fun _ _ hs => hs.2)
    (fun _ d hs => W_budget_bound B m d hB hs.1)
  apply h.trans
  apply ENNReal.ofReal_le_ofReal
  apply Real.exp_le_exp.mpr
  have he := WeightedHazardConstants.large_exponent (B:ℝ) hB
  change (2048:ℝ) ≤
    ((7/100)*kappa*(B:ℝ))^2/(2*((182/100)*jumpBound*kappa*(B:ℝ)+
      jumpBound*((7/100)*kappa*(B:ℝ))/3)) at he
  simpa only [neg_div] using neg_le_neg he

#print axioms ZW_initial
#print axioms stopped_large_bound
end OptimalOTS.WeightedConstruction.WideHazard
