import Submissions.UpperCompressions.WideStoppedPayoff
import Submissions.UpperCompressions.WeightedRealBridge
import Submissions.UpperCompressions.WideCountRelations

/-! Shared-budget aggregation of the checked actual small-budget moments. -/
noncomputable section
namespace OptimalOTS.WeightedConstruction.WideStoppedPayoff
open OracleSpec OracleComp OracleComp.EvalDist
open WeightedReference WeightedConstants WeightedBudgetClosure
open WeightedSchedule WideDomains WeightedCacheCounts WeightedRow.Weights
open WeightedRealExecution
open scoped Classical ENNReal
set_option maxHeartbeats 1000000

def pairEnvelope (c : Cache) : ℝ := score c+2*pairs c/(2:ℝ)^86

theorem score_nonneg (c : Cache) : 0 ≤ score c := by
  unfold score WeightedRow.Weights.score
  exact Finset.sum_nonneg fun i _ => mul_nonneg (Nat.cast_nonneg _) (referenceWeight_nonneg i)

theorem pairs_nonneg (c : Cache) : 0≤pairs c := by
  unfold pairs WeightedRow.Weights.pairScore
  exact Finset.sum_nonneg fun i _ => div_nonneg
    (mul_nonneg (Nat.cast_nonneg _) (referenceWeight_nonneg i)) (classProbability_pos i).le

theorem pairEnvelope_nonneg (c : Cache) : 0≤pairEnvelope c := by
  unfold pairEnvelope
  exact add_nonneg (score_nonneg c) (div_nonneg (mul_nonneg (by norm_num) (pairs_nonneg c)) (by positivity))

theorem hazard_le_pairEnvelope (m : Message) (c : Cache) :
    securityWeights.hazard ((2:ℝ)^86) (seen (rowDomain m) c).card
      (classCounts indexDomain c decode) (classCounts (rowDomain m) c decode) ≤ pairEnvelope c :=
  securityWeights.hazard_le_score_pair _ (by positivity) _ _ _ (row_class_le_global m c)

theorem actual_small_shared_real {α : Type} (oa : OracleComp Spec α) (B : ℕ)
    (hB : CostAtMost oa B) (hBN : (B:ℝ)≤(2:ℝ)^86/10)
    (c : Cache) (hf : ∀ q : Query,q.1=342 → c q=none)
    (a t : ℝ) (ha : 0≤a) (ht : 0≤t)
    (hclock : realEval (run oa c) (fun out => (queryCount out.2:ℝ))+a+t ≤ B) :
    C*realEval (run oa c) (fun out => pairEnvelope out.2)+(kappa/2)*a+postRate*t+
      kappa*(B:ℝ)/1000 ≤ (243337:ℝ)/245000*kappa*(B:ℝ) := by
  have h := small_payoff_actual oa B hB hBN c hf
  change realEval (run oa c) (fun out => C*pairEnvelope out.2+
    postRate*((B:ℝ)-(queryCount out.2:ℝ)))+_ ≤ _ at h
  rw [realEval_add,realEval_mul,realEval_mul,realEval_sub,realEval_const] at h
  have hp : 0≤postRate := by norm_num [postRate,C,kappa]
  have hshare := mul_le_mul_of_nonneg_left hclock hp
  have hauth := mul_le_mul_of_nonneg_right postRate_ge_auth ha
  nlinarith

theorem actual_small_shared_ennreal {α : Type} (oa : OracleComp Spec α) (B : ℕ)
    (hB : CostAtMost oa B) (hBN : (B:ℝ) ≤ (2:ℝ)^86/10)
    (c : Cache) (hf : ∀ q : Query,q.1=342 → c q=none)
    (a t : ℝ≥0∞)
    (hclock : E (run oa c) (fun out => (queryCount out.2:ℝ≥0∞))+a+t ≤ B) :
    ENNReal.ofReal C*E (run oa c) (fun out => ENNReal.ofReal (pairEnvelope out.2))+
      ENNReal.ofReal (kappa/2)*a+ENNReal.ofReal postRate*t+
      ENNReal.ofReal (kappa*(B:ℝ)/1000) ≤
        ENNReal.ofReal ((243337:ℝ)/245000*kappa*(B:ℝ)) := by
  let run := OptimalOTS.run oa c
  let Q := realEval run (fun out => (queryCount out.2:ℝ))
  let P := realEval run (fun out => pairEnvelope out.2)
  have hQ0 : 0 ≤ Q := realEval_nonneg run _ (fun out => Nat.cast_nonneg _)
  have hP0 : 0 ≤ P := realEval_nonneg run _ (fun out => pairEnvelope_nonneg _)
  have hQ : E run (fun out => (queryCount out.2:ℝ≥0∞))=ENNReal.ofReal Q := by
    simpa only [ENNReal.ofReal_natCast] using
      (ofReal_realEval run (fun out => (queryCount out.2:ℝ)) (fun out => Nat.cast_nonneg _)).symm
  have hP : E run (fun out => ENNReal.ofReal (pairEnvelope out.2))=ENNReal.ofReal P :=
    (ofReal_realEval run (fun out => pairEnvelope out.2) (fun out => pairEnvelope_nonneg _)).symm
  change E run _+a+t ≤ B at hclock
  rw [hQ] at hclock
  have haB : a ≤ (B:ℝ≥0∞) := (le_add_self.trans le_self_add).trans hclock
  have htB : t ≤ (B:ℝ≥0∞) := le_add_self.trans hclock
  have ha : a≠⊤ := ne_top_of_le_ne_top (by simp) haB
  have ht : t≠⊤ := ne_top_of_le_ne_top (by simp) htB
  have hsum : ENNReal.ofReal Q+a≠⊤ := ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top,ha⟩
  have hc := ENNReal.toReal_mono (show (B:ℝ≥0∞)≠⊤ by simp) hclock
  rw [ENNReal.toReal_add hsum ht,ENNReal.toReal_add ENNReal.ofReal_ne_top ha,
    ENNReal.toReal_ofReal hQ0,ENNReal.toReal_natCast] at hc
  have hr := actual_small_shared_real oa B hB hBN c hf a.toReal t.toReal
    ENNReal.toReal_nonneg ENNReal.toReal_nonneg hc
  have hC0 : 0 ≤ C := by norm_num [C]
  have hk0 : 0 ≤ kappa/2 := by norm_num [kappa]
  have hp0 : 0 ≤ postRate := by norm_num [postRate,C,kappa]
  have htail : 0 ≤ kappa*(B:ℝ)/1000 :=
    div_nonneg (mul_nonneg (by norm_num [kappa]) (Nat.cast_nonneg B)) (by norm_num)
  have hCP : 0 ≤ C*P := mul_nonneg hC0 hP0
  have hka : 0 ≤ (kappa/2)*a.toReal := mul_nonneg hk0 ENNReal.toReal_nonneg
  have hpt : 0 ≤ postRate*t.toReal := mul_nonneg hp0 ENNReal.toReal_nonneg
  have he := ENNReal.ofReal_le_ofReal hr
  change ENNReal.ofReal (C*P+(kappa/2)*a.toReal+postRate*t.toReal+kappa*(B:ℝ)/1000) ≤ _ at he
  rw [ENNReal.ofReal_add (add_nonneg (add_nonneg hCP hka) hpt) htail,
    ENNReal.ofReal_add (add_nonneg hCP hka) hpt,ENNReal.ofReal_add hCP hka,
    ENNReal.ofReal_mul hC0,ENNReal.ofReal_mul hk0,ENNReal.ofReal_mul hp0,
    ENNReal.ofReal_toReal ha,ENNReal.ofReal_toReal ht] at he
  change ENNReal.ofReal C*E run (fun out => ENNReal.ofReal (pairEnvelope out.2))+_+_+_ ≤ _
  rw [hP]
  exact he

#print axioms actual_small_shared_ennreal
#print axioms hazard_le_pairEnvelope
#print axioms actual_small_shared_real
end OptimalOTS.WeightedConstruction.WideStoppedPayoff
