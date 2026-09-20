import Submissions.UpperCompressions.ActualGamePayoffGated
import Submissions.UpperCompressions.WideReplayEvent
import Submissions.UpperCompressions.WeightedBudgetClosure
import Submissions.UpperCompressions.WideInitialClock

/-! Concrete replay/excess expansion of the actual full-game payoff. The bad
gate is paid once, while the conditional table error is kept separate and only
bounded after averaging over the actual adaptive public execution. -/
open OracleSpec OracleComp OracleComp.EvalDist ENNReal
noncomputable section
open scoped Classical
set_option maxRecDepth 10000
namespace OptimalOTS.WeightedConstruction.WideForest
open OptimalOTS.Dag Name WeightedReplacement WeightedSampling WideInitialGame
open WeightedCacheCounts WideDomains WeightedSchedule WeightedBudgetClosure
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Finset.univ Finset.filter

def cacheHazard (m : Message) (c : Cache) : ℝ :=
  securityWeights.hazard ((2:ℝ)^86) (seen (rowDomain m) c).card
    (classCounts indexDomain c decode) (classCounts (rowDomain m) c decode)

theorem signer_replay_bound (m : Message) (c : Cache) :
    signerAverage m c signBudget (winnerReplay c m) ≤
      ENNReal.ofReal (C*cacheHazard m c)+ENNReal.ofReal (WideCachedRow.tableFailure m c) := by
  rw [signerAverage_eq_actual]
  have he : winnerReplay c m = WideCachedRow.alternatePayoff m c := by
    funext s
    cases s with
    | none => rfl
    | some s =>
      rcases s with ⟨η,i⟩
      rw [WideCachedRow.alternatePayoff_some]
      rfl
  rw [he]
  exact (WideCachedRow.actual_alternative_bound m c).trans ENNReal.ofReal_add_le

theorem signer_excess_bound (m : Message) (c : Cache) (hc : WideEmpirical.Good c) :
    signerAverage m c signBudget winnerExcess ≤
      ENNReal.ofReal (C*(WeightedReference.kappa*(2/5)+WeightedReference.kappa/100)) +
        ENNReal.ofReal (WideCachedRow.tableFailure m c) := by
  rw [signerAverage_eq_actual]
  have he : winnerExcess = (fun s => ENNReal.ofReal (WeightedCompletion.score s
      (fun r : Winner 86 WeightedSchedule.M => WeightedSchedule.excess r.2))) := by
    funext s
    cases s <;> simp [winnerExcess,WeightedCompletion.score]
  rw [he]
  exact (WideCachedRow.actual_excess_bound m c hc).trans ENNReal.ofReal_add_le

theorem concrete_postRate : authRate +
    ENNReal.ofReal (C*(WeightedReference.kappa*(2/5)+WeightedReference.kappa/100)) =
      ENNReal.ofReal postRate := by
  rw [authRate_ofReal,← ENNReal.ofReal_add]
  · rfl
  · unfold WeightedReference.kappa
    positivity
  · unfold C WeightedReference.kappa
    positivity

theorem concrete_continuation_bound (m : Message) (c : Cache) (hc : WideEmpirical.Good c)
    (remaining : ℕ) :
    signerAverage m c signBudget (winnerReplay c m) +
      remaining*(authRate+signerAverage m c signBudget winnerExcess) ≤
      ENNReal.ofReal (C*cacheHazard m c)+ENNReal.ofReal postRate*remaining +
        (1+remaining)*ENNReal.ofReal (WideCachedRow.tableFailure m c) := by
  have he : authRate+signerAverage m c signBudget winnerExcess ≤
      ENNReal.ofReal postRate+ENNReal.ofReal (WideCachedRow.tableFailure m c) := by
    calc
      _ ≤ authRate + (ENNReal.ofReal (C*(WeightedReference.kappa*(2/5)+WeightedReference.kappa/100)) +
          ENNReal.ofReal (WideCachedRow.tableFailure m c)) := add_le_add le_rfl (signer_excess_bound m c hc)
      _ = _ := by rw [← add_assoc,concrete_postRate]
  calc
    _ ≤ (ENNReal.ofReal (C*cacheHazard m c)+ENNReal.ofReal (WideCachedRow.tableFailure m c)) +
        remaining*(ENNReal.ofReal postRate+ENNReal.ofReal (WideCachedRow.tableFailure m c)) :=
      add_le_add (signer_replay_bound m c) (mul_le_mul_right he remaining)
    _ = _ := by ring

def preAuth (A : forestScheme.toAlgorithm.Adversary) : ℝ≥0∞ :=
  ∑ pk : PublicKey, (authRate*sumW (fiberA pk))*
    expectedCharge (otherPaid (isIndexLength (msgBits+86))) (A.choose pk) ∅

def weightedClock (A : forestScheme.toAlgorithm.Adversary) (B : ℕ)
    (F : PublicKey → ((Message × A.State) × Cache × ℕ) → ℝ≥0∞) : ℝ≥0∞ :=
  ∑ pk : PublicKey, sumW (fiberA pk)*E (runRemaining (A.choose pk) ∅ (B-995)) (F pk)

def gatedHazard (A : forestScheme.toAlgorithm.Adversary)
    (good : PublicKey → ((Message × A.State) × Cache × ℕ) → Prop)
    (pk : PublicKey) (r : (Message × A.State) × Cache × ℕ) : ℝ≥0∞ :=
  if good pk r then ENNReal.ofReal (C*cacheHazard r.1.1 r.2.1) else 0

def badGate (A : forestScheme.toAlgorithm.Adversary)
    (good : PublicKey → ((Message × A.State) × Cache × ℕ) → Prop)
    (pk : PublicKey) (r : (Message × A.State) × Cache × ℕ) : ℝ≥0∞ :=
  if good pk r then 0 else 1

def postRemaining (A : forestScheme.toAlgorithm.Adversary)
    (_pk : PublicKey) (r : (Message × A.State) × Cache × ℕ) : ℝ≥0∞ := (r.2.2-signBudget : ℕ)

def tableError (A : forestScheme.toAlgorithm.Adversary)
    (_pk : PublicKey) (r : (Message × A.State) × Cache × ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (WideCachedRow.tableFailure r.1.1 r.2.1)

theorem gated_payoff_pointwise (A : forestScheme.toAlgorithm.Adversary) (B : ℕ)
    (good : PublicKey → ((Message × A.State) × Cache × ℕ) → Prop)
    (hgood : ∀ pk r, good pk r → WideEmpirical.Good r.2.1)
    (pk : PublicKey) (r : (Message × A.State) × Cache × ℕ)
    (hr : r.2.2-signBudget ≤ B) :
    gatedContinuationPayoff A good pk r ≤ sumW (fiberA pk)*
      (gatedHazard A good pk r+ENNReal.ofReal postRate*postRemaining A pk r+
        badGate A good pk r+(1+B)*tableError A pk r) := by
  by_cases hg : good pk r
  · simp only [gatedContinuationPayoff,gatedHazard,badGate,if_pos hg,add_zero,postRemaining,tableError]
    apply mul_le_mul_right
    refine (concrete_continuation_bound r.1.1 r.2.1 (hgood pk r hg) _).trans ?_
    gcongr
  · simp only [gatedContinuationPayoff,gatedHazard,badGate,if_neg hg,zero_add,mul_one]
    calc
      _ = sumW (fiberA pk)*1 := by rw [mul_one]
      _ ≤ _ := mul_le_mul_right (le_add_right le_add_self) _

theorem weightedClock_add (A : forestScheme.toAlgorithm.Adversary) (B : ℕ)
    (F G : PublicKey → ((Message × A.State) × Cache × ℕ) → ℝ≥0∞) :
    weightedClock A B (fun pk r => F pk r+G pk r) = weightedClock A B F+weightedClock A B G := by
  unfold weightedClock
  simp only [auth_E_add,mul_add,Finset.sum_add_distrib]

theorem weightedClock_const_mul (A : forestScheme.toAlgorithm.Adversary) (B : ℕ) (a : ℝ≥0∞)
    (F : PublicKey → ((Message × A.State) × Cache × ℕ) → ℝ≥0∞) :
    weightedClock A B (fun pk r => a*F pk r) = a*weightedClock A B F := by
  unfold weightedClock
  simp_rw [← E_const_mul]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem weightedClock_tableError_le (A : forestScheme.toAlgorithm.Adversary) (B : ℕ) :
    weightedClock A B (tableError A) ≤ (2:ℝ≥0∞)⁻¹^761 := by
  have htail (pk : PublicKey) : E (runRemaining (A.choose pk) ∅ (B-995)) (tableError A pk) ≤
      (2:ℝ≥0∞)⁻¹^761 := by
    have h := WideCachedRow.tableFailure_average (A.choose pk) (fun x => x.1) ∅ (fun _ _ => rfl)
    rw [← runRemaining_project (A.choose pk) ∅ (B-995),E_map] at h
    exact h
  calc
    _ ≤ ∑ pk : PublicKey, sumW (fiberA pk)*((2:ℝ≥0∞)⁻¹^761) :=
      Finset.sum_le_sum fun pk _ => mul_le_mul_right (htail pk) _
    _ = _ := by rw [← Finset.sum_mul,sum_fiber_weights,one_mul]

/-- Shared concrete final-payoff expansion. The good hazard remains gated;
post remaining cost is ungated; bad probability and the averaged completion
tail are each charged once. Small and large numerical closures use this same
actual-game bound. -/
theorem global_actual_payoff_expanded (A : forestScheme.toAlgorithm.Adversary) {B : ℕ}
    (hB : CostAtMost (forestScheme.toAlgorithm.experiment A) B)
    (good : PublicKey → ((Message × A.State) × Cache × ℕ) → Prop)
    (hgood : ∀ pk r, good pk r → WideEmpirical.Good r.2.1) :
    E (run (forestScheme.toAlgorithm.experiment A) ∅) successValue ≤
      preAuth A+weightedClock A B (gatedHazard A good)+
      ENNReal.ofReal postRate*weightedClock A B (postRemaining A)+
      weightedClock A B (badGate A good)+(1+B)*((2:ℝ≥0∞)⁻¹^761) := by
  have h := global_actual_game_payoff_gated A hB good
  have hp : (∑ pk : PublicKey, E (runRemaining (A.choose pk) ∅ (B-995))
      (gatedContinuationPayoff A good pk)) ≤
      weightedClock A B (fun pk r => gatedHazard A good pk r+
        ENNReal.ofReal postRate*postRemaining A pk r+badGate A good pk r+(1+B)*tableError A pk r) := by
    apply Finset.sum_le_sum
    intro pk _
    rw [E_const_mul]
    apply expectedValue_mono_of_support
    intro r hr
    apply gated_payoff_pointwise A B good hgood pk r
    exact (Nat.sub_le _ _).trans ((experiment_choose_reserve A hB pk r hr).2.1.trans (Nat.sub_le _ _))
  refine (h.trans (add_le_add le_rfl hp)).trans ?_
  rw [weightedClock_add,weightedClock_add,weightedClock_add,
    weightedClock_const_mul,weightedClock_const_mul]
  calc
    _ = preAuth A+weightedClock A B (gatedHazard A good)+
        ENNReal.ofReal postRate*weightedClock A B (postRemaining A)+
        weightedClock A B (badGate A good)+(1+B)*weightedClock A B (tableError A) := by unfold preAuth; ring
    _ ≤ _ := add_le_add le_rfl (mul_le_mul_right (weightedClock_tableError_le A B) (1+B))

#print axioms signer_replay_bound
#print axioms concrete_continuation_bound
#print axioms weightedClock_tableError_le
#print axioms global_actual_payoff_expanded
end OptimalOTS.WeightedConstruction.WideForest
