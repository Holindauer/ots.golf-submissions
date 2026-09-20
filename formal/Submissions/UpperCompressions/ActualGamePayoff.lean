import Submissions.UpperCompressions.SignedConditionalMaster
import Submissions.UpperCompressions.WideInitialEager
import Submissions.UpperCompressions.WideInitialPayoff

/-! The actual complete mixed72 experiment reduces to physical pre-sign-cache
replay and excess payoffs, with the genuine remaining-budget clock. There are
no assumed posterior, security, or conditional-game bounds in this theorem. -/
open OracleSpec OracleComp OracleComp.EvalDist ENNReal
noncomputable section
open scoped Classical
set_option maxRecDepth 10000
namespace OptimalOTS.WeightedConstruction.WideForest
open OptimalOTS.Dag Name WeightedReplacement WeightedSampling WideInitialGame
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Finset.univ Finset.filter

theorem signerAverage_eq_actual (m : Message) (c : Cache) (k : ℕ)
    (F : SignedWinner → ℝ≥0∞) :
    signerAverage m c k F = outE (loop 86 WeightedSchedule.decode WeightedSchedule.tier m k) c F :=
  (outE_length_preload (msgBits+86) (loop 86 WeightedSchedule.decode WeightedSchedule.tier m k) c F).symm

theorem conditional_eq_game (A : forestScheme.toAlgorithm.Adversary) (pk : PublicKey)
    (m : Message) (st : A.State) (c : Cache) :
    conditional A pk (m,st) c =
      conditionalGame A ((fiberA pk).filter (fun ξ => ¬ Cache.Hits c (kc ξ))) m st c signBudget := by
  rw [conditional_eager]
  unfold conditionalGame outcomeSuccessLoss
  apply Finset.sum_congr rfl
  intro ξ hξ
  have hpk := pkOf_of_subset_fiberA (Finset.filter_subset _ _) ξ hξ
  rw [hpk]

theorem conditional_actual_master (A : forestScheme.toAlgorithm.Adversary) (pk : PublicKey)
    (m : Message) (st : A.State) (c : Cache) (B : ℕ)
    (hB : SupportedPostBudget A pk m st c signBudget B) :
    conditional A pk (m,st) c ≤ survivingSpr pk c + sumW (fiberA pk) *
      (signerAverage m c signBudget (winnerReplay c m) +
        B*(authRate+signerAverage m c signBudget winnerExcess)) := by
  rw [conditional_eq_game]
  exact conditional_game_master A pk _ (Finset.filter_subset _ _) m st c signBudget B
    (fun ξ hξ => (Finset.mem_filter.mp hξ).2) hB

theorem supportedPostBudget_of_experiment (A : forestScheme.toAlgorithm.Adversary) {B : ℕ}
    (hB : CostAtMost (forestScheme.toAlgorithm.experiment A) B) (pk : PublicKey)
    (r : (Message × A.State) × Cache × ℕ)
    (hr : r ∈ support (runRemaining (A.choose pk) ∅ (B-995))) :
    SupportedPostBudget A pk r.1.1 r.1.2 r.2.1 signBudget (r.2.2-signBudget) := by
  intro ξ hξ g p hp
  have h := (experiment_choose_reserve A hB pk r hr).2.2 ξ hξ _ p hp
  have hpk := pkOf_of_subset_fiberA (Finset.Subset.refl _) ξ hξ
  simpa only [hpk] using h

def continuationPayoff (A : forestScheme.toAlgorithm.Adversary)
    (pk : PublicKey) (r : (Message × A.State) × Cache × ℕ) : ℝ≥0∞ :=
  sumW (fiberA pk) * (signerAverage r.1.1 r.2.1 signBudget (winnerReplay r.2.1 r.1.1) +
    (r.2.2-signBudget : ℕ)*(authRate+signerAverage r.1.1 r.2.1 signBudget winnerExcess))

/-- Full actual experiment-to-payoff bound. The public choose stage and all
remaining sign/post stages use their actual shared-cache semantics and one
residual budget. Pre-sign spurious loss is absorbed exactly once. -/
theorem global_actual_game_payoff (A : forestScheme.toAlgorithm.Adversary) {B : ℕ}
    (hB : CostAtMost (forestScheme.toAlgorithm.experiment A) B) :
    E (run (forestScheme.toAlgorithm.experiment A) ∅) successValue ≤
      (∑ pk : PublicKey, (authRate*sumW (fiberA pk))*
        expectedCharge (otherPaid (isIndexLength (msgBits+86))) (A.choose pk) ∅) +
      ∑ pk : PublicKey, E (runRemaining (A.choose pk) ∅ (B-995)) (continuationPayoff A pk) := by
  apply global_payoff_clock A (B-995) (isIndexLength (msgBits+86))
    (fun q hq => exists_encQuery_of_length q hq) (continuationPayoff A)
  intro pk r hr
  exact conditional_actual_master A pk r.1.1 r.1.2 r.2.1 (r.2.2-signBudget)
    (supportedPostBudget_of_experiment A hB pk r hr)

#print axioms conditional_actual_master
#print axioms supportedPostBudget_of_experiment
#print axioms global_actual_game_payoff
end OptimalOTS.WeightedConstruction.WideForest
