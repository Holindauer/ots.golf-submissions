import Submissions.UpperCompressions.SignedWinnerMaster

/-! The actual signing-failure branch of the common game master. It carries
pre-sign spurious mass once and spends only its supported public continuation. -/
open OracleSpec OracleComp OracleComp.EvalDist ENNReal
noncomputable section
open scoped Classical
set_option maxRecDepth 10000
namespace OptimalOTS.WeightedConstruction.WideForest
open OptimalOTS.Dag Name WeightedReplacement WeightedSampling
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Finset.univ Finset.filter

def nonePost (A : forestScheme.toAlgorithm.Adversary) (ξ : Rec)
    (m : Message) (st : A.State) := stBWithForgery A (pkOf ξ) m st none

def noneSuccessLoss (A : forestScheme.toAlgorithm.Adversary) (ξ : Rec)
    (m : Message) (st : A.State) (d : Cache) : ℝ≥0∞ :=
  E (run (nonePost A ξ m st) (Cache.extend d (kc ξ))) forgerySuccess

def noneOtherCost (A : forestScheme.toAlgorithm.Adversary) (ξ : Rec)
    (m : Message) (st : A.State) (d : Cache) : ℝ≥0∞ :=
  expectedCharge (otherPaid (isIndexLength (msgBits+86))) (nonePost A ξ m st) d

theorem retained_charge_eq (A : forestScheme.toAlgorithm.Adversary)
    (pk : PublicKey) (m : Message) (st : A.State) (σ : Option WeightedScheme.Signature)
    (charge : Spec.Domain → ℝ≥0∞) (c : Cache) :
    expectedCharge charge (stBWithForgery A pk m st σ) c =
      expectedCharge charge (stB A pk m st σ) c := by
  have h := expectedCharge_map charge (stBWithForgery A pk m st σ)
    (fun r : ForgeryResult => r.2.2) c
  rw [stBWithForgery_map] at h
  exact h.symm

theorem none_fiber_leaf (A : forestScheme.toAlgorithm.Adversary) (pk : BitVec 128)
    (T : Finset Rec) (hT : T ⊆ fiberA pk) (m : Message) (st : A.State)
    (c d' : Cache) (hd' : IndexExtension c d') (hTc : ∀ ξ∈T, ¬ Cache.Hits c (kc ξ)) :
    (∑ ξ∈T, w*noneSuccessLoss A ξ m st d') ≤
      (∑ ξ∈T, w*ind (Spr c ξ)) + authRate*(∑ ξ∈fiberA pk, w*noneOtherCost A ξ m st d') := by
  have hsum : (∑ ξ∈fiberA pk, w*noneOtherCost A ξ m st d') =
      sumW (fiberA pk)*expectedCharge (otherPaid (isIndexLength (msgBits+86)))
        (stB A pk m st none) d' := by
    calc
      _ = ∑ ξ∈fiberA pk, w*expectedCharge (otherPaid (isIndexLength (msgBits+86)))
          (stB A pk m st none) d' := by
        apply Finset.sum_congr rfl
        intro ξ hξ
        unfold noneOtherCost nonePost
        rw [retained_charge_eq, (Finset.mem_filter.mp hξ).2]
      _ = _ := (Finset.sum_mul _ _ _).symm
  calc
    _ = ∑ ξ∈T, w*E (run (stB A (pkOf ξ) m st none) (Cache.extend d' (kc ξ))) successValue := by
      apply Finset.sum_congr rfl
      intro ξ _
      exact congrArg (w*·) (retained_success_eq A (pkOf ξ) m st none _)
    _ ≤ (∑ ξ∈T, w*ind (Spr c ξ)) + (authRate*sumW (fiberA pk))*
        expectedCharge (otherPaid (isIndexLength (msgBits+86))) (stB A pk m st none) d' :=
      failed_sign_success_expected A pk T hT m st c d' hd' hTc
        (isIndexLength (msgBits+86)) (fun q hq => exists_encQuery_of_length q hq)
    _ = _ := by rw [hsum]; ring

theorem none_cost_budget (A : forestScheme.toAlgorithm.Adversary) (pk : BitVec 128)
    (m : Message) (st : A.State) (c : Cache) (k B : ℕ)
    (hB : SupportedPostBudget A pk m st c k B) :
    signedAverage m c k none (fun _ d => authRate*(∑ ξ∈fiberA pk, w*noneOtherCost A ξ m st d)) ≤
      (authRate*sumW (fiberA pk)*B)*signedMass m c k none := by
  rw [← signedAverage_const]
  apply signedAverage_mono_support
  intro g p hp hb
  have hcont : ∀ ξ∈fiberA pk, noneOtherCost A ξ m st p.2 ≤ B := by
    intro ξ hξ
    have h := hB ξ hξ g p hp
    have hc : CostAtMost (nonePost A ξ m st) B := by
      simpa only [hb,signatureFromWinner,Option.map_none,nonePost] using h
    have hq := expectedCharge_budget (otherPaid (isIndexLength (msgBits+86))) 1
      (fun t => by simpa only [one_mul] using otherPaid_le_queryCost (isIndexLength (msgBits+86)) t)
      (nonePost A ξ m st) B hc p.2
    simpa only [one_mul,noneOtherCost] using hq
  calc
    _ ≤ authRate*(∑ ξ∈fiberA pk, w*B) := mul_le_mul_right
      (Finset.sum_le_sum fun ξ hξ => mul_le_mul_right (hcont ξ hξ) w) authRate
    _ = _ := by rw [← Finset.sum_mul]; simp only [sumW,mul_assoc]

/-- Joint actual failed-signature success, with no posterior/index premise and
no budget obligation for unsupported signer outputs. -/
theorem signed_none_master (A : forestScheme.toAlgorithm.Adversary) (pk : BitVec 128)
    (T : Finset Rec) (hT : T ⊆ fiberA pk)
    (m : Message) (st : A.State) (c : Cache) (k B : ℕ)
    (hTc : ∀ ξ∈T, ¬ Cache.Hits c (kc ξ))
    (hB : SupportedPostBudget A pk m st c k B) :
    (∑ ξ∈T, w*signedAverage m c k none (fun _ d => noneSuccessLoss A ξ m st d)) ≤
      (∑ ξ∈T, w*ind (Spr c ξ))*signedMass m c k none +
      (authRate*sumW (fiberA pk)*B)*signedMass m c k none := by
  rw [← signedAverage_weighted_sum]
  calc
    _ ≤ signedAverage m c k none (fun _ d => (∑ ξ∈T, w*ind (Spr c ξ)) +
        authRate*(∑ ξ∈fiberA pk, w*noneOtherCost A ξ m st d)) := by
      apply signedAverage_mono_support
      intro g p hp _
      exact none_fiber_leaf A pk T hT m st c p.2
        (preloaded_loop_indexExtension WeightedSchedule.decode WeightedSchedule.tier m k c g p hp) hTc
    _ = (∑ ξ∈T, w*ind (Spr c ξ))*signedMass m c k none +
        signedAverage m c k none (fun _ d => authRate*(∑ ξ∈fiberA pk, w*noneOtherCost A ξ m st d)) := by
      rw [signedAverage_add,signedAverage_const]
    _ ≤ _ := add_le_add le_rfl (none_cost_budget A pk m st c k B hB)

#print axioms none_fiber_leaf
#print axioms signed_none_master
end OptimalOTS.WeightedConstruction.WideForest
