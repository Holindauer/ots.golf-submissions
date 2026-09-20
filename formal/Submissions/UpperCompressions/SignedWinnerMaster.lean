import Submissions.UpperCompressions.SignedAverage

/-! A concrete joint signed-winner game-to-payoff master. Query budgets are
required only at supported actual signer outcomes; impossible returned classes
never impose a continuation-budget premise. -/
open OracleSpec OracleComp OracleComp.EvalDist ENNReal
noncomputable section
open scoped Classical
set_option maxRecDepth 10000
namespace OptimalOTS.WeightedConstruction.WideForest
open OptimalOTS.Dag Name WeightedReplacement WeightedSampling
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Finset.univ Finset.filter

def signedMass (m : Message) (c : Cache) (k : ℕ) (b : SignedWinner) : ℝ≥0∞ :=
  signedAverage m c k b (fun _ _ => 1)

theorem signedAverage_const (m : Message) (c : Cache) (k : ℕ) (b : SignedWinner)
    (a : ℝ≥0∞) : signedAverage m c k b (fun _ _ => a) = a*signedMass m c k b := by
  simpa only [mul_one,signedMass] using signedAverage_const_mul m c k b a (fun _ _ => 1)

def SupportedPostBudget (A : forestScheme.toAlgorithm.Adversary) (pk : BitVec 128)
    (m : Message) (st : A.State) (c : Cache) (k B : ℕ) : Prop :=
  ∀ ξ∈fiberA pk, ∀ g p,
    p ∈ support (run (loop 86 WeightedSchedule.decode WeightedSchedule.tier m k)
      ((lengthSlice (msgBits+86)).preload c g)) →
    CostAtMost (stBWithForgery A (pkOf ξ) m st (signatureFromWinner ξ p.1)) B

def successLoss (A : forestScheme.toAlgorithm.Adversary) (ξ : Rec)
    (m : Message) (st : A.State) (η : Nonce 86) (i : Fin WeightedSchedule.M) (d : Cache) : ℝ≥0∞ :=
  E (run (fixedPost A ξ m st η i) (Cache.extend d (kc ξ))) forgerySuccess

theorem signed_leaf_average (A : forestScheme.toAlgorithm.Adversary) (ξ : Rec)
    (m : Message) (st : A.State) (c : Cache) (k : ℕ) (η : Nonce 86)
    (i : Fin WeightedSchedule.M) (hξ : ¬ Cache.Hits c (kc ξ)) :
    signedAverage m c k (some (η,i)) (fun _ d => successLoss A ξ m st η i d) ≤
      signedAverage m c k (some (η,i)) (fun _ d => graphLoss A ξ m st η i d) +
      signedAverage m c k (some (η,i)) (fun _ _ => ind (AlternateClass c (m,η) i)) +
      signedAverage m c k (some (η,i)) (freshLoss A ξ m st η i c) := by
  rw [← signedAverage_add, ← signedAverage_add]
  apply signedAverage_mono_support
  intro g p hp _
  exact signed_game_leaf A ξ i η m st c p.2 g
    (preloaded_loop_indexExtension WeightedSchedule.decode WeightedSchedule.tier m k c g p hp)
    hξ (sub_of_mem_support_run _ _ p hp)

theorem signed_cost_budget (A : forestScheme.toAlgorithm.Adversary) (pk : BitVec 128)
    (m : Message) (st : A.State) (c : Cache) (k B : ℕ) (η : Nonce 86)
    (i : Fin WeightedSchedule.M) (hB : SupportedPostBudget A pk m st c k B) :
    posteriorRate i * (∑ ξ∈fiberA pk, w*signedAverage m c k (some (η,i))
      (fun _ d => postCost A ξ m st η i (indexPaid (isIndexLength (msgBits+86))) d)) +
    authRate * (∑ ξ∈fiberA pk, w*signedAverage m c k (some (η,i))
      (fun _ d => postCost A ξ m st η i (otherPaid (isIndexLength (msgBits+86))) d)) ≤
      (max (posteriorRate i) authRate * sumW (fiberA pk) * B) * signedMass m c k (some (η,i)) := by
  rw [← signedAverage_weighted_sum, ← signedAverage_weighted_sum,
    ← signedAverage_const_mul, ← signedAverage_const_mul, ← signedAverage_add,
    ← signedAverage_const]
  apply signedAverage_mono_support
  intro g p hp hb
  have hcont : ∀ ξ∈fiberA pk,
      CostAtMost (fixedPost A ξ m st η i) B := by
    intro ξ hξ
    have h := hB ξ hξ g p hp
    simpa only [hb,signatureFromWinner,Option.map_some,fixedPost] using h
  have h := record_shared_paid_budget (setsName i) pk p.2 (isIndexLength (msgBits+86))
    (posteriorRate i) authRate
    (fun dt => stBWithForgery A dt.1 m st (some (η,dt.2.1))) B hcont
  exact h

/-- Conditional successful-signature master for a fixed returned nonce/class.
It contains the actual strong-success event, concrete posterior law, graph
resampling, and one supported continuation clock. Only the pre-sign record
filter and the actual residual budget are premises. -/
theorem signed_winner_master (A : forestScheme.toAlgorithm.Adversary) (pk : BitVec 128)
    (T : Finset Rec) (hT : T ⊆ fiberA pk)
    (m : Message) (st : A.State) (c : Cache) (k B : ℕ) (η : Nonce 86)
    (i : Fin WeightedSchedule.M) (hTc : ∀ ξ∈T, ¬ Cache.Hits c (kc ξ))
    (hB : SupportedPostBudget A pk m st c k B) :
    (∑ ξ∈T, w*signedAverage m c k (some (η,i)) (fun _ d => successLoss A ξ m st η i d)) ≤
      (∑ ξ∈T, w*ind (Spr c ξ))*signedMass m c k (some (η,i)) +
      sumW T * signedAverage m c k (some (η,i)) (fun _ _ => ind (AlternateClass c (m,η) i)) +
      (max (posteriorRate i) authRate * sumW (fiberA pk) * B)*signedMass m c k (some (η,i)) := by
  let G (ξ : Rec) := signedAverage m c k (some (η,i)) (fun _ d => graphLoss A ξ m st η i d)
  let F (ξ : Rec) := signedAverage m c k (some (η,i)) (freshLoss A ξ m st η i c)
  let CI (ξ : Rec) := signedAverage m c k (some (η,i))
    (fun _ d => postCost A ξ m st η i (indexPaid (isIndexLength (msgBits+86))) d)
  let CO (ξ : Rec) := signedAverage m c k (some (η,i))
    (fun _ d => postCost A ξ m st η i (otherPaid (isIndexLength (msgBits+86))) d)
  let R := signedAverage m c k (some (η,i)) (fun _ _ => ind (AlternateClass c (m,η) i))
  have hG : (∑ ξ∈T, w*G ξ) ≤
      (∑ ξ∈T, w*ind (Spr c ξ))*signedMass m c k (some (η,i)) +
        authRate*(∑ ξ∈fiberA pk, w*CO ξ) := by
    have h := signedAverage_graph_bound A pk T hT m st c k η i hTc
    rw [signedAverage_weighted_sum, signedAverage_add, signedAverage_const,
      signedAverage_const_mul, signedAverage_weighted_sum] at h
    exact h
  have hF : (∑ ξ∈T, w*F ξ) ≤ posteriorRate i*(∑ ξ∈fiberA pk, w*CI ξ) := by
    calc
      _ ≤ ∑ ξ∈T, w*(posteriorRate i*CI ξ) :=
        Finset.sum_le_sum fun ξ _ => mul_le_mul_right (signedAverage_fresh_bound A ξ m st c k η i) w
      _ = posteriorRate i*(∑ ξ∈T, w*CI ξ) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun _ _ => by ring
      _ ≤ _ := mul_le_mul_right (Finset.sum_le_sum_of_subset hT) (posteriorRate i)
  calc
    _ ≤ ∑ ξ∈T, w*(G ξ+R+F ξ) := Finset.sum_le_sum fun ξ hξ =>
      mul_le_mul_right (signed_leaf_average A ξ m st c k η i (hTc ξ hξ)) w
    _ = (∑ ξ∈T, w*G ξ)+sumW T*R+(∑ ξ∈T, w*F ξ) := by
      simp only [mul_add,Finset.sum_add_distrib,Finset.sum_mul,sumW]
    _ ≤ ((∑ ξ∈T, w*ind (Spr c ξ))*signedMass m c k (some (η,i)) +
        authRate*(∑ ξ∈fiberA pk, w*CO ξ))+sumW T*R+
        posteriorRate i*(∑ ξ∈fiberA pk, w*CI ξ) := add_le_add (add_le_add hG le_rfl) hF
    _ = (∑ ξ∈T, w*ind (Spr c ξ))*signedMass m c k (some (η,i)) + sumW T*R +
        (posteriorRate i*(∑ ξ∈fiberA pk, w*CI ξ)+authRate*(∑ ξ∈fiberA pk, w*CO ξ)) := by ring
    _ ≤ _ := add_le_add le_rfl (signed_cost_budget A pk m st c k B η i hB)

#print axioms signed_cost_budget
#print axioms signed_winner_master
end OptimalOTS.WeightedConstruction.WideForest
