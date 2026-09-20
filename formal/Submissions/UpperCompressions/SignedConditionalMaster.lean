import Submissions.UpperCompressions.SignedNoneMaster

/-! The common conditional game-to-payoff master, including actual signing
failure and every supported signed outcome. Replay and excess retain the actual
completed-table signer law, ready for the concrete empirical/hazard bounds. -/
open OracleSpec OracleComp OracleComp.EvalDist ENNReal
noncomputable section
open scoped Classical
set_option maxRecDepth 10000
namespace OptimalOTS.WeightedConstruction.WideForest
open OptimalOTS.Dag Name WeightedReplacement WeightedSampling
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Finset.univ Finset.filter

def winnerReplay (c : Cache) (m : Message) : SignedWinner → ℝ≥0∞
  | none => 0
  | some (η,i) => ind (AlternateClass c (m,η) i)

def winnerExcess : SignedWinner → ℝ≥0∞
  | none => 0
  | some (_,i) => ENNReal.ofReal (WeightedSchedule.excess i)

def signerAverage (m : Message) (c : Cache) (k : ℕ) (F : SignedWinner → ℝ≥0∞) : ℝ≥0∞ :=
  E ($ᵗ IndexTable) (fun g => E (run (loop 86 WeightedSchedule.decode WeightedSchedule.tier m k)
    ((lengthSlice (msgBits+86)).preload c g)) (fun p => F p.1))

def outcomeSuccessLoss (A : forestScheme.toAlgorithm.Adversary) (ξ : Rec)
    (m : Message) (st : A.State) (b : SignedWinner) (d : Cache) : ℝ≥0∞ :=
  E (run (stBWithForgery A (pkOf ξ) m st (signatureFromWinner ξ b))
    (Cache.extend d (kc ξ))) forgerySuccess

def conditionalGame (A : forestScheme.toAlgorithm.Adversary) (T : Finset Rec)
    (m : Message) (st : A.State) (c : Cache) (k : ℕ) : ℝ≥0∞ :=
  ∑ ξ∈T, w*E ($ᵗ IndexTable) (fun g =>
    E (run (loop 86 WeightedSchedule.decode WeightedSchedule.tier m k)
      ((lengthSlice (msgBits+86)).preload c g))
      (fun p => outcomeSuccessLoss A ξ m st p.1 p.2))

theorem signedAverage_partition (m : Message) (c : Cache) (k : ℕ)
    (F : SignedWinner → IndexTable → Cache → ℝ≥0∞) :
    (∑ b : SignedWinner, signedAverage m c k b (F b)) =
      E ($ᵗ IndexTable) (fun g => E (run (loop 86 WeightedSchedule.decode WeightedSchedule.tier m k)
        ((lengthSlice (msgBits+86)).preload c g)) (fun p => F p.1 g p.2)) := by
  let trial (g : IndexTable) := run (loop 86 WeightedSchedule.decode WeightedSchedule.tier m k)
    ((lengthSlice (msgBits+86)).preload c g)
  let latent : ProbComp IndexTable := $ᵗ IndexTable
  change (∑ b : SignedWinner, E latent (fun g => E (trial g)
    (fun p => if p.1=b then F b g p.2 else 0))) =
      E latent (fun g => E (trial g) (fun p => F p.1 g p.2))
  rw [← E_finsetSum]
  congr 1
  funext g
  rw [← E_finsetSum]
  congr 1
  funext p
  simp

theorem signedMass_weighted_sum (m : Message) (c : Cache) (k : ℕ)
    (F : SignedWinner → ℝ≥0∞) :
    (∑ b : SignedWinner, F b*signedMass m c k b) = signerAverage m c k F := by
  simp_rw [← signedAverage_const]
  exact signedAverage_partition m c k (fun b _ _ => F b)

theorem signedMass_sum_le (m : Message) (c : Cache) (k : ℕ) :
    (∑ b : SignedWinner, signedMass m c k b) ≤ 1 := by
  have h := signedMass_weighted_sum m c k (fun _ => 1)
  simp only [one_mul] at h
  rw [h]
  exact (E_mono _ (fun _ => E_const_le _ 1)).trans (E_const_le _ 1)

theorem conditionalGame_partition (A : forestScheme.toAlgorithm.Adversary)
    (T : Finset Rec) (m : Message) (st : A.State) (c : Cache) (k : ℕ) :
    conditionalGame A T m st c k =
      ∑ b : SignedWinner, ∑ ξ∈T, w*signedAverage m c k b (fun _ d => outcomeSuccessLoss A ξ m st b d) := by
  unfold conditionalGame
  calc
    _ = ∑ ξ∈T, w*(∑ b : SignedWinner,
        signedAverage m c k b (fun _ d => outcomeSuccessLoss A ξ m st b d)) := by
      apply Finset.sum_congr rfl
      intro ξ _
      exact congrArg (w*·) (signedAverage_partition m c k (fun b _ d => outcomeSuccessLoss A ξ m st b d)).symm
    _ = _ := by simp only [Finset.mul_sum]; rw [Finset.sum_comm]

theorem authRate_ofReal : authRate = ENNReal.ofReal (WeightedReference.kappa/2) := by
  unfold authRate WeightedReference.kappa
  rw [ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ)<2),
    ENNReal.ofReal_div_of_pos (by positivity : (0:ℝ)<2^127)]
  norm_num

theorem max_posterior_auth_le (i : Fin WeightedSchedule.M) :
    max (posteriorRate i) authRate ≤ authRate+ENNReal.ofReal (WeightedSchedule.excess i) := by
  apply max_le
  · rw [authRate_ofReal]
    exact concrete_posterior_rate_ennreal_base_excess i
  · exact le_self_add

theorem signed_outcome_master (A : forestScheme.toAlgorithm.Adversary) (pk : BitVec 128)
    (T : Finset Rec) (hT : T ⊆ fiberA pk) (m : Message) (st : A.State)
    (c : Cache) (k B : ℕ) (hTc : ∀ ξ∈T, ¬ Cache.Hits c (kc ξ))
    (hB : SupportedPostBudget A pk m st c k B) (b : SignedWinner) :
    (∑ ξ∈T, w*signedAverage m c k b (fun _ d => outcomeSuccessLoss A ξ m st b d)) ≤
      ((∑ ξ∈T, w*ind (Spr c ξ)) + sumW T*winnerReplay c m b +
        (sumW (fiberA pk)*B)*(authRate+winnerExcess b))*signedMass m c k b := by
  cases b with
  | none =>
    have h := signed_none_master A pk T hT m st c k B hTc hB
    change (∑ ξ∈T, w*signedAverage m c k none (fun _ d => noneSuccessLoss A ξ m st d)) ≤ _
    refine h.trans_eq ?_
    simp only [winnerReplay,winnerExcess,mul_zero,add_zero]
    ring
  | some b =>
    rcases b with ⟨η,i⟩
    have h := signed_winner_master A pk T hT m st c k B η i hTc hB
    change (∑ ξ∈T, w*signedAverage m c k (some (η,i)) (fun _ d => successLoss A ξ m st η i d)) ≤ _
    refine h.trans ?_
    rw [signedAverage_const]
    calc
      _ ≤ (∑ ξ∈T, w*ind (Spr c ξ))*signedMass m c k (some (η,i)) +
          sumW T*(ind (AlternateClass c (m,η) i)*signedMass m c k (some (η,i))) +
          ((authRate+ENNReal.ofReal (WeightedSchedule.excess i))*sumW (fiberA pk)*B)*
            signedMass m c k (some (η,i)) := by
        gcongr
        exact max_posterior_auth_le i
      _ = _ := by simp only [winnerReplay,winnerExcess]; ring

/-- The actual conditional sign/forge/verify game, including signing failure,
is bounded by surviving pre-sign spurious mass plus replay and expected class
excess of the same all-L signer. The base graph/index cost is spent once.
Only supported remaining budgets and the pre-sign no-hit record filter remain. -/
theorem conditional_game_master (A : forestScheme.toAlgorithm.Adversary) (pk : BitVec 128)
    (T : Finset Rec) (hT : T ⊆ fiberA pk) (m : Message) (st : A.State)
    (c : Cache) (k B : ℕ) (hTc : ∀ ξ∈T, ¬ Cache.Hits c (kc ξ))
    (hB : SupportedPostBudget A pk m st c k B) :
    conditionalGame A T m st c k ≤
      (∑ ξ∈T, w*ind (Spr c ξ)) + sumW (fiberA pk) *
        (signerAverage m c k (winnerReplay c m) +
          B*(authRate+signerAverage m c k winnerExcess)) := by
  rw [conditionalGame_partition]
  let P := ∑ ξ∈T, w*ind (Spr c ξ)
  let Z := sumW (fiberA pk)*(B:ℝ≥0∞)
  calc
    _ ≤ ∑ b : SignedWinner, (P+sumW T*winnerReplay c m b+Z*(authRate+winnerExcess b))*
        signedMass m c k b := Finset.sum_le_sum fun b _ =>
      signed_outcome_master A pk T hT m st c k B hTc hB b
    _ = P*(∑ b : SignedWinner, signedMass m c k b) +
        sumW T*(∑ b : SignedWinner, winnerReplay c m b*signedMass m c k b) +
        Z*(authRate*(∑ b : SignedWinner, signedMass m c k b) +
          ∑ b : SignedWinner, winnerExcess b*signedMass m c k b) := by
      simp only [Finset.mul_sum,Finset.sum_add_distrib]
      simp only [← Finset.sum_add_distrib]
      rw [Finset.mul_sum,← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun b _ => by ring
    _ ≤ P*1 + sumW T*(∑ b : SignedWinner, winnerReplay c m b*signedMass m c k b) +
        Z*(authRate*1+∑ b : SignedWinner, winnerExcess b*signedMass m c k b) := by
      gcongr <;> exact signedMass_sum_le m c k
    _ = P+sumW T*signerAverage m c k (winnerReplay c m)+Z*(authRate+signerAverage m c k winnerExcess) := by
      rw [mul_one,mul_one,signedMass_weighted_sum,signedMass_weighted_sum]
    _ ≤ P+sumW (fiberA pk)*signerAverage m c k (winnerReplay c m)+
        Z*(authRate+signerAverage m c k winnerExcess) := by
      gcongr
      exact sumW_mono hT
    _ = _ := by dsimp only [P,Z]; ring

#print axioms conditionalGame_partition
#print axioms authRate_ofReal
#print axioms conditional_game_master
end OptimalOTS.WeightedConstruction.WideForest
