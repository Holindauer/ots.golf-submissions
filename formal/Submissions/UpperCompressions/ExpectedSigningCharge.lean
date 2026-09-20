import Submissions.UpperCompressions.ExpectedChargeTower
import Submissions.UpperCompressions.WeightedScheme

/-! The concrete all-L signer spends no non-index paid cost. Combining public
phases across it preserves exactly the non-index clock used by authentication. -/
open OracleSpec OracleComp OracleComp.EvalDist ENNReal
noncomputable section
open scoped Classical
namespace WeightedReplacement
open OptimalOTS OptimalOTS.WeightedSampling
set_option maxHeartbeats 800000
attribute [local irreducible] hashBits blockBits msgBits signBudget

theorem otherPaid_le_queryCost (isIndex : Spec.Domain → Prop) (t : Spec.Domain) :
    otherPaid isIndex t ≤ queryCost t := by
  unfold otherPaid
  split_ifs <;> simp

theorem expectedCharge_other_private {α : Type} (isIndex : Spec.Domain → Prop)
    (oa : ProbComp α) (c : Cache) :
    expectedCharge (otherPaid isIndex) (liftM oa : OracleComp Spec α) c = 0 := by
  apply le_antisymm _ zero_le
  have h := expectedCharge_budget (otherPaid isIndex) 1
    (fun t => by simpa only [one_mul] using otherPaid_le_queryCost isIndex t)
    (liftM oa : OracleComp Spec α) 0 (AlgorithmCosts.costAtMost_liftM_probComp oa 0) c
  simpa only [Nat.cast_zero, mul_zero] using h

theorem expectedCharge_other_hash {n : ℕ} (isIndex : Spec.Domain → Prop)
    (x : BitVec n) (hx : isIndex (.inr ⟨n,x⟩)) (c : Cache) :
    expectedCharge (otherPaid isIndex) (hash x) c = 0 := by
  have h := expectedCharge_query (otherPaid isIndex) (.inr ⟨n,x⟩)
    (fun u => pure u) c
  simpa only [OptimalOTS.hash, bind_pure, expectedCharge_pure, E, expectedValue_def, mul_zero,
    tsum_zero, add_zero, otherPaid, if_pos hx] using h

theorem loop_otherPaid_zero {M : ℕ} (n : ℕ)
    (decode : BitVec hashBits → Option (Fin M)) (tier : Fin M → ℕ) (m : Message)
    (isIndex : Spec.Domain → Prop)
    (hi : ∀ η : Nonce n, isIndex (.inr ⟨msgBits+n,m++η⟩)) :
    ∀ k c, expectedCharge (otherPaid isIndex) (loop n decode tier m k) c = 0 := by
  intro k
  induction k with
  | zero => intro c; simp [loop]
  | succ k ih =>
    intro c
    rw [loop, expectedCharge_bind]
    rw [show expectedCharge (otherPaid isIndex) (sampleBits n) c = 0 from
      expectedCharge_other_private isIndex _ c]
    simp only [zero_add]
    have hpoint (p : Nonce n × Cache) :
        expectedCharge (otherPaid isIndex)
          (hash (m++p.1) >>= fun u => loop n decode tier m k >>= fun r =>
            pure (best (fun r => tier r.2) (candidate decode p.1 u) r)) p.2 = 0 := by
      rw [expectedCharge_bind, expectedCharge_other_hash isIndex _ (hi p.1)]
      simp only [expectedCharge_bind_pure, ih, E, expectedValue_def, mul_zero,
        tsum_zero, add_zero]
    simp_rw [hpoint]
    simp [E, expectedValue_def]

/-- All accepted nonwinning queries of the actual signer are included. They
are paid index queries and therefore do not consume the graph charge clock. -/
theorem sign_otherPaid_zero {M : ℕ} (S : WeightedScheme.Scheme M)
    (x : S.graph.Assignment) (m : Message) (c : Cache)
    (isIndex : Spec.Domain → Prop)
    (hi : ∀ η : Nonce 86, isIndex (.inr ⟨msgBits+86,m++η⟩)) :
    expectedCharge (otherPaid isIndex) (S.sign x m) c = 0 := by
  rw [WeightedScheme.Scheme.sign, expectedCharge_map]
  exact loop_otherPaid_zero 86 S.decode S.tier m isIndex hi signBudget c

theorem sign_post_otherPaid {M : ℕ} {α : Type} (S : WeightedScheme.Scheme M)
    (x : S.graph.Assignment) (m : Message) (c : Cache)
    (isIndex : Spec.Domain → Prop)
    (hi : ∀ η : Nonce 86, isIndex (.inr ⟨msgBits+86,m++η⟩))
    (post : Option WeightedScheme.Signature → OracleComp Spec α) :
    expectedCharge (otherPaid isIndex) (S.sign x m >>= post) c =
      E (run (S.sign x m) c) (fun p => expectedCharge (otherPaid isIndex) (post p.1) p.2) := by
  rw [expectedCharge_bind, sign_otherPaid_zero S x m c isIndex hi, zero_add]

#print axioms loop_otherPaid_zero
#print axioms sign_otherPaid_zero
#print axioms sign_post_otherPaid
end WeightedReplacement
