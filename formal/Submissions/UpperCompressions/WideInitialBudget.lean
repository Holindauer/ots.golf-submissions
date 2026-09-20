import Submissions.UpperCompressions.WideInitialGame
import Submissions.UpperCompressions.ReplacementSupportReserve

/-! Pathwise budgets for the actual reduced adaptive choose run and all-L
signer. Only supported actual signer outcomes need continuation budgets. -/
open OracleSpec OracleComp OracleComp.EvalDist ENNReal
noncomputable section
open scoped Classical
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
namespace OptimalOTS.WeightedConstruction.WideInitialGame
open OptimalOTS.Dag WideForest WideForest.Name WeightedReplacement WeightedSampling
attribute [local irreducible] Finset.univ Finset.filter graph CostAtMost WeightedResearch92.classes
variable (A : forestScheme.toAlgorithm.Adversary)

theorem fiber_nonempty (pk : PublicKey) : (fiberA pk).Nonempty := by
  refine ⟨(fun _ => 0, fun _ => pk.setWidth 256), ?_⟩
  simp only [fiberA,Finset.mem_filter,Finset.mem_univ,true_and]
  show lowPk (pk.setWidth 256) = pk
  rw [lowPk,BitVec.setWidth_setWidth_of_le _ (by norm_num [pkBits])]
  exact BitVec.setWidth_eq pk

theorem choose_remaining_support (pk : PublicKey) (b : ℕ)
    (hB : ∀ ξ ∈ fiberA pk, CostAtMost (afterKeygen A (pkOf ξ,graph.evalRec ξ)) b)
    (r : (Message × A.State) × Cache × ℕ)
    (hr : r ∈ support (runRemaining (A.choose pk) ∅ b)) :
    r.2.2 ≤ b ∧ ∀ ξ ∈ fiberA pk,
      CostAtMost (afterChoose A pk (graph.evalRec ξ) r.1) r.2.2 := by
  letI : Nonempty {ξ : Rec // ξ ∈ fiberA pk} := (fiber_nonempty pk).to_subtype
  have hb : ∀ j : {ξ : Rec // ξ ∈ fiberA pk},
      CostAtMost (A.choose pk >>= afterChoose A pk (graph.evalRec j.1)) b := by
    intro j
    have h := hB j.1 j.2
    have hpk := pkOf_of_subset_fiberA (Finset.Subset.refl _) j.1 j.2
    simpa only [afterKeygen,hpk] using h
  obtain ⟨hle,hk⟩ := runRemaining_family_support (A.choose pk)
    (fun j : {ξ : Rec // ξ ∈ fiberA pk} => afterChoose A pk (graph.evalRec j.1)) ∅ b hb r hr
  exact ⟨hle,fun ξ hξ => hk ⟨ξ,hξ⟩⟩

/-- After the actual choose output, every consistent supported signer return
leaves the same reserved L-subtracted budget for the retained-forgery program. -/
theorem choose_supported_sign_reserve (pk : PublicKey) (b : ℕ)
    (hB : ∀ ξ ∈ fiberA pk, CostAtMost (afterKeygen A (pkOf ξ,graph.evalRec ξ)) b)
    (r : (Message × A.State) × Cache × ℕ)
    (hr : r ∈ support (runRemaining (A.choose pk) ∅ b)) :
    signBudget ≤ r.2.2 ∧ r.2.2 ≤ b ∧
      ∀ ξ ∈ fiberA pk, ∀ c p,
        p ∈ support (run (loop 86 WeightedSchedule.decode WeightedSchedule.tier r.1.1 signBudget) c) →
        CostAtMost (stBWithForgery A pk r.1.1 r.1.2 (signatureFromWinner ξ p.1)) (r.2.2-signBudget) := by
  obtain ⟨hle,hk⟩ := choose_remaining_support A pk b hB r hr
  have hres (ξ : Rec) (hξ : ξ ∈ fiberA pk) := actual_loop_reserve 86
    WeightedSchedule.decode WeightedSchedule.tier r.1.1 index86_cost signBudget
    (fun s => stB A pk r.1.1 r.1.2 (signatureFromWinner ξ s)) r.2.2
    (by rw [← afterChoose_loop]; exact hk ξ hξ)
  obtain ⟨ξ₀,hξ₀⟩ := fiber_nonempty pk
  refine ⟨(hres ξ₀ hξ₀).1,hle,?_⟩
  intro ξ hξ c p hp
  have hh := (hres ξ hξ).2 c p hp
  rw [← stBWithForgery_map] at hh
  exact (AlgorithmCosts.costAtMost_map_iff _ _ _).1 hh

theorem experiment_choose_reserve {B : ℕ}
    (hB : CostAtMost (forestScheme.toAlgorithm.experiment A) B)
    (pk : PublicKey) (r : (Message × A.State) × Cache × ℕ)
    (hr : r ∈ support (runRemaining (A.choose pk) ∅ (B-995))) :
    signBudget ≤ r.2.2 ∧ r.2.2 ≤ B-995 ∧
      ∀ ξ ∈ fiberA pk, ∀ c p,
        p ∈ support (run (loop 86 WeightedSchedule.decode WeightedSchedule.tier r.1.1 signBudget) c) →
        CostAtMost (stBWithForgery A pk r.1.1 r.1.2 (signatureFromWinner ξ p.1)) (r.2.2-signBudget) :=
  choose_supported_sign_reserve A pk (B-995) (fun ξ _ => (keygen_remaining A hB).2 ξ) r hr

theorem choose_spent_remaining_le {B : ℕ}
    (hB : CostAtMost (forestScheme.toAlgorithm.experiment A) B) (pk : PublicKey) :
    expectedCharge (fun t => queryCost t) (A.choose pk) ∅ +
      E (runRemaining (A.choose pk) ∅ (B-995)) (fun r => (r.2.2:ℝ≥0∞)) ≤ (B-995:ℕ) := by
  letI : Nonempty {ξ : Rec // ξ ∈ fiberA pk} := (fiber_nonempty pk).to_subtype
  apply expected_spent_remaining_le (A.choose pk)
    (fun j : {ξ : Rec // ξ ∈ fiberA pk} => afterChoose A pk (graph.evalRec j.1)) ∅ (B-995)
  intro j
  have h := (keygen_remaining A hB).2 j.1
  have hpk := pkOf_of_subset_fiberA (Finset.Subset.refl _) j.1 j.2
  simpa only [afterKeygen,hpk] using h

/-- The same global factorization with the actual remaining budget retained
in the first-stage output, ready for a path-dependent continuation bound. -/
theorem global_reduced_clock (b : ℕ) (isIndex : Spec.Domain → Prop)
    (hindex : ∀ q, isIndex (.inr q) → ∃ u : WideForest.EncInput, q=WideForest.encQuery u) :
    E (run (forestScheme.toAlgorithm.experiment A) ∅) successValue ≤
      (∑ pk : PublicKey, (authRate*sumW (fiberA pk))*
        expectedCharge (otherPaid isIndex) (A.choose pk) ∅) +
      ∑ pk : PublicKey, E (runRemaining (A.choose pk) ∅ b)
        (fun r => conditional A pk r.1 r.2.1) := by
  have h := global_reduced A isIndex hindex
  have he (pk : PublicKey) : E (run (A.choose pk) ∅) (fun p => conditional A pk p.1 p.2) =
      E (runRemaining (A.choose pk) ∅ b) (fun r => conditional A pk r.1 r.2.1) := by
    rw [← runRemaining_project (A.choose pk) ∅ b,E_map]
  simp_rw [he] at h
  exact h

#print axioms global_reduced_clock
#print axioms choose_supported_sign_reserve
#print axioms experiment_choose_reserve
#print axioms choose_spent_remaining_le
end OptimalOTS.WeightedConstruction.WideInitialGame
