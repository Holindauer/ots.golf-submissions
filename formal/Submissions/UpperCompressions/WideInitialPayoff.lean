import Submissions.UpperCompressions.WideInitialBudget

/-! Sharp initial authentication accounting: the surviving pre-sign Spr term
is absorbed together with the stageA hit event exactly once. -/
open OracleSpec OracleComp OracleComp.EvalDist ENNReal
noncomputable section
open scoped Classical BigOperators
set_option maxRecDepth 10000
set_option maxHeartbeats 800000
namespace OptimalOTS.WeightedConstruction.WideInitialGame
open OptimalOTS.Dag WideForest WideForest.Name WeightedReplacement
attribute [local irreducible] Finset.univ Finset.filter WeightedResearch92.classes
variable (A : forestScheme.toAlgorithm.Adversary)

def hitMass (pk : PublicKey) (d : Cache) : ℝ≥0∞ :=
  ∑ ξ ∈ fiberA pk, w*ind (Cache.Hits d (kc ξ))

def survivingSpr (pk : PublicKey) (d : Cache) : ℝ≥0∞ :=
  ∑ ξ ∈ (fiberA pk).filter (fun ξ => ¬ Cache.Hits d (kc ξ)), w*ind (Spr d ξ)

theorem hit_survivingSpr_le_auth (pk : PublicKey) (d : Cache) :
    hitMass pk d + survivingSpr pk d ≤ authPotential (fiberA pk) none d := by
  have hs : survivingSpr pk d ≤ ∑ ξ ∈ fiberA pk, w*ind (Spr d ξ) :=
    Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
  refine (add_le_add le_rfl hs).trans_eq ?_
  simp only [hitMass,authPotential,fHid_none,mul_add,Finset.sum_add_distrib]

theorem global_reduced_hits :
    E (run (forestScheme.toAlgorithm.experiment A) ∅) successValue ≤
      ∑ pk : PublicKey, E (run (A.choose pk) ∅)
        (fun p => hitMass pk p.2 + conditional A pk p.1 p.2) := by
  rw [E_experiment]
  calc
    _ ≤ ∑ ξ : Rec, w*E (run (A.choose (pkOf ξ)) ∅) (fun p =>
        if Cache.Hits p.2 (kc ξ) then 1 else
          E (run (afterChoose A (pkOf ξ) (graph.evalRec ξ) p.1)
            (Cache.extend p.2 (kc ξ))) successValue) :=
      Finset.sum_le_sum fun ξ _ => mul_le_mul' le_rfl (stageA_iub A ξ)
    _ = ∑ pk : PublicKey, E (run (A.choose pk) ∅) (fun p =>
        ∑ ξ ∈ fiberA pk, w*(if Cache.Hits p.2 (kc ξ) then 1 else
          E (run (afterChoose A (pkOf ξ) (graph.evalRec ξ) p.1)
            (Cache.extend p.2 (kc ξ))) successValue)) := regroup A _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro pk _
      congr 1
      funext p
      unfold hitMass conditional
      simp only [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro ξ hξ
      rw [pkOf_of_subset_fiberA (Finset.Subset.refl _) ξ hξ]
      by_cases hh : Cache.Hits p.2 (kc ξ) <;> simp [hh,ind]

theorem global_reduced_hits_clock (b : ℕ) :
    E (run (forestScheme.toAlgorithm.experiment A) ∅) successValue ≤
      ∑ pk : PublicKey, E (runRemaining (A.choose pk) ∅ b)
        (fun r => hitMass pk r.2.1 + conditional A pk r.1 r.2.1) := by
  have h := global_reduced_hits A
  have he (pk : PublicKey) :
      E (run (A.choose pk) ∅) (fun p => hitMass pk p.2 + conditional A pk p.1 p.2) =
      E (runRemaining (A.choose pk) ∅ b) (fun r => hitMass pk r.2.1 + conditional A pk r.1 r.2.1) := by
    rw [← runRemaining_project (A.choose pk) ∅ b,E_map]
  simp_rw [he] at h
  exact h

/-- A supported conditional sign/post bound carrying the surviving pre-Spr
term lifts to the global game, charging pre-sign authentication only once. -/
theorem global_payoff_clock (b : ℕ) (isIndex : Spec.Domain → Prop)
    (hindex : ∀ q, isIndex (.inr q) → ∃ u : WideForest.EncInput, q=WideForest.encQuery u)
    (payoff : PublicKey → ((Message × A.State) × Cache × ℕ) → ℝ≥0∞)
    (hpay : ∀ pk r, r ∈ support (runRemaining (A.choose pk) ∅ b) →
      conditional A pk r.1 r.2.1 ≤ survivingSpr pk r.2.1 + payoff pk r) :
    E (run (forestScheme.toAlgorithm.experiment A) ∅) successValue ≤
      (∑ pk : PublicKey, (authRate*sumW (fiberA pk))*
        expectedCharge (otherPaid isIndex) (A.choose pk) ∅) +
      ∑ pk : PublicKey, E (runRemaining (A.choose pk) ∅ b) (payoff pk) := by
  refine (global_reduced_hits_clock A b).trans ?_
  calc
    _ ≤ ∑ pk : PublicKey, E (runRemaining (A.choose pk) ∅ b)
        (fun r => authPotential (fiberA pk) none r.2.1 + payoff pk r) := by
      apply Finset.sum_le_sum
      intro pk _
      apply expectedValue_mono_of_support
      intro r hr
      calc
        _ ≤ hitMass pk r.2.1 + (survivingSpr pk r.2.1 + payoff pk r) := add_le_add le_rfl (hpay pk r hr)
        _ ≤ _ := by rw [← add_assoc]; exact add_le_add (hit_survivingSpr_le_auth pk r.2.1) le_rfl
    _ = ∑ pk : PublicKey, (E (run (A.choose pk) ∅) (fun p => authPotential (fiberA pk) none p.2) +
        E (runRemaining (A.choose pk) ∅ b) (payoff pk)) := by
      apply Finset.sum_congr rfl
      intro pk _
      calc
        _ = E (runRemaining (A.choose pk) ∅ b) (fun r => authPotential (fiberA pk) none r.2.1) +
            E (runRemaining (A.choose pk) ∅ b) (payoff pk) := expectedValue_add _ _ _
        _ = _ := by rw [← runRemaining_project (A.choose pk) ∅ b,E_map]
    _ ≤ ∑ pk : PublicKey, ((authRate*sumW (fiberA pk))*
        expectedCharge (otherPaid isIndex) (A.choose pk) ∅ +
        E (runRemaining (A.choose pk) ∅ b) (payoff pk)) :=
      Finset.sum_le_sum fun pk _ => add_le_add (stageA_auth_expected A pk isIndex hindex) le_rfl
    _ = _ := Finset.sum_add_distrib

#print axioms global_reduced_hits
#print axioms global_payoff_clock
end OptimalOTS.WeightedConstruction.WideInitialGame
