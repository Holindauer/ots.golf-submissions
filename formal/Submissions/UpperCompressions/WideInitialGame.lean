import Submissions.UpperCompressions.SignedGameBridge
import Submissions.UpperCompressions.WeightedReserve

/-! Actual mixed72 keygen and adaptive message-choice decomposition. The
reduced choose run starts with an empty public cache; hidden graph points are
removed by the checked identical-until-bad coupling. -/
open OracleSpec OracleComp OracleComp.EvalDist ENNReal
noncomputable section
open scoped Classical BigOperators
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
namespace OptimalOTS.WeightedConstruction.WideInitialGame
open OptimalOTS.Dag WideForest WideForest.Name WeightedReplacement WeightedSampling
attribute [local irreducible] Finset.univ Finset.filter CostAtMost
attribute [local irreducible] WeightedResearch92.classes
variable (A : forestScheme.toAlgorithm.Adversary)

def afterChoose (pk : PublicKey) (sk : forestScheme.graph.Assignment) (x : Message × A.State) : OracleComp Spec Bool :=
  forestScheme.sign sk x.1 >>= stB A pk x.1 x.2

def afterKeygen (p : PublicKey × forestScheme.graph.Assignment) : OracleComp Spec Bool :=
  A.choose p.1 >>= afterChoose A p.1 p.2

theorem experiment_eq : forestScheme.toAlgorithm.experiment A =
    forestScheme.keygen >>= afterKeygen A := by
  unfold TypedScheme.experiment afterKeygen afterChoose stB
  apply bind_congr
  rintro ⟨pk,sk⟩
  apply bind_congr
  rintro ⟨m,st⟩
  apply bind_congr
  intro σ
  apply bind_congr
  rintro ⟨m₂,σ₂⟩
  apply bind_congr
  intro ok
  congr 1
  by_cases h : σ.map (fun s => (m,s)) ≠ some (m₂,σ₂)
  · simp [h]
    intro _
    exact h
  · simp [h]
    intro _
    exact not_not.mp h

theorem publicKey_record (ξ : Rec) : forestScheme.publicKey (graph.evalRec ξ) = pkOf ξ := by
  change lowPk (graph.evalRec ξ graph.root) = lowPk (ξ.2 rh.fin)
  rw [← val_rh ξ]
  unfold val
  exact (lowPk_cast_eq (graph_len_fin rh) (graph.evalRec ξ rh.fin)).symm


theorem E_keygen (F : (PublicKey × forestScheme.graph.Assignment) × Cache → ℝ≥0∞) :
    E (run forestScheme.keygen ∅) F = ∑ ξ : Rec, w*F ((pkOf ξ,graph.evalRec ξ),kc ξ) := by
  rw [WeightedScheme.Scheme.keygen, GraphKeygenBridge.E_run_keygen forestScheme.graph forestScheme.publicKey tagging F]
  change (∑ ξ : Rec, w*F ((forestScheme.publicKey (graph.evalRec ξ),graph.evalRec ξ),kc ξ)) = _
  apply Finset.sum_congr rfl
  intro ξ _
  rw [publicKey_record]

theorem E_experiment (F : Bool × Cache → ℝ≥0∞) :
    E (run (forestScheme.toAlgorithm.experiment A) ∅) F =
      ∑ ξ : Rec, w*E (run (afterKeygen A (pkOf ξ,graph.evalRec ξ)) (kc ξ)) F := by
  rw [experiment_eq,run_bind,E_bind,E_keygen]

theorem keygen_remaining {B : ℕ}
    (hB : CostAtMost (forestScheme.toAlgorithm.experiment A) B) :
    995 ≤ B ∧ ∀ ξ : Rec,
      CostAtMost (afterKeygen A (pkOf ξ,graph.evalRec ξ)) (B-995) := by
  rw [experiment_eq,WeightedScheme.Scheme.keygen] at hB
  obtain ⟨hc,hr⟩ := GraphKeygenBridge.costAtMost_keygen_bind forestScheme.graph forestScheme.publicKey (afterKeygen A) hB
  rw [forestScheme_keygenCost] at hc hr
  refine ⟨hc,fun ξ => ?_⟩
  have hh := hr ξ
  change CostAtMost (afterKeygen A (forestScheme.publicKey (graph.evalRec ξ),graph.evalRec ξ)) (B-995) at hh
  rwa [publicKey_record] at hh

theorem afterChoose_loop (pk : PublicKey) (ξ : Rec) (x : Message × A.State) :
    afterChoose A pk (graph.evalRec ξ) x =
      loop 86 WeightedSchedule.decode WeightedSchedule.tier x.1 signBudget >>=
        fun r => stB A pk x.1 x.2 (signatureFromWinner ξ r) := by
  unfold afterChoose WeightedScheme.Scheme.sign
  rw [bind_map_left]
  rfl

theorem afterChoose_extend (pk : PublicKey) (ξ : Rec) (x : Message × A.State) (d : Cache) :
    E (run (afterChoose A pk (graph.evalRec ξ) x) (Cache.extend d (kc ξ))) successValue =
      E (run (loop 86 WeightedSchedule.decode WeightedSchedule.tier x.1 signBudget) d)
        (fun p => E (run (stB A pk x.1 x.2 (signatureFromWinner ξ p.1))
          (Cache.extend p.2 (kc ξ))) successValue) := by
  rw [afterChoose_loop,run_bind,run_loop_extend 86 WeightedSchedule.decode WeightedSchedule.tier x.1 (kc ξ) (fun η => kc_enc ξ (x.1,η)) signBudget d,
    bind_map_left,E_bind]

theorem stageA_iub (ξ : Rec) :
    E (run (afterKeygen A (pkOf ξ,graph.evalRec ξ)) (kc ξ)) successValue ≤
      E (run (A.choose (pkOf ξ)) ∅) (fun p => if Cache.Hits p.2 (kc ξ) then 1 else
        E (run (afterChoose A (pkOf ξ) (graph.evalRec ξ) p.1) (Cache.extend p.2 (kc ξ))) successValue) := by
  unfold afterKeygen
  rw [run_bind,E_bind]
  have h := iub (A.choose (pkOf ξ)) (kc ξ)
    (fun p => E (run (afterChoose A (pkOf ξ) (graph.evalRec ξ) p.1) p.2) successValue)
    (fun p => E_le_one _ successValue_le_one) ∅ (fun _ _ => rfl)
  rw [Cache.empty_extend] at h
  exact h

theorem regroup (G : Rec → (Message × A.State) × Cache → ℝ≥0∞) :
    (∑ ξ : Rec, w*E (run (A.choose (pkOf ξ)) ∅) (G ξ)) =
      ∑ pk : PublicKey, E (run (A.choose pk) ∅)
        (fun p => ∑ ξ ∈ fiberA pk, w*G ξ p) := by
  symm
  calc
    _ = ∑ pk : PublicKey, ∑ ξ ∈ fiberA pk, w*E (run (A.choose (pkOf ξ)) ∅) (G ξ) := by
      apply Finset.sum_congr rfl
      intro pk _
      rw [E_finsetSum]
      apply Finset.sum_congr rfl
      intro ξ hξ
      have hpk : pkOf ξ = pk := pkOf_of_subset_fiberA (Finset.Subset.refl _) ξ hξ
      rw [hpk]
      exact (E_const_mul _ _ _).symm
    _ = _ := by
      unfold fiberA
      exact Finset.sum_fiberwise Finset.univ pkOf _

def conditional (pk : PublicKey) (x : Message × A.State) (d : Cache) : ℝ≥0∞ :=
  ∑ ξ ∈ fiberA pk, w * (if Cache.Hits d (kc ξ) then 0 else
    E (run (afterChoose A pk (graph.evalRec ξ) x) (Cache.extend d (kc ξ))) successValue)

/-- The actual global success decomposes into pre-sign graph authentication
cost and the record-weighted actual conditional sign/post experiment. -/
theorem global_reduced (isIndex : Spec.Domain → Prop)
    (hindex : ∀ q, isIndex (.inr q) → ∃ u : WideForest.EncInput, q=WideForest.encQuery u) :
    E (run (forestScheme.toAlgorithm.experiment A) ∅) successValue ≤
      (∑ pk : PublicKey, (authRate*sumW (fiberA pk))*
        expectedCharge (otherPaid isIndex) (A.choose pk) ∅) +
      ∑ pk : PublicKey, E (run (A.choose pk) ∅) (fun p => conditional A pk p.1 p.2) := by
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
    _ ≤ ∑ pk : PublicKey, ((authRate*sumW (fiberA pk))*
        expectedCharge (otherPaid isIndex) (A.choose pk) ∅ +
        E (run (A.choose pk) ∅) (fun p => conditional A pk p.1 p.2)) := by
      apply Finset.sum_le_sum
      intro pk _
      calc
        _ ≤ E (run (A.choose pk) ∅) (fun p => authPotential (fiberA pk) none p.2 +
            conditional A pk p.1 p.2) := by
          apply E_mono
          intro p
          unfold conditional authPotential
          simp only [← Finset.sum_add_distrib]
          apply Finset.sum_le_sum
          intro ξ hξ
          have hpk : pkOf ξ = pk := pkOf_of_subset_fiberA (Finset.Subset.refl _) ξ hξ
          rw [hpk,fHid_none]
          by_cases hh : Cache.Hits p.2 (kc ξ)
          · simp only [if_pos hh,ind_of hh,mul_zero,add_zero]
            exact mul_le_mul' le_rfl (le_add_right (le_refl (1:ℝ≥0∞)))
          · simp only [if_neg hh,ind_not hh,zero_add]
            exact le_add_of_nonneg_left (bot_le : (0:ℝ≥0∞) ≤ _)
        _ = E (run (A.choose pk) ∅) (fun p => authPotential (fiberA pk) none p.2) +
            E (run (A.choose pk) ∅) (fun p => conditional A pk p.1 p.2) := expectedValue_add _ _ _
        _ ≤ _ := add_le_add (stageA_auth_expected A pk isIndex hindex) le_rfl
    _ = _ := Finset.sum_add_distrib

#print axioms E_experiment
#print axioms keygen_remaining
#print axioms global_reduced
end OptimalOTS.WeightedConstruction.WideInitialGame
