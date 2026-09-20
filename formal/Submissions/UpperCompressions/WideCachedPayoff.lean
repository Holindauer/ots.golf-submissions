import Submissions.UpperCompressions.WideCachedRow
import Submissions.UpperCompressions.ReplacementConcreteCompletion

/-! Actual signing replay/excess bounds from the physical pre-sign cache.
The conditional table exception is explicit and is bounded only after averaging
under the actual adaptive execution. -/
noncomputable section
namespace OptimalOTS.WeightedConstruction.WideCachedRow
open OracleSpec OracleComp OracleComp.EvalDist
open WeightedSchedule WideDomains WideForest WideConcentration WeightedReference WeightedConstants
open WeightedReplacement WeightedCompletion WeightedCacheCounts
open scoped Classical ENNReal
set_option maxHeartbeats 1000000
attribute [local irreducible] Finset.univ Finset.filter

def tableFailure (m : Message) (c : Cache) : ℝ :=
  uniformMean (fun g : BitVec 342 → BitVec 256 =>
    if rowGood (decode ∘ cachedRow 86 m c g) then 0 else 1)

def replayScore (m : Message) (c : Cache) (η : BitVec 86) (i : Fin M) : ℝ :=
  if η ∈ exposed m c then (if 2 ≤ classCounts indexDomain c decode i then 1 else 0)
  else (if classCounts indexDomain c decode i=0 then 0 else 1)

theorem replayScore_nonneg (m : Message) (c : Cache) (η : BitVec 86) (i : Fin M) :
    0≤replayScore m c η i := by unfold replayScore; split_ifs <;> norm_num

theorem actual_replay_bound (m : Message) (c : Cache) :
    outE (WeightedSampling.loop 86 decode tier m L) c
      (fun s => ENNReal.ofReal (score s (fun r => replayScore m c r.1 r.2))) ≤
      ENNReal.ofReal ((99:ℝ)/98*securityWeights.hazard ((2:ℝ)^86)
        (seen (rowDomain m) c).card (classCounts indexDomain c decode)
        (classCounts (rowDomain m) c decode)+tableFailure m c) := by
  rw [actual_sign_payoff m c _ (replayScore_nonneg m c)]
  apply ENNReal.ofReal_le_ofReal
  have h := replay_kernel_bound securityWeights L tier (exposed m c) (fixed m c)
    (fun g : BitVec 342 → BitVec 256 => decode ∘ cachedRow 86 m c g)
    (classCounts indexDomain c decode) (cached_known m c) (cached_fresh_probability m c)
    (fun g => rowGood (decode ∘ cachedRow 86 m c g)) ((99:ℝ)/98) (tableFailure m c)
    (by norm_num) (fun g hg i => rowGood_kernel _ hg i) le_rfl
  rw [exposed_card,fixed_counts,Fintype.card_bitVec,Nat.cast_pow,Nat.cast_ofNat] at h
  exact h

theorem excess_le_one (i : Fin M) : excess i ≤ 1 := by
  have hp : classProbability i ≤ acceptance := by
    rw [← classProbability_sum]
    exact Finset.single_le_sum (fun j _ => (classProbability_pos j).le) (Finset.mem_univ i)
  have ha : 0<1-acceptance := by norm_num [acceptance]
  have hp' : classProbability i/(1-acceptance) ≤ 1 := by
    apply (div_le_iff₀ ha).mpr
    have hx : acceptance≤1-acceptance := by norm_num [acceptance]
    linarith
  unfold excess
  apply max_le
  · have hk : 0≤kappa := by norm_num [kappa]
    linarith
  · norm_num

theorem excess_score_identity (r : Fin M → ℕ) :
    (∑ i : Fin M,(r i:ℝ)*(referenceWeight i/classProbability i*excess i))=
      excessWeights.score r := by
  unfold WeightedRow.Weights.score
  apply Finset.sum_congr rfl
  intro i hi
  change (r i:ℝ)*(referenceWeight i/classProbability i*excess i)=
    (r i:ℝ)*(referenceWeight i*excess i/classProbability i)
  ring

theorem actual_excess_bound (m : Message) (c : Cache) (hc : WideEmpirical.Good c) :
    outE (WeightedSampling.loop 86 decode tier m L) c
      (fun s => ENNReal.ofReal (score s (fun r => excess r.2))) ≤
      ENNReal.ofReal ((99:ℝ)/98*(kappa*(2/5)+kappa/100)+tableFailure m c) := by
  rw [actual_sign_payoff m c (fun _ i => excess i) (fun _ i => le_max_right _ _)]
  apply ENNReal.ofReal_le_ofReal
  have h := excess_kernel_bound securityWeights L tier (exposed m c) (fixed m c)
    (fun g : BitVec 342 → BitVec 256 => decode ∘ cachedRow 86 m c g)
    (cached_known m c) (cached_fresh_probability m c) excess (fun i => le_max_right _ _)
    1 zero_le_one excess_le_one (fun g => rowGood (decode ∘ cachedRow 86 m c g))
    ((99:ℝ)/98) (tableFailure m c) (by norm_num) (fun g hg i => rowGood_kernel _ hg i) le_rfl
  rw [exposed_card,fixed_counts,Fintype.card_bitVec,Nat.cast_pow,Nat.cast_ofNat,one_mul] at h
  change _ ≤ (99:ℝ)/98*((1-((seen (rowDomain m) c).card:ℝ)/(2:ℝ)^86)*
    (∑ i : Fin M,referenceWeight i*excess i)+
      (∑ i : Fin M,(classCounts (rowDomain m) c decode i:ℝ)*
        (referenceWeight i/classProbability i*excess i))/(2:ℝ)^86)+tableFailure m c at h
  rw [excess_score_identity] at h
  have hb := mul_le_mul_of_nonneg_left (WideEmpirical.good_excess_payoff c hc m)
    (show (0:ℝ)≤99/98 by norm_num)
  exact h.trans (add_le_add hb le_rfl)

theorem uniformMean_instances {A : Type} (fa fb : Fintype A) (f : A → ℝ) :
    @uniformMean A fa f=@uniformMean A fb f := by
  cases Subsingleton.elim fa fb
  rfl

theorem tableFailure_average {α : Type} (oa : OracleComp Spec α) (message : α → Message)
    (c : Cache) (hf : ∀ q : Query,q.1=342 → c q=none) :
    E (run oa c) (fun out => ENNReal.ofReal (tableFailure (message out.1) out.2)) ≤
      (2:ℝ≥0∞)⁻¹^761 := by
  convert actual_rowGood_completion_failure oa c (fun x => hf ⟨342,x⟩ rfl) message using 1
  congr 1
  funext out
  congr 1
  exact uniformMean_instances _ _ _

#print axioms actual_replay_bound
#print axioms actual_excess_bound
#print axioms tableFailure_average
end OptimalOTS.WeightedConstruction.WideCachedRow
