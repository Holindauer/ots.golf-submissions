import Submissions.UpperCompressions.ReplacementHybridPrefix
import Submissions.UpperCompressions.ReplacementFactorization
import Submissions.UpperCompressions.ReplacementTableGood

/-! Denominator-free first-exposure bounds. Zero-probability public prefixes
require no exceptional conditioning argument. Evidence remains joint throughout. -/

open OracleSpec OracleComp OracleComp.EvalDist ENNReal
open OptimalOTS
namespace WeightedReplacement
noncomputable section
open scoped Classical BigOperators
local instance stagedLocal_ReplacementJointPosterior_1 {α : Type*} : DecidableEq α := Classical.decEq α

theorem finite_likelihood_joint {Ω : Type*} [Fintype Ω]
    (weight likelihood : Ω → ℝ) (target survival : Ω → Prop) (c : ℝ)
    (hw : ∀ y, 0 ≤ weight y) (hl : ∀ y, 0 ≤ likelihood y)
    (ht : ∀ y, target y → likelihood y = c)
    (hs : ∀ y, survival y → c ≤ likelihood y)
    (hmass : 0 < weightedMass weight survival) :
    (∑ y, if target y then weight y * likelihood y else 0) ≤
      (weightedMass weight target / weightedMass weight survival) *
        (∑ y, weight y * likelihood y) := by
  have hnum : (∑ y, if target y then weight y * likelihood y else 0) =
      weightedMass weight target * c := by
    rw [weightedMass, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro y _
    by_cases hy : target y <;> simp [hy, ht y]
  have hlow : weightedMass weight survival * c ≤ ∑ y, weight y * likelihood y := by
    rw [weightedMass, Finset.sum_mul]
    apply Finset.sum_le_sum
    intro y _
    by_cases hy : survival y
    · simp only [if_pos hy]
      exact mul_le_mul_of_nonneg_left (hs y hy) (hw y)
    · simp only [if_neg hy, zero_mul]
      exact mul_nonneg (hw y) (hl y)
  rw [hnum]
  have hcp : c ≤ (∑ y, weight y * likelihood y) / weightedMass weight survival := by
    apply (le_div_iff₀ hmass).2
    simpa only [mul_comm] using hlow
  calc
    _ ≤ weightedMass weight target * ((∑ y, weight y * likelihood y) / weightedMass weight survival) :=
      mul_le_mul_of_nonneg_left hcp (weightedMass_nonneg weight target hw)
    _ = _ := by ring

theorem weightedMass_uniform {Ω : Type*} [Fintype Ω] (P : Ω → Prop) :
    weightedMass (fun _ : Ω => 1/(Fintype.card Ω:ℝ)) P = fraction P := by
  unfold weightedMass fraction uniformMean
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro y _
  split_ifs <;> simp

theorem coordinate_uniform_joint {Ω : Type*} [Fintype Ω]
    (L : ℕ) (A B δ N : ℝ) (target weak strict : Ω → Prop)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hδ : 0 ≤ δ) (hN : 0 ≤ N)
    (ht : ∀ y, target y → weak y ∧ ¬ strict y) (hmass : 0 < fraction weak) :
    uniformMean (fun y => if target y then coordinateLikelihood L A B δ N weak strict y else 0) ≤
      (fraction target / fraction weak) * uniformMean (coordinateLikelihood L A B δ N weak strict) := by
  have h := finite_likelihood_joint (fun _ : Ω => 1/(Fintype.card Ω:ℝ))
    (coordinateLikelihood L A B δ N weak strict) target weak (kernel L (A+δ) B/N)
    (fun _ => by positivity) (coordinateLikelihood_nonneg L A B δ N weak strict hA hB hδ hN)
    (fun y hy => coordinateLikelihood_same L A B δ N weak strict y (ht y hy).1 (ht y hy).2)
    (coordinateLikelihood_survival L A B δ N weak strict hA hB hδ hN)
    (by simpa only [weightedMass_uniform] using hmass)
  simp only [weightedMass_uniform] at h
  have hn : (∑ y, if target y then (1/(Fintype.card Ω:ℝ))*coordinateLikelihood L A B δ N weak strict y else 0) =
      uniformMean (fun y => if target y then coordinateLikelihood L A B δ N weak strict y else 0) := by
    simp only [uniformMean, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro y _
    split_ifs <;> simp [div_eq_mul_inv, mul_comm]
  have hd : (∑ y, (1/(Fintype.card Ω:ℝ))*coordinateLikelihood L A B δ N weak strict y) =
      uniformMean (coordinateLikelihood L A B δ N weak strict) := by
    simp [uniformMean, div_eq_mul_inv, mul_comm, ← Finset.mul_sum]
  rwa [hn, hd] at h

def hybridEvidence {α : Type} (u : Query) (oa : OracleComp Spec α) (c : Cache)
    (event : Option α × PublicTrace → Prop) : ℝ :=
  (E (hybridPrefix u oa c []) (fun p => if event p then 1 else 0)).toReal

theorem hybridEvidence_nonneg {α : Type} (u : Query) (oa : OracleComp Spec α) (c : Cache)
    (event : Option α × PublicTrace → Prop) : 0 ≤ hybridEvidence u oa c event := ENNReal.toReal_nonneg

theorem ofReal_hybridEvidence {α : Type} (u : Query) (oa : OracleComp Spec α) (c : Cache)
    (event : Option α × PublicTrace → Prop) :
    ENNReal.ofReal (hybridEvidence u oa c event) =
      E (hybridPrefix u oa c []) (fun p => if event p then 1 else 0) := by
  apply ENNReal.ofReal_toReal
  exact ne_of_lt (lt_of_le_of_lt (E_le_one _ (fun _ => by split_ifs <;> simp)) (by simp))

theorem E_taggedHybridPrefix {α β : Type} (p : ProbComp β)
    (post : β → OracleComp Spec α) (b : β) (u : Query) (c : Cache) (y : BitVec hashBits)
    (event : Option α × PublicTrace → Prop) :
    E (taggedBind p (fun b' => hybridPrefix u (post b') (overwrite c u y) []))
      (fun r => if r.1 = b ∧ event r.2 then 1 else 0) =
        E p (fun b' => if b' = b then 1 else 0) * ENNReal.ofReal (hybridEvidence u (post b) c event) := by
  rw [E_taggedBind_event, hybridPrefix_event_overwrite, ofReal_hybridEvidence]

def resampledSignedPrefix {α β : Type} (p : BitVec hashBits → ProbComp β)
    (post : β → OracleComp Spec α) (u : Query) (c : Cache) :
    ProbComp (BitVec hashBits × β × (Option α × PublicTrace)) := do
  let y ← $ᵗ BitVec hashBits
  let r ← taggedBind (p y) (fun b => hybridPrefix u (post b) (overwrite c u y) [])
  pure (y,r)

/-- Exact joint factorization under an actual uniform coordinate resampling.
The public program is fully adaptive and uses the original mixed lazy oracle. -/
theorem resampledSignedPrefix_joint {α β : Type} (p : BitVec hashBits → ProbComp β)
    (post : β → OracleComp Spec α) (b : β) (u : Query) (c : Cache)
    (event : Option α × PublicTrace → Prop) (target : BitVec hashBits → Prop)
    (likelihood : BitVec hashBits → ℝ) (hl : ∀ y, 0 ≤ likelihood y)
    (hp : ∀ y, E (p y) (fun b' => if b' = b then 1 else 0) = ENNReal.ofReal (likelihood y)) :
    E (resampledSignedPrefix p post u c)
      (fun r => if target r.1 ∧ r.2.1 = b ∧ event r.2.2 then 1 else 0) =
      ENNReal.ofReal (uniformMean (fun y => if target y then likelihood y else 0) *
        hybridEvidence u (post b) c event) := by
  rw [resampledSignedPrefix, E_bind]
  have hpoint (y : BitVec hashBits) :
      E (taggedBind (p y) (fun b' => hybridPrefix u (post b') (overwrite c u y) []))
        (fun r => E (pure (y,r)) (fun r => if target r.1 ∧ r.2.1 = b ∧ event r.2.2 then 1 else 0)) =
      ENNReal.ofReal ((if target y then likelihood y else 0) * hybridEvidence u (post b) c event) := by
    simp only [E_pure]
    by_cases hy : target y
    · simp only [hy, true_and, if_true]
      rw [E_taggedHybridPrefix, hp y, ENNReal.ofReal_mul (hl y)]
    · simp [hy, E, expectedValue_def]
  simp only [E_bind, hpoint]
  rw [E_uniform_ofReal _ (fun y => mul_nonneg (by split_ifs <;> simp [hl]) (hybridEvidence_nonneg _ _ _ _)),
    uniformMean_mul_const]

theorem resampledSignedPrefix_bound {α β : Type} (p : BitVec hashBits → ProbComp β)
    (post : β → OracleComp Spec α) (b : β) (u : Query) (c : Cache)
    (event : Option α × PublicTrace → Prop) (target : BitVec hashBits → Prop)
    (likelihood : BitVec hashBits → ℝ) (rate : ℝ) (hl : ∀ y, 0 ≤ likelihood y)
    (hr : 0 ≤ rate)
    (hp : ∀ y, E (p y) (fun b' => if b' = b then 1 else 0) = ENNReal.ofReal (likelihood y))
    (hb : uniformMean (fun y => if target y then likelihood y else 0) ≤ rate*uniformMean likelihood) :
    E (resampledSignedPrefix p post u c)
      (fun r => if target r.1 ∧ r.2.1 = b ∧ event r.2.2 then 1 else 0) ≤
      ENNReal.ofReal rate * E (resampledSignedPrefix p post u c)
        (fun r => if r.2.1 = b ∧ event r.2.2 then 1 else 0) := by
  have hden := resampledSignedPrefix_joint p post b u c event (fun _ => True) likelihood hl hp
  simp only [true_and, if_true] at hden
  rw [resampledSignedPrefix_joint p post b u c event target likelihood hl hp, hden,
    ← ENNReal.ofReal_mul hr]
  apply ENNReal.ofReal_le_ofReal
  calc
    _ ≤ (rate*uniformMean likelihood)*hybridEvidence u (post b) c event :=
      mul_le_mul_of_nonneg_right hb (hybridEvidence_nonneg _ _ _ _)
    _ = _ := by ring

#print axioms finite_likelihood_joint
#print axioms coordinate_uniform_joint
#print axioms resampledSignedPrefix_bound

end
end WeightedReplacement
