import Submissions.UpperCompressions.WeightedUniformCompletion

/-! Concrete mixed72 replay/excess bounds for literal uniform completion tables.
The remaining Good-tail premise is supplied by global table concentration. -/
noncomputable section
open scoped BigOperators Classical
namespace OptimalOTS.WeightedConstruction.WeightedSchedule
open WeightedCompletion WeightedReplacement WeightedConstants WeightedReference
attribute [local irreducible] Finset.univ Finset.filter WeightedResearch92.classes
variable {D : Type} [Fintype D] [Nonempty D] [DecidableEq D]

def rowGood (table : D → Option (Fin M)) : Prop := ∀ i,
  fraction (weakRank tier i ∘ table) ≤ survival (tier i)+1/(100*(L:ℝ)) ∧
  fraction (strictRank tier i ∘ table) ≤ lower (tier i)+1/(100*(L:ℝ))

theorem rowGood_kernel (table : D → Option (Fin M)) (hg : rowGood table) (i : Fin M) :
    kernel L (fraction (weakRank tier i ∘ table)) (fraction (strictRank tier i ∘ table)) ≤
      (99:ℝ)/98 * (referenceWeight i / classProbability i) := by
  apply empirical_kernel_le i _ _ _ _ (hg i).1 (hg i).2
  all_goals
    unfold fraction uniformMean
    apply div_nonneg
    · apply Finset.sum_nonneg
      intro x _
      split_ifs <;> norm_num
    · exact Nat.cast_nonneg _

/-- The replay formula is concrete at nonce-domain D; D=BitVec86 gives N=2^86.
The independent table is sampled before applying the joint Good indicator. -/
theorem concrete_replay_bound (R : Finset D) (fixed : D → Option (Fin M)) (k : Fin M → ℕ)
    (Good : (D → BitVec 256) → Prop) (δ : ℝ)
    (hgood : ∀ g, Good g → rowGood (completionTable R fixed decode g))
    (hbad : uniformMean (fun g => if Good g then 0 else 1) ≤ δ) :
    uniformMean (fun g : D → BitVec 256 =>
      tableKernel L (completionTable R fixed decode g) tier (fun a i =>
        if a ∈ R then (if 2 ≤ k i then 1 else 0) else (if k i = 0 then 0 else 1))) ≤
      (99:ℝ)/98 * securityWeights.hazard (Fintype.card D) R.card k (rowCount R fixed) + δ := by
  apply replay_kernel_bound securityWeights L tier R fixed (completionTable R fixed decode) k
    (completionTable_known R fixed decode)
    (completion_decode_probability R fixed) Good ((99:ℝ)/98) δ (by norm_num)
  · intro g hg i
    exact rowGood_kernel _ (hgood g hg) i
  · exact hbad

/-- Concrete expected excess score, including zero payoff on signing failure. -/
theorem concrete_excess_bound (R : Finset D) (fixed : D → Option (Fin M))
    (Good : (D → BitVec 256) → Prop) (δ emax : ℝ) (hemax : 0 ≤ emax)
    (hesc : ∀ i, excess i ≤ emax)
    (hgood : ∀ g, Good g → rowGood (completionTable R fixed decode g))
    (hbad : uniformMean (fun g => if Good g then 0 else 1) ≤ δ) :
    uniformMean (fun g : D → BitVec 256 =>
      tableKernel L (completionTable R fixed decode g) tier (fun _ i => excess i)) ≤
      (99:ℝ)/98 * ((1-(R.card : ℝ)/Fintype.card D) * (∑ i, referenceWeight i * excess i) +
        (∑ i, (rowCount R fixed i : ℝ) * (referenceWeight i/classProbability i * excess i)) /
          Fintype.card D) + emax * δ := by
  apply excess_kernel_bound securityWeights L tier R fixed (completionTable R fixed decode)
    (completionTable_known R fixed decode) (completion_decode_probability R fixed)
    excess (fun i => le_max_right _ _) emax hemax hesc Good ((99:ℝ)/98) δ (by norm_num)
  · intro g hg i
    exact rowGood_kernel _ (hgood g hg) i
  · exact hbad

end OptimalOTS.WeightedConstruction.WeightedSchedule
#print axioms OptimalOTS.WeightedConstruction.WeightedSchedule.concrete_replay_bound
#print axioms OptimalOTS.WeightedConstruction.WeightedSchedule.concrete_excess_bound
