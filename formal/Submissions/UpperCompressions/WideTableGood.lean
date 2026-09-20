import Submissions.UpperCompressions.WeightedPrefix
import Submissions.UpperCompressions.WideReplayBounds
import Submissions.UpperCompressions.ReplacementTableGood

/-! Concrete full-table72-prefix event, exact first-minimum kernel envelope,
and its unconditional tail. This event is never used to recondition the oracle. -/
open OracleSpec OracleComp OracleComp.EvalDist ENNReal
noncomputable section
open scoped BigOperators Classical
namespace OptimalOTS.WeightedConstruction.WeightedSchedule
open WeightedReplacement WeightedCompletion WeightedReference WeightedConstants
attribute [local irreducible] Finset.univ Finset.filter WeightedResearch92.classes

def prefixPredicates (j : Fin 72) : BitVec 256 → Prop := prefixLe j.val

theorem empirical_eq_fraction {D : Type} [Fintype D]
    (P : BitVec 256 → Prop) (row : D → BitVec 256) :
    empirical P row = fraction (P ∘ row) := rfl

theorem fraction_le_one {D : Type} [Fintype D] [Nonempty D] (P : D → Prop) :
    fraction P ≤ 1 := by
  unfold fraction
  exact (uniformMean_mono _ (fun _ => 1) (fun _ => by split_ifs <;> norm_num)).trans_eq
    (uniformMean_const 1)

/-- The empty weak prefix costs nothing; all other weak prefixes and every
strict prefix use one of the72 concentration predicates. -/
theorem prefix_deficits_rowGood {D : Type} [Fintype D] [Nonempty D] [DecidableEq D]
    (row : D → BitVec 256)
    (hgood : ∀ j : Fin 72, fraction (prefixPredicates j)-1/(100*(L:ℝ)) <
      empirical (prefixPredicates j) row) : rowGood (decode ∘ row) := by
  intro i
  have hj : tier i ≤ 71 := by have := tier_lt i; omega
  have hw : weakRank tier i ∘ (decode ∘ row) = fun a => ¬ prefixLt (tier i) (row a) := by
    funext a
    exact congrArg (fun f => f (row a)) (weakRank_prefix i)
  have hs : strictRank tier i ∘ (decode ∘ row) = fun a => ¬ prefixLe (tier i) (row a) := by
    funext a
    exact congrArg (fun f => f (row a)) (strictRank_prefix i)
  constructor
  · by_cases h0 : tier i = 0
    · have hh := fraction_le_one (weakRank tier i ∘ (decode ∘ row))
      simp only [h0, survival, Nat.cast_zero, zero_mul, sub_zero]
      exact hh.trans (le_add_of_nonneg_right (by positivity))
    · let j : Fin 72 := ⟨tier i-1, by omega⟩
      have hp : prefixPredicates j = prefixLt (tier i) := by
        unfold prefixPredicates
        rw [prefixLe_eq]
        congr 1
        dsimp only [j]
        omega
      have hg := hgood j
      rw [hp, prefixLt_probability (tier i) hj, empirical_eq_fraction] at hg
      rw [hw, fraction_not]
      unfold survival
      change 1-fraction (prefixLt (tier i) ∘ row) ≤ _
      linarith
  · have hg := hgood ⟨tier i, tier_lt i⟩
    change fraction (prefixLe (tier i))-1/(100*(L:ℝ)) < empirical (prefixLe (tier i)) row at hg
    rw [prefixLe_probability (tier i) hj, empirical_eq_fraction] at hg
    rw [hs, fraction_not]
    change 1-fraction (prefixLe (tier i) ∘ row) ≤ _
    linarith

def fullTableGood (g : BitVec (msgBits+86) → BitVec hashBits) : Prop :=
  ¬ fullRowBad prefixPredicates g

theorem fullTableGood_row (g : BitVec (msgBits+86) → BitVec hashBits)
    (hg : fullTableGood g) (m : Message) :
    rowGood (decode ∘ (fun η : BitVec 86 => g (m ++ η))) := by
  apply prefix_deficits_rowGood
  intro j
  apply lt_of_not_ge
  intro hj
  apply hg
  refine ⟨(m,j), ?_⟩
  convert hj using 1 <;> norm_num [L]
  all_goals rfl

/-- Pointwise good-table envelope for every message row and actual decoded class. -/
theorem fullTableGood_kernel (g : BitVec (msgBits+86) → BitVec hashBits)
    (hg : fullTableGood g) (m : Message) (i : Fin M) :
    kernel L (fraction (weakRank tier i ∘ decode ∘ (fun η : BitVec 86 => g (m ++ η))))
      (fraction (strictRank tier i ∘ decode ∘ (fun η : BitVec 86 => g (m ++ η)))) ≤
        (99:ℝ)/98 * (referenceWeight i/classProbability i) :=
  rowGood_kernel _ (fullTableGood_row g hg m) i

/-- Unconditional tail across all message rows and all72 actual prefix predicates. -/
theorem fullTableGood_bad_probability :
    E ($ᵗ (BitVec (msgBits+86) → BitVec hashBits))
      (fun g => if fullTableGood g then 0 else 1) ≤ (2:ℝ≥0∞)⁻¹^761 := by
  have h := full_table_bad_probability prefixPredicates
  convert h using 1
  congr 1
  funext g
  unfold fullTableGood fullRowBad
  split_ifs <;> simp_all

end OptimalOTS.WeightedConstruction.WeightedSchedule
#print axioms OptimalOTS.WeightedConstruction.WeightedSchedule.fullTableGood_row
#print axioms OptimalOTS.WeightedConstruction.WeightedSchedule.fullTableGood_kernel
#print axioms OptimalOTS.WeightedConstruction.WeightedSchedule.fullTableGood_bad_probability
