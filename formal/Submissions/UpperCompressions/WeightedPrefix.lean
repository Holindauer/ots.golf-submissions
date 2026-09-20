import Submissions.UpperCompressions.WeightedUniformCompletion

/-! Exact raw256 tier-prefix probabilities. These are the72 predicates needed
by full-table concentration, connected to both first-minimum survival endpoints. -/
noncomputable section
open scoped BigOperators Classical
namespace OptimalOTS.WeightedConstruction.WeightedSchedule
open WeightedReplacement WeightedCompletion WeightedReference WeightedConstants
attribute [local irreducible] Finset.univ Finset.filter WeightedResearch92.classes

def prefixLt (j : ℕ) (x : BitVec 256) : Prop :=
  match decode x with | none => False | some i => tier i < j

def prefixLe (j : ℕ) (x : BitVec 256) : Prop :=
  match decode x with | none => False | some i => tier i ≤ j

theorem prefixLe_eq (j : ℕ) : prefixLe j = prefixLt (j+1) := by
  funext x
  apply propext
  cases decode x <;> simp [prefixLe, prefixLt, Nat.lt_succ_iff]

theorem prefix_mass_sum (j : ℕ) (hj : j ≤ 72) :
    fraction (prefixLt j) = ∑ t ∈ Finset.range j, mass t := by
  have he : (fun x : BitVec 256 => if prefixLt j x then (1:ℝ) else 0) =
      fun x => score (decode x) (fun i => if tier i < j then 1 else 0) := by
    funext x
    cases hx : decode x <;> simp [prefixLt, score, hx]
  unfold fraction
  rw [he, mean_score decode classProbability (fun i => if tier i < j then 1 else 0)
    uniform_decode_probability]
  simp only [classProbability_eq]
  rw [sum_tier (fun t => probability t * (if t < j then 1 else 0))]
  have hh : (∑ t : Tier, (population t : ℝ) * (probability t.val * (if t.val < j then 1 else 0))) =
      ∑ t : Tier, if t.val < j then mass t.val else 0 := by
    apply Finset.sum_congr rfl
    intro t _
    rw [← mul_assoc, population_probability]
    split_ifs <;> simp
  rw [hh, Fin.sum_univ_eq_sum_range (fun t => if t < j then mass t else 0) 72]
  rw [← Finset.sum_filter]
  have hfilter : (Finset.range 72).filter (fun t => t < j) = Finset.range j := by
    ext t
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  rw [hfilter]

theorem mass_early (j : ℕ) (hj : j < 71) : mass j = q := by
  unfold mass lower
  rw [if_pos hj]
  simp only [survival, Nat.cast_add, Nat.cast_one]
  ring

theorem prefixLt_probability (j : ℕ) (hj : j ≤ 71) :
    fraction (prefixLt j) = (j:ℝ)*q := by
  rw [prefix_mass_sum j (by omega)]
  calc
    _ = ∑ _t ∈ Finset.range j, q := by
      apply Finset.sum_congr rfl
      intro t ht
      exact mass_early t (by have := Finset.mem_range.mp ht; omega)
    _ = _ := by simp

theorem prefixLe_probability (j : ℕ) (hj : j ≤ 71) :
    fraction (prefixLe j) = 1-lower j := by
  rw [prefixLe_eq]
  by_cases h : j < 71
  · rw [prefixLt_probability (j+1) (by omega)]
    simp only [lower, if_pos h, survival]
    ring
  · have hj' : j = 71 := by omega
    subst j
    rw [prefix_mass_sum 72 le_rfl, total_mass]
    norm_num [lower]

/-- Complement a predicate before or after fixing a complete table. -/
theorem fraction_not {D : Type} [Fintype D] [Nonempty D] (P : D → Prop) :
    fraction (fun x => ¬ P x) = 1-fraction P := by
  unfold fraction uniformMean
  rw [eq_sub_iff_add_eq, ← add_div]
  have hs : (∑ x : D, if ¬ P x then (1:ℝ) else 0) +
      (∑ x : D, if P x then (1:ℝ) else 0) = Fintype.card D := by
    rw [← Finset.sum_add_distrib]
    calc
      _ = ∑ _x : D, (1:ℝ) := by
        apply Finset.sum_congr rfl
        intro x _
        by_cases hx : P x <;> simp [hx]
      _ = _ := by simp
  convert div_self (show (Fintype.card D : ℝ) ≠ 0 by exact_mod_cast Fintype.card_ne_zero) using 1
  congr 1
  convert hs using 1
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : P x <;> simp [hx]

theorem weakRank_prefix (i : Fin M) :
    weakRank tier i ∘ decode = fun x => ¬ prefixLt (tier i) x := by
  funext x
  apply propext
  cases hx : decode x <;> simp [Function.comp_apply, weakRank, prefixLt, hx]

theorem strictRank_prefix (i : Fin M) :
    strictRank tier i ∘ decode = fun x => ¬ prefixLe (tier i) x := by
  funext x
  apply propext
  cases hx : decode x <;> simp [Function.comp_apply, strictRank, prefixLe, hx]

theorem weakRank_probability (i : Fin M) :
    fraction (weakRank tier i ∘ decode) = survival (tier i) := by
  rw [weakRank_prefix, fraction_not, prefixLt_probability (tier i) (by have := tier_lt i; omega)]
  rfl

theorem strictRank_probability (i : Fin M) :
    fraction (strictRank tier i ∘ decode) = lower (tier i) := by
  rw [strictRank_prefix, fraction_not, prefixLe_probability (tier i) (by have := tier_lt i; omega)]
  ring

theorem prefixLt_zero : prefixLt 0 = fun _ => False := by
  funext x
  cases hx : decode x <;> simp [prefixLt, hx]

theorem prefixLt_succ (j : ℕ) : prefixLt (j+1) = prefixLe j := (prefixLe_eq j).symm

end OptimalOTS.WeightedConstruction.WeightedSchedule
#print axioms OptimalOTS.WeightedConstruction.WeightedSchedule.prefixLe_probability
#print axioms OptimalOTS.WeightedConstruction.WeightedSchedule.weakRank_probability
#print axioms OptimalOTS.WeightedConstruction.WeightedSchedule.strictRank_probability
