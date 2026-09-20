import Submissions.UpperCompressions.ReplacementProgram
import Submissions.UpperCompressions.ReplacementPosterior

/-! Exact single-coordinate decomposition for real table updates, followed by a
Bayes bound for the actual first-minimum sampling likelihood. No Good event is
conditioned on. Adaptive transcript/filtration integration remains separate. -/

namespace WeightedReplacement

open OptimalOTS.WeightedSampling
open scoped Classical
noncomputable section
local instance stagedLocal_ReplacementCoordinate_1 {α : Type*} : DecidableEq α := Classical.decEq α

noncomputable def fractionExcept {ι : Type} [Fintype ι] (p : ι → Prop) (u : ι) : ℝ :=
  (∑ a ∈ Finset.univ.erase u, if p a then (1 : ℝ) else 0) / Fintype.card ι

theorem fractionExcept_nonneg {ι : Type} [Fintype ι] (p : ι → Prop) (u : ι) :
    0 ≤ fractionExcept p u := by
  apply div_nonneg _ (Nat.cast_nonneg _)
  apply Finset.sum_nonneg
  intro a ha
  split_ifs <;> norm_num

theorem fraction_update {ι Ω : Type} [Fintype ι] (table : ι → Ω)
    (p : Ω → Prop) (u : ι) (y : Ω) :
    fraction (p ∘ Function.update table u y) = fractionExcept (p ∘ table) u +
      if p y then 1 / (Fintype.card ι : ℝ) else 0 := by
  have hs : (∑ a, if p (Function.update table u y a) then (1 : ℝ) else 0) =
      (∑ a ∈ Finset.univ.erase u, if p (table a) then (1 : ℝ) else 0) +
        (if p y then 1 else 0) := by
    calc
      _ = (∑ a ∈ Finset.univ.erase u,
          if p (Function.update table u y a) then (1 : ℝ) else 0) +
          (if p (Function.update table u y u) then 1 else 0) :=
        (Finset.sum_erase_add Finset.univ
          (fun a => if p (Function.update table u y a) then (1 : ℝ) else 0)
          (Finset.mem_univ u)).symm
      _ = _ := by
        rw [Function.update_self]
        congr 1
        apply Finset.sum_congr rfl
        intro a ha
        rw [Function.update_of_ne (Finset.mem_erase.mp ha).1]
  unfold fraction uniformMean fractionExcept
  simp only [Function.comp_apply]
  rw [hs, add_div]
  by_cases hy : p y <;> simp [hy]

/-- The exact first-minimum target likelihood on one concrete decoded table. -/
noncomputable def tableWinnerLikelihood {ι Ω γ : Type} [Fintype ι]
    (k : ℕ) (table : ι → Ω) (decode : Ω → Option γ) (tier : γ → ℕ)
    (v : ι) (i : γ) : ℝ :=
  iidMean k (fun xs => if select (fun p : ι × γ => tier p.2)
      (xs.map fun a => (fun j => (a,j)) <$> decode (table a)) = some (v,i)
    then (1 : ℝ) else 0)

theorem tableWinnerLikelihood_eq {ι Ω γ : Type} [Fintype ι]
    (k : ℕ) (table : ι → Ω) (decode : Ω → Option γ) (tier : γ → ℕ)
    (v : ι) (i : γ) (hv : decode (table v) = some i) :
    tableWinnerLikelihood k table decode tier v i =
      kernel k (fraction (weakRank tier i ∘ decode ∘ table))
        (fraction (strictRank tier i ∘ decode ∘ table)) / Fintype.card ι := by
  have h := iid_tagged_table_probability (decode ∘ table) tier v i hv k
  unfold tableWinnerLikelihood
  convert h using 1
  congr 1

/-- Changing a distinct unknown nonce changes each survival endpoint only by
that coordinate's exact mass 1/N. This identifies the generic Bayes kernel with
the actual selector likelihood, not an assumed likelihood surrogate. -/
theorem tableWinnerLikelihood_update {ι Ω γ : Type} [Fintype ι]
    (k : ℕ) (table : ι → Ω) (decode : Ω → Option γ) (tier : γ → ℕ)
    (u v : ι) (i : γ) (hvu : v ≠ u) (hv : decode (table v) = some i) (y : Ω) :
    tableWinnerLikelihood k (Function.update table u y) decode tier v i =
      coordinateLikelihood k
        (fractionExcept (weakRank tier i ∘ decode ∘ table) u)
        (fractionExcept (strictRank tier i ∘ decode ∘ table) u)
        (1 / (Fintype.card ι : ℝ)) (Fintype.card ι)
        (weakRank tier i ∘ decode) (strictRank tier i ∘ decode) y := by
  rw [tableWinnerLikelihood_eq k _ decode tier v i
    (by simpa only [Function.update_of_ne hvu] using hv)]
  have hweak := fraction_update table (weakRank tier i ∘ decode) u y
  have hstrict := fraction_update table (strictRank tier i ∘ decode) u y
  simp only [Function.comp_assoc] at hweak hstrict
  rw [hweak, hstrict]
  rfl

/-- Posterior bound for a fresh coordinate, pointwise in every other table entry.
The signed nonce v differs from the unknown nonce u. -/
theorem updated_table_posterior_bound {ι Ω γ : Type} [Fintype ι] [Fintype Ω]
    (k : ℕ) (table : ι → Ω) (decode : Ω → Option γ) (tier : γ → ℕ)
    (u v : ι) (i : γ) (hvu : v ≠ u) (hv : decode (table v) = some i)
    (weight : Ω → ℝ) (hw : ∀ y, 0 ≤ weight y)
    (hmass : 0 < weightedMass weight (weakRank tier i ∘ decode))
    (hden : 0 < ∑ y, weight y *
      tableWinnerLikelihood k (Function.update table u y) decode tier v i) :
    (∑ y, if decode y = some i then weight y *
      tableWinnerLikelihood k (Function.update table u y) decode tier v i else 0) /
      (∑ y, weight y * tableWinnerLikelihood k (Function.update table u y) decode tier v i) ≤
      weightedMass weight (fun y => decode y = some i) /
        weightedMass weight (weakRank tier i ∘ decode) := by
  simp_rw [tableWinnerLikelihood_update k table decode tier u v i hvu hv] at hden ⊢
  have ht : ∀ y, decode y = some i →
      (weakRank tier i ∘ decode) y ∧ ¬ (strictRank tier i ∘ decode) y := by
    intro y hy
    simp [hy, weakRank, strictRank]
  have h := coordinate_posterior_bound k
    (fractionExcept (weakRank tier i ∘ decode ∘ table) u)
    (fractionExcept (strictRank tier i ∘ decode ∘ table) u)
    (1 / (Fintype.card ι : ℝ)) (Fintype.card ι) weight
    (fun y => decode y = some i) (weakRank tier i ∘ decode) (strictRank tier i ∘ decode)
    (fractionExcept_nonneg _ _) (fractionExcept_nonneg _ _)
    (div_nonneg zero_le_one (Nat.cast_nonneg _)) (Nat.cast_nonneg _) hw ht hmass hden
  convert h using 1 <;> congr 2
  funext y
  split_ifs <;> rfl

def lowerRank {γ : Type} (tier : γ → ℕ) (i : γ) : Option γ → Prop
  | none => False
  | some j => tier j < tier i

theorem weakRank_iff_not_lowerRank {γ : Type} (tier : γ → ℕ) (i : γ) (x : Option γ) :
    weakRank tier i x ↔ ¬ lowerRank tier i x := by
  cases x <;> simp [weakRank, lowerRank, Nat.not_lt]

theorem weightedMass_add_complement {Ω : Type} [Fintype Ω]
    (weight : Ω → ℝ) (p : Ω → Prop) :
    weightedMass weight p + weightedMass weight (fun y => ¬ p y) = ∑ y, weight y := by
  unfold weightedMass
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro y hy
  by_cases hp : p y <;> simp [hp]

/-- With a normalized prior, exact class mass p and lower-tier prefix mass F,
the concrete updated-table Bayes posterior is at most p/(1-F). -/
theorem updated_table_posterior_class_bound {ι Ω γ : Type} [Fintype ι] [Fintype Ω]
    (k : ℕ) (table : ι → Ω) (decode : Ω → Option γ) (tier : γ → ℕ)
    (u v : ι) (i : γ) (hvu : v ≠ u) (hv : decode (table v) = some i)
    (weight : Ω → ℝ) (hw : ∀ y, 0 ≤ weight y) (hunit : ∑ y, weight y = 1)
    (p F : ℝ) (hp : weightedMass weight (fun y => decode y = some i) = p)
    (hF : weightedMass weight (lowerRank tier i ∘ decode) = F) (hFlt : F < 1)
    (hden : 0 < ∑ y, weight y *
      tableWinnerLikelihood k (Function.update table u y) decode tier v i) :
    (∑ y, if decode y = some i then weight y *
      tableWinnerLikelihood k (Function.update table u y) decode tier v i else 0) /
      (∑ y, weight y * tableWinnerLikelihood k (Function.update table u y) decode tier v i) ≤
      p / (1-F) := by
  have hweak : weightedMass weight (weakRank tier i ∘ decode) = 1-F := by
    have h := weightedMass_add_complement weight (lowerRank tier i ∘ decode)
    have he : (fun y => ¬ (lowerRank tier i ∘ decode) y) = weakRank tier i ∘ decode := by
      funext y
      exact propext (weakRank_iff_not_lowerRank tier i (decode y)).symm
    rw [he, hF, hunit] at h
    linarith
  have hmass : 0 < weightedMass weight (weakRank tier i ∘ decode) := by
    rw [hweak]
    linarith
  simpa only [hp, hweak] using
    updated_table_posterior_bound k table decode tier u v i hvu hv weight hw hmass hden

#print axioms fraction_update
#print axioms tableWinnerLikelihood_update
#print axioms updated_table_posterior_class_bound

end
end WeightedReplacement
