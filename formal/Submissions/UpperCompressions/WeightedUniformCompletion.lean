import Submissions.UpperCompressions.WeightedKernelReplay

/-! Literal uniform-table completion has the unconditional one-coordinate
marginals required by the replay/excess formulas. -/
noncomputable section
open scoped BigOperators Classical
namespace WeightedCompletion
open WeightedReplacement
variable {D W I : Type} [Fintype D] [Fintype W] [Nonempty W] [DecidableEq D] [DecidableEq I]

theorem uniformMean_coordinate (a : D) (f : W → ℝ) :
    uniformMean (fun g : D → W => f (g a)) = uniformMean f := by
  have h : uniformMean (fun g : D → W => ∏ d, (if d = a then f (g d) else 1)) =
      ∏ d : D, uniformMean (fun x : W => if d = a then f x else 1) := by
    simp only [uniformMean, Fintype.card_fun, Nat.cast_pow]
    rw [← Fintype.prod_sum (f := fun d : D => fun x : W => if d = a then f x else 1),
      Finset.prod_div_distrib]
    simp
  have hm (d : D) : uniformMean (fun x : W => if d = a then f x else 1) =
      if d = a then uniformMean f else 1 := by
    by_cases hd : d = a <;> simp only [hd, if_true, if_false, uniformMean_const]
  simpa only [hm, Finset.prod_ite_eq', Finset.mem_univ, if_true] using h

def completionTable (R : Finset D) (fixed : D → Option I) (decode : W → Option I)
    (g : D → W) (a : D) : Option I := if a ∈ R then fixed a else decode (g a)

theorem completionTable_known (R : Finset D) (fixed : D → Option I) (decode : W → Option I)
    (g : D → W) (a : D) (ha : a ∈ R) : completionTable R fixed decode g a = fixed a := by
  exact if_pos ha

theorem completionTable_fresh (R : Finset D) (fixed : D → Option I) (decode : W → Option I)
    (a : D) (ha : a ∉ R) (i : I) :
    uniformMean (fun g : D → W => if completionTable R fixed decode g a = some i then 1 else 0) =
      uniformMean (fun x : W => if decode x = some i then 1 else 0) := by
  simp only [completionTable, if_neg ha]
  exact uniformMean_coordinate (W := W) a (fun x : W => if decode x = some i then 1 else 0)

theorem uniformMean_indicator (p : W → Prop) [DecidablePred p] :
    uniformMean (fun x => if p x then 1 else 0) =
      ((Finset.univ.filter p).card : ℝ) / Fintype.card W := by
  unfold uniformMean
  congr 1
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]

end WeightedCompletion

namespace OptimalOTS.WeightedConstruction.WeightedSchedule
open WeightedReplacement WeightedCompletion
attribute [local irreducible] Finset.univ Finset.filter WeightedResearch92.classes

/-- Actual uniform256 oracle answers have the exact classProbability marginal. -/
theorem uniform_decode_probability (i : Fin M) :
    uniformMean (fun x : BitVec 256 => if decode x = some i then 1 else 0) = classProbability i := by
  rw [uniformMean_indicator]
  have hcard : (Fintype.card (BitVec 256) : ℝ) = 2^256 := by
    rw [Fintype.card_bitVec, Nat.cast_pow, Nat.cast_ofNat]
  rw [hcard]
  exact class_probability_real i

/-- Unexposed coordinates retain their original marginal before applying the
joint Good indicator. Cached coordinates are overwritten by their public values. -/
theorem completion_decode_probability {D : Type} [Fintype D] [DecidableEq D]
    (R : Finset D) (fixed : D → Option (Fin M)) (a : D) (ha : a ∉ R) (i : Fin M) :
    uniformMean (fun g : D → BitVec 256 =>
      if completionTable R fixed decode g a = some i then 1 else 0) = classProbability i := by
  exact (completionTable_fresh R fixed decode a ha i).trans (uniform_decode_probability i)

end OptimalOTS.WeightedConstruction.WeightedSchedule
#print axioms WeightedCompletion.uniformMean_coordinate
#print axioms OptimalOTS.WeightedConstruction.WeightedSchedule.completion_decode_probability
