import Submissions.UpperCompressions.Master

open OracleSpec OracleComp OracleComp.EvalDist ENNReal
noncomputable section
open scoped Classical

namespace OptimalOTS.WeightedSampling.Availability

attribute [local irreducible] Finset.univ Finset.filter

theorem card_option_none {n : ℕ} {α : Type} (decode : BitVec n → Option α) (a : ℕ)
    (ha : (Finset.univ.filter fun w => (decode w).isSome).card = a) :
    (Finset.univ.filter fun w => (decode w).isNone).card = 2^n-a := by
  have hp (w : BitVec n) : (decode w).isNone = true ↔ ¬ (decode w).isSome = true := by
    cases decode w <;> simp
  have h := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (BitVec n))) (p := fun w => (decode w).isSome = true)
  simp only [← hp,ha,Finset.card_univ,Fintype.card_bitVec] at h
  omega

theorem uniform_option_miss {n : ℕ} {α : Type} (decode : BitVec n → Option α) (a : ℕ)
    (ha : (Finset.univ.filter fun w => (decode w).isSome).card = a) (c : ℝ≥0∞) :
    E ($ᵗ BitVec n) (fun w => if (decode w).isNone then c else 0) =
      ((2^n-a : ℕ) : ℝ≥0∞)/(2:ℝ≥0∞)^n*c := by
  rw [E_uniform]
  simp only [mul_ite,mul_zero]
  rw [← Finset.sum_filter,Finset.sum_const,nsmul_eq_mul,
    card_option_none decode a ha,Fintype.card_bitVec]
  simp only [Nat.cast_pow,Nat.cast_ofNat,div_eq_mul_inv,mul_assoc]

#print axioms uniform_option_miss
end OptimalOTS.WeightedSampling.Availability
