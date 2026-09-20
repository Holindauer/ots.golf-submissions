import Submissions.UpperCompressions.ReplacementConcentration

/-! Actual full-table concentration, using the exact uniform restriction law. -/

open OracleSpec OracleComp OracleComp.EvalDist ENNReal
open OptimalOTS

namespace WeightedReplacement
noncomputable section
open scoped Classical BigOperators
local instance stagedLocal_ReplacementTableGood_1 {α : Type*} : DecidableEq α := Classical.decEq α

theorem E_uniform_ofReal {A : Type} [Fintype A] [Nonempty A] [SampleableType A]
    (f : A → ℝ) (hf : ∀ a, 0 ≤ f a) :
    E ($ᵗ A) (fun a => ENNReal.ofReal (f a)) = ENNReal.ofReal (uniformMean f) := by
  rw [ofReal_uniformMean f hf, E, expectedValue_def, tsum_fintype]
  simp only [probOutput_uniformSample]

theorem E_uniform_restrict {A B W : Type} [Fintype A] [Fintype B] [Fintype W]
    [Nonempty W] [SampleableType W] [SampleableType (A → W)] [SampleableType (B → W)]
    (e : A → B) (he : Function.Injective e) (f : (A → W) → ℝ≥0∞) :
    E ($ᵗ (B → W)) (fun g => f (g ∘ e)) = E ($ᵗ (A → W)) f := by
  have hd := evalSPMF_uniformSample_map_comp_injective (R := W) he
  have h := expectedValue_congr (mx := (do let g ← $ᵗ (B → W); pure (g ∘ e)))
    (my := ($ᵗ (A → W))) (fun g => by
      simpa only [probOutput_def] using congrArg (fun p : SPMF (A → W) => p g) hd) f
  simpa only [E, expectedValue_bind, expectedValue_pure] using h

theorem E_table_deficit {A B W : Type} [Fintype A] [Nonempty A]
    [Fintype B] [Fintype W] [Nonempty W] [SampleableType W]
    [SampleableType (A → W)] [SampleableType (B → W)]
    (e : A → B) (he : Function.Injective e) (P : W → Prop)
    (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    E ($ᵗ (B → W)) (fun g => if empirical P (g ∘ e) ≤ fraction P - δ then 1 else 0) ≤
      ENNReal.ofReal (Real.exp (-((Fintype.card A:ℝ)*δ^2/4))) := by
  rw [E_uniform_restrict e he (fun g => if empirical P g ≤ fraction P-δ then 1 else 0)]
  have hx := E_uniform_ofReal (fun g : A → W =>
    if empirical P g ≤ fraction P-δ then (1:ℝ) else 0) (fun g => by split_ifs <;> norm_num)
  simp only [apply_ite, ENNReal.ofReal_one, ENNReal.ofReal_zero] at hx
  rw [hx]
  exact ENNReal.ofReal_le_ofReal (uniform_table_deficit P δ hδ0 hδ1)

theorem E_finite_union {T I : Type} [Fintype I] (p : ProbComp T)
    (bad : I → T → Prop) (ε : ℝ≥0∞)
    (hb : ∀ i, E p (fun t => if bad i t then 1 else 0) ≤ ε) :
    E p (fun t => if ∃ i, bad i t then 1 else 0) ≤ (Fintype.card I:ℝ≥0∞)*ε := by
  calc
    _ ≤ E p (fun t => ∑ i, if bad i t then 1 else 0) := E_mono p (fun t => by
      split_ifs with h
      · obtain ⟨i, hi⟩ := h
        have hle := Finset.single_le_sum (s := Finset.univ)
          (f := fun j => if bad j t then (1:ℝ≥0∞) else 0)
          (fun _ _ => bot_le) (Finset.mem_univ i)
        simpa only [if_pos hi] using hle
      · exact bot_le)
    _ = ∑ i, E p (fun t => if bad i t then 1 else 0) := expectedValue_finsetSum p _ _
    _ ≤ ∑ _i : I, ε := Finset.sum_le_sum (fun i _ => hb i)
    _ = _ := by simp [nsmul_eq_mul]

def fullRowBad (P : Fin 72 → BitVec hashBits → Prop)
    (g : BitVec (msgBits+86) → BitVec hashBits) : Prop :=
  ∃ s : Message × Fin 72,
    empirical (P s.2) (fun η : BitVec 86 => g (s.1 ++ η)) ≤
      fraction (P s.2) - 1/(100*(2:ℝ)^20)

theorem append_right_injective (m : Message) :
    Function.Injective (fun η : BitVec 86 => m ++ η) := by
  intro a b h
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hh := congrArg (fun x : BitVec (msgBits+86) => x.getLsbD i) h
  simpa only [BitVec.getLsbD_append, if_pos hi] using hh

theorem concrete_row_exponent :
    Real.exp (-((Fintype.card (BitVec 86):ℝ)*(1/(100*(2:ℝ)^20))^2/4)) ≤
      (2:ℝ)⁻¹^1024 := by
  have hnum : (1024:ℝ) ≤ (Fintype.card (BitVec 86):ℝ)*(1/(100*(2:ℝ)^20))^2/4 := by
    norm_num
  have hexp : 2 ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1:ℝ)]
  calc
    _ ≤ Real.exp (-(1024:ℝ)) := Real.exp_le_exp.mpr (neg_le_neg hnum)
    _ = (Real.exp 1)⁻¹^1024 := by rw [Real.exp_neg, inv_pow, ← Real.exp_nat_mul]; norm_num
    _ ≤ _ := pow_le_pow_left₀ (by positivity) (inv_anti₀ (by norm_num) hexp) 1024

theorem full_table_bad_probability (P : Fin 72 → BitVec hashBits → Prop) :
    E ($ᵗ (BitVec (msgBits+86) → BitVec hashBits))
      (fun g => if ∃ s : Message × Fin 72,
        empirical (P s.2) (fun η : BitVec 86 => g (s.1 ++ η)) ≤
          fraction (P s.2)-1/(100*(2:ℝ)^20) then 1 else 0) ≤ (2:ℝ≥0∞)⁻¹^761 := by
  let bad : (Message × Fin 72) → (BitVec (msgBits+86) → BitVec hashBits) → Prop :=
    fun s g => empirical (P s.2) (fun η : BitVec 86 => g (s.1 ++ η)) ≤
      fraction (P s.2)-1/(100*(2:ℝ)^20)
  have hb (s : Message × Fin 72) :
      E ($ᵗ (BitVec (msgBits+86) → BitVec hashBits)) (fun g => if bad s g then 1 else 0) ≤
        (2:ℝ≥0∞)⁻¹^1024 := by
    have hx := E_table_deficit (fun η : BitVec 86 => s.1 ++ η) (append_right_injective s.1)
      (P s.2) (1/(100*(2:ℝ)^20)) (by positivity) (by norm_num)
    have he : ENNReal.ofReal ((2:ℝ)⁻¹^1024) = (2:ℝ≥0∞)⁻¹^1024 := by
      rw [ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_inv_of_pos (by norm_num)]
      norm_num
    exact hx.trans (he ▸ ENNReal.ofReal_le_ofReal concrete_row_exponent)
  have h := E_finite_union ($ᵗ (BitVec (msgBits+86) → BitVec hashBits)) bad
    ((2:ℝ≥0∞)⁻¹^1024) hb
  have hc : (Fintype.card (Message × Fin 72):ℝ≥0∞) ≤ (2:ℝ≥0∞)^263 := by
    have hn : Fintype.card (Message × Fin 72) ≤ 2^263 := by
      have hcard : Fintype.card (Message × Fin 72) = 2^256*72 := by
        norm_num [Message, msgBits, Fintype.card_prod]
      rw [hcard]
      calc
        2^256*72 ≤ 2^256*2^7 := Nat.mul_le_mul_left _ (by norm_num)
        _ = 2^263 := by rw [← pow_add]
    exact_mod_cast hn
  have hnum : (Fintype.card (Message × Fin 72):ℝ≥0∞)*(2:ℝ≥0∞)⁻¹^1024 ≤ (2:ℝ≥0∞)⁻¹^761 := by
    calc
      _ ≤ (2:ℝ≥0∞)^263 * (2:ℝ≥0∞)⁻¹^1024 := mul_le_mul' hc le_rfl
      _ = (2:ℝ≥0∞)⁻¹^761 := by
        rw [show 1024 = 263+761 by omega, pow_add, ← mul_assoc, ← mul_pow]
        have hh : (2:ℝ≥0∞)*(2:ℝ≥0∞)⁻¹ = 1 := ENNReal.mul_inv_cancel (by norm_num) (by norm_num)
        rw [hh, one_pow, one_mul]
  exact h.trans hnum

#print axioms E_uniform_restrict
#print axioms E_table_deficit
#print axioms full_table_bad_probability

end
end WeightedReplacement
