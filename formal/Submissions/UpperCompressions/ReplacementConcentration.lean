import Submissions.UpperCompressions.ReplacementProgram
import Submissions.UpperCompressions.BernsteinMGF
import Submissions.UpperCompressions.FiniteKernelConcentration

/-! Finite product concentration of uniform function tables. All expectations
are finite normalized sums, then connected to the actual uniform ProbComp. -/

open OracleSpec OracleComp OracleComp.EvalDist ENNReal
open OptimalOTS

namespace WeightedReplacement
noncomputable section
open scoped Classical BigOperators
local instance stagedLocal_ReplacementConcentration_1 {α : Type*} : DecidableEq α := Classical.decEq α

def meanLinear (α : Type*) [Fintype α] : (α → ℝ) →ₗ[ℝ] ℝ where
  toFun := uniformMean
  map_add' f g := uniformMean_add f g
  map_smul' r f := by
    change uniformMean (fun a => r*f a) = r*uniformMean f
    simp only [uniformMean, ← Finset.mul_sum]
    ring

theorem uniformMean_mono {α : Type*} [Fintype α] (f g : α → ℝ)
    (h : ∀ a, f a ≤ g a) : uniformMean f ≤ uniformMean g :=
  div_le_div_of_nonneg_right (Finset.sum_le_sum (fun a _ => h a)) (by positivity)

theorem uniformMean_const {α : Type*} [Fintype α] [Nonempty α] (c : ℝ) :
    uniformMean (fun _ : α => c) = c := by
  simp [uniformMean, Finset.sum_const, nsmul_eq_mul]

theorem uniformMean_product {D W : Type*} [Fintype D] [Fintype W]
    (f : D → W → ℝ) :
    uniformMean (fun g : D → W => ∏ d, f d (g d)) = ∏ d, uniformMean (f d) := by
  simp only [uniformMean, Fintype.card_fun, Nat.cast_pow]
  rw [← Fintype.prod_sum, Finset.prod_div_distrib]
  simp

theorem uniformMean_centered_indicator_mgf {W : Type*} [Fintype W] [Nonempty W]
    (P : W → Prop) (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    uniformMean (fun w => Real.exp (θ * (fraction P - if P w then 1 else 0) - θ^2)) ≤ 1 := by
  let X : W → ℝ := fun w => fraction P - if P w then 1 else 0
  have hμ0 : 0 ≤ fraction P := by
    unfold fraction
    exact (show uniformMean (fun _ : W => (0:ℝ)) ≤ _ from
      uniformMean_mono _ _ (fun w => by split_ifs <;> norm_num)).trans_eq' (uniformMean_const 0)
  have hμ1 : fraction P ≤ 1 := by
    unfold fraction
    calc
      _ ≤ uniformMean (fun _ : W => (1:ℝ)) := uniformMean_mono _ _ (fun w => by split_ifs <;> norm_num)
      _ = _ := uniformMean_const 1
  have hb : ∀ w, |X w| ≤ 1 := by
    intro w
    dsimp [X]
    split_ifs <;> rw [abs_le] <;> constructor <;> linarith
  have hm : meanLinear W X = 0 := by
    change uniformMean X = 0
    dsimp [X]
    simp [uniformMean, fraction, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul,
      sub_div, mul_div_cancel_left₀ _ (show (Fintype.card W:ℝ) ≠ 0 by positivity)]
  have hs : meanLinear W (fun w => (X w)^2) ≤ 1 := by
    change uniformMean _ ≤ 1
    calc
      _ ≤ uniformMean (fun _ : W => (1:ℝ)) := uniformMean_mono _ _ (fun w => (sq_le_one_iff_abs_le_one _).2 (hb w))
      _ = _ := uniformMean_const 1
  have hx := WeightedMGF.centered_mgf (meanLinear W) (fun f g h => uniformMean_mono f g h)
    (uniformMean_const 1) X θ 1 1 hθ0 (by norm_num) (by nlinarith) hb hm hs
  have hc : θ^2 * 1 / (2 * (1-θ*1/3)) ≤ θ^2 := by
    have hd : 0 < 2*(1-θ*1/3) := by linarith
    apply (div_le_iff₀ hd).2
    nlinarith [sq_nonneg θ]
  have hbase : uniformMean (fun w => Real.exp (θ*X w)) ≤ Real.exp (θ^2) :=
    hx.trans (Real.exp_le_exp.mpr hc)
  have hf : (fun w => Real.exp (θ*X w-θ^2)) =
      (fun w => Real.exp (θ*X w) * Real.exp (-θ^2)) := by
    funext w
    rw [sub_eq_add_neg, Real.exp_add]
  change uniformMean (fun w => Real.exp (θ*X w-θ^2)) ≤ 1
  rw [hf, uniformMean_mul_const]
  calc
    _ ≤ Real.exp (θ^2)*Real.exp (-θ^2) :=
      mul_le_mul_of_nonneg_right hbase (Real.exp_nonneg _)
    _ = 1 := by rw [← Real.exp_add]; simp

def empirical {D W : Type*} [Fintype D] (P : W → Prop) (g : D → W) : ℝ :=
  fraction (P ∘ g)

theorem uniform_table_deficit {D W : Type*} [Fintype D] [Nonempty D]
    [Fintype W] [Nonempty W] (P : W → Prop) (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    uniformMean (fun g : D → W => if empirical P g ≤ fraction P - δ then 1 else 0) ≤
      Real.exp (-((Fintype.card D : ℝ) * δ^2 / 4)) := by
  let θ := δ/2
  let X : W → ℝ := fun w => fraction P - if P w then 1 else 0
  let Z : (D → W) → ℝ := fun g => ∑ d, (θ*X (g d)-θ^2)
  have hmgf : uniformMean (fun g : D → W => Real.exp (Z g)) ≤ 1 := by
    have hf : (fun g : D → W => Real.exp (Z g)) =
        (fun g => ∏ d, Real.exp (θ*X (g d)-θ^2)) := by
      funext g
      exact Real.exp_sum _ _
    rw [hf, uniformMean_product (fun _d : D => fun w => Real.exp (θ*X w-θ^2))]
    calc
      _ ≤ ∏ _d : D, (1:ℝ) := Finset.prod_le_prod
        (fun d _ => div_nonneg (Finset.sum_nonneg (fun w _ => Real.exp_nonneg _)) (by positivity))
        (fun d _ => uniformMean_centered_indicator_mgf P θ (by dsimp [θ]; positivity) (by dsimp [θ]; linarith))
      _ = _ := by simp
  have hbad (g : D → W) (hg : empirical P g ≤ fraction P-δ) :
      (Fintype.card D:ℝ)*δ^2/4 ≤ Z g := by
    have hN : 0 < (Fintype.card D:ℝ) := by positivity
    have hsum : (∑ d, if P (g d) then (1:ℝ) else 0) ≤
        (fraction P-δ)*(Fintype.card D:ℝ) := by
      apply (div_le_iff₀ hN).mp
      exact hg
    dsimp [Z, X, θ]
    simp only [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul]
    nlinarith
  exact WeightedKernel.exponential_tail (meanLinear (D → W))
    (fun f g h => uniformMean_mono f g h) _ Z ((Fintype.card D:ℝ)*δ^2/4) hbad hmgf

#print axioms uniformMean_product
#print axioms uniform_table_deficit

end
end WeightedReplacement
