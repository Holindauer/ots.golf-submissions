import Submissions.UpperCompressions.WeightedScoreMGF
noncomputable section
open scoped BigOperators
namespace WeightedEmpirical
open WeightedRow.Weights
variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- A convenient conservative sufficient condition for the linear boundary. -/
theorem rate_le_linear (w : WeightedRow.Weights ι) (G θ δ : ℝ)
    (hG : 0 ≤ G) (hθ : 0 ≤ θ) (hθG : θ*G ≤ 1)
    (hsmall : θ*G*w.mean ≤ δ/2) : rate w θ G ≤ θ*δ/2 := by
  have hm : 0 ≤ w.mean := by
    unfold mean
    exact Finset.sum_nonneg (fun i _ => mul_nonneg (w.p_pos i).le (w.g_nonneg i))
  have hn : 0 ≤ θ^2*(G*w.mean) := by positivity
  have hd : 1 ≤ 2*(1-θ*G/3) := by linarith
  calc
    rate w θ G ≤ θ^2*(G*w.mean) := div_le_self hn hd
    _ = θ*(θ*G*w.mean) := by ring
    _ ≤ θ*(δ/2) := mul_le_mul_of_nonneg_left hsmall hθ
    _ = θ*δ/2 := by ring

def mixedTheta (κ : ℝ) : ℝ := 1/(1000*(2^20:ℝ)*κ)

/-- Explicit mixed72 constants for global .01κ max(q,N/10) concentration.
This deliberately leaves enormous exponent slack. -/
theorem mixed_global_constants (w : WeightedRow.Weights ι) (κ : ℝ)
    (hκ : 0 < κ) (hm : w.mean ≤ κ) :
    0 < mixedTheta κ ∧
    mixedTheta κ*((2^20:ℝ)*κ/2) < 3 ∧
    rate w (mixedTheta κ) ((2^20:ℝ)*κ/2) ≤ mixedTheta κ*(κ/100)/2 ∧
    (2^40:ℝ) ≤ mixedTheta κ*(κ/100)*((2^86:ℝ)/10)/2 := by
  have hθ : 0 < mixedTheta κ := by unfold mixedTheta; positivity
  have hp : mixedTheta κ*((2^20:ℝ)*κ/2) = 1/2000 := by
    unfold mixedTheta
    field_simp
    <;> ring
  refine ⟨hθ, ?_, ?_, ?_⟩
  · rw [hp]
    norm_num
  · apply rate_le_linear w _ _ _ (by positivity) hθ.le
    · rw [hp]; norm_num
    · rw [hp]
      nlinarith
  · have he : mixedTheta κ*(κ/100)*((2^86:ℝ)/10)/2 = (2^66:ℝ)/2000000 := by
      unfold mixedTheta
      field_simp
      <;> ring
    rw [he]
    norm_num

#print axioms rate_le_linear
#print axioms mixed_global_constants
end WeightedEmpirical
