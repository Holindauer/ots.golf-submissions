import Submissions.UpperCompressions.WeightedMoments
import Submissions.UpperCompressions.BernsteinMGF

noncomputable section
open scoped Classical BigOperators
namespace WeightedEmpirical
open WeightedRow.Weights
set_option maxHeartbeats 800000
variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Positive normalized expectation for the decoder's class distribution. -/
def expectLinear (w : WeightedRow.Weights ι) : (Option ι → ℝ) →ₗ[ℝ] ℝ where
  toFun := w.expect
  map_add' := w.expect_add
  map_smul' c f := w.expect_smul c f

/-- The per-fresh-query Bernstein compensator for a score bounded by G. -/
def rate (w : WeightedRow.Weights ι) (θ G : ℝ) : ℝ :=
  θ^2*(G*w.mean)/(2*(1-θ*G/3))

/-- Exponential drift including cached queries and private randomness. -/
theorem score_step_mgf (w : WeightedRow.Weights ι) (G θ : ℝ)
    (hG : 0 ≤ G) (hg : ∀ i, w.g i ≤ G) (hθ : 0 ≤ θ) (hθG : θ*G < 3)
    (fresh : Bool) (q : ℕ) (k : ι → ℕ) :
    w.expect (fun x => Real.exp (θ*w.M1 (step fresh q k x).1 (step fresh q k x).2-
      rate w θ G*((step fresh q k x).1:ℝ))) ≤
      Real.exp (θ*w.M1 q k-rate w θ G*(q:ℝ)) := by
  cases fresh with
  | false => simp only [step_not_fresh, expect_const, le_refl]
  | true =>
    have hnorm : expectLinear w (fun _ => 1) = 1 := w.expect_const 1
    have hm : expectLinear w (fun x => w.scoreJump x-w.mean) = 0 := by
      change w.expect (fun x => w.scoreJump x-w.mean) = 0
      rw [expect_sub, mean_scoreJump, expect_const, sub_self]
    have hb : ∀ x, |w.scoreJump x-w.mean| ≤ G := by
      intro x
      have hh := w.centered_abs_le w.scoreJump G (w.scoreJump_bounds G hG hg) x
      simpa only [mean_scoreJump] using hh
    have hs : expectLinear w (fun x => (w.scoreJump x-w.mean)^2) ≤ G*w.mean :=
      w.score_variance_le G hG hg
    have hx := WeightedMGF.compensated_mgf (expectLinear w) w.expect_mono hnorm
      (fun x => w.scoreJump x-w.mean) θ G (G*w.mean) hθ hG hθG hb hm hs
    change w.expect (fun x => Real.exp (θ*(w.scoreJump x-w.mean)-rate w θ G)) ≤ 1 at hx
    have hf : (fun x => Real.exp (θ*w.M1 (step true q k x).1 (step true q k x).2-
        rate w θ G*((step true q k x).1:ℝ))) =
      (fun x => Real.exp (θ*w.M1 q k-rate w θ G*(q:ℝ))*
        Real.exp (θ*(w.scoreJump x-w.mean)-rate w θ G)) := by
      funext x
      simp only [step, ite_true, M1_increment, Nat.cast_add, Nat.cast_one]
      rw [← Real.exp_add]
      congr 1
      ring
    rw [hf, expect_smul]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hx
      (Real.exp_nonneg (θ*w.M1 q k-rate w θ G*(q:ℝ)))

#print axioms score_step_mgf
end WeightedEmpirical
