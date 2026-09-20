import Submissions.UpperCompressions.WeightedScoreMGF
noncomputable section
open scoped Classical BigOperators
namespace WeightedEmpirical
open WeightedRow.Weights
set_option maxHeartbeats 800000
variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem lower_score_step_mgf (w : WeightedRow.Weights ι) (G θ : ℝ)
    (hG : 0 ≤ G) (hg : ∀ i, w.g i ≤ G) (hθ : 0 ≤ θ) (hθG : θ*G < 3)
    (fresh : Bool) (q : ℕ) (k : ι → ℕ) :
    w.expect (fun x => Real.exp (θ*(-w.M1 (step fresh q k x).1 (step fresh q k x).2)-
      rate w θ G*((step fresh q k x).1:ℝ))) ≤
      Real.exp (θ*(-w.M1 q k)-rate w θ G*(q:ℝ)) := by
  cases fresh with
  | false => simp only [step_not_fresh, expect_const, le_refl]
  | true =>
    have hnorm : expectLinear w (fun _ => 1) = 1 := w.expect_const 1
    have hm : expectLinear w (fun x => w.mean-w.scoreJump x) = 0 := by
      change w.expect (fun x => w.mean-w.scoreJump x) = 0
      rw [expect_sub, mean_scoreJump, expect_const, sub_self]
    have hb : ∀ x, |w.mean-w.scoreJump x| ≤ G := by
      intro x
      have hh := w.centered_abs_le w.scoreJump G (w.scoreJump_bounds G hG hg) x
      simpa only [mean_scoreJump, abs_sub_comm] using hh
    have hs : expectLinear w (fun x => (w.mean-w.scoreJump x)^2) ≤ G*w.mean := by
      have he : (fun x => (w.mean-w.scoreJump x)^2) =
          (fun x => (w.scoreJump x-w.mean)^2) := by funext x; ring
      rw [he]
      exact w.score_variance_le G hG hg
    have hx := WeightedMGF.compensated_mgf (expectLinear w) w.expect_mono hnorm
      (fun x => w.mean-w.scoreJump x) θ G (G*w.mean) hθ hG hθG hb hm hs
    change w.expect (fun x => Real.exp (θ*(w.mean-w.scoreJump x)-rate w θ G)) ≤ 1 at hx
    have hf : (fun x => Real.exp (θ*(-w.M1 (step true q k x).1 (step true q k x).2)-
        rate w θ G*((step true q k x).1:ℝ))) =
      (fun x => Real.exp (θ*(-w.M1 q k)-rate w θ G*(q:ℝ))*
        Real.exp (θ*(w.mean-w.scoreJump x)-rate w θ G)) := by
      funext x
      simp only [step, ite_true, M1_increment, Nat.cast_add, Nat.cast_one]
      rw [← Real.exp_add]
      congr 1
      ring
    rw [hf, expect_smul]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hx
      (Real.exp_nonneg (θ*(-w.M1 q k)-rate w θ G*(q:ℝ)))

#print axioms lower_score_step_mgf
end WeightedEmpirical
