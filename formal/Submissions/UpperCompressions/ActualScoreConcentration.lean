import Submissions.UpperCompressions.ActualWeightedMoments
import Submissions.UpperCompressions.WeightedLowerMGF
import Submissions.UpperCompressions.ActualLinearBoundary
import Submissions.UpperCompressions.LinearBoundaryConstants
import Submissions.UpperCompressions.RowConcentrationConstants

/-! Concentration of actual fresh-query score statistics. The only oracle-law
hypothesis is the exact primitive-query class law, discharged separately by the
concrete shared-cache implementation. No terminal concentration is assumed. -/
noncomputable section
open OracleSpec OracleComp OracleComp.EvalDist
open scoped Classical BigOperators ENNReal
namespace WeightedActualScore
open WeightedRealExecution WeightedRow.Weights WeightedOracleExecution WeightedFirstHit WeightedEmpirical

set_option maxHeartbeats 800000
variable {ι S α : Type} [Fintype ι] [DecidableEq ι]
variable (w : WeightedRow.Weights ι)
    (impl : QueryImpl OptimalOTS.Spec (StateT S ProbComp))
    (qCount : S → ℕ) (counts : S → (ι → ℕ))
    (fresh : OptimalOTS.Spec.Domain → S → Bool)
    (hlaw : ∀ t s (f : ℕ → (ι → ℕ) → ℝ),
      realEval ((impl t).run s) (fun out => f (qCount out.2) (counts out.2)) =
        w.expect (fun x => f (step (fresh t s) (qCount s) (counts s) x).1
          (step (fresh t s) (qCount s) (counts s) x).2))

def signedM1 (lower : Bool) (s : S) : ℝ :=
  if lower then -w.M1 (qCount s) (counts s) else w.M1 (qCount s) (counts s)

include fresh hlaw

/-- Both upper and lower exponential drift follow from the same exact fresh-query law. -/
theorem query_mgf (lower : Bool) (G θ : ℝ)
    (hG : 0 ≤ G) (hg : ∀ i, w.g i ≤ G) (hθ : 0 ≤ θ) (hθG : θ*G < 3)
    (t : OptimalOTS.Spec.Domain) (s : S) :
    expectedValue ((impl t).run s)
      (fun out => ENNReal.ofReal (Real.exp (θ*signedM1 w qCount counts lower out.2-
        rate w θ G*(qCount out.2:ℝ)))) ≤
      ENNReal.ofReal (Real.exp (θ*signedM1 w qCount counts lower s-rate w θ G*(qCount s:ℝ))) := by
  rw [← ofReal_realEval _ _ (fun _ => Real.exp_nonneg _)]
  apply ENNReal.ofReal_le_ofReal
  cases lower with
  | false =>
    change realEval ((impl t).run s)
      (fun out => Real.exp (θ*w.M1 (qCount out.2) (counts out.2)-rate w θ G*(qCount out.2:ℝ))) ≤ _
    rw [hlaw t s (fun q k => Real.exp (θ*w.M1 q k-rate w θ G*(q:ℝ)))]
    exact score_step_mgf w G θ hG hg hθ hθG (fresh t s) (qCount s) (counts s)
  | true =>
    change realEval ((impl t).run s)
      (fun out => Real.exp (θ*(-w.M1 (qCount out.2) (counts out.2))-rate w θ G*(qCount out.2:ℝ))) ≤ _
    rw [hlaw t s (fun q k => Real.exp (θ*(-w.M1 q k)-rate w θ G*(q:ℝ)))]
    exact lower_score_step_mgf w G θ hG hg hθ hθG (fresh t s) (qCount s) (counts s)

theorem global_boundary (lower : Bool) (G θ δ Q : ℝ)
    (hG : 0 ≤ G) (hg : ∀ i, w.g i ≤ G) (hθ : 0 ≤ θ) (hθG : θ*G < 3)
    (hδ : 0 ≤ δ) (hrate : rate w θ G ≤ θ*δ/2)
    (oa : OracleComp OptimalOTS.Spec α) (s₀ : S)
    (hq0 : qCount s₀ = 0) (hk0 : counts s₀ = fun _ => 0) :
    let hit := fun (_ : ℕ) (s : S) =>
      δ*max (qCount s:ℝ) Q ≤ signedM1 w qCount counts lower s
    let kill := fun (_ : ℕ) (_ : S) => False
    Pr[fun out => out.2.status = .hit |
      (simulateQ (stoppedImpl impl hit kill) oa).run (classify hit kill 0 s₀)] ≤
      ENNReal.ofReal (Real.exp (-(θ*δ*Q/2))) := by
  exact actual_linear_boundary impl qCount (signedM1 w qCount counts lower)
    θ (rate w θ G) δ Q hθ hδ hrate
    (query_mgf w impl qCount counts fresh hlaw lower G θ hG hg hθ hθG)
    oa s₀ hq0 (by cases lower <;> simp [signedM1, M1, score, hq0, hk0])

/-- The row hit is explicitly restricted to at most N fresh row inputs.
Connecting that restriction to the finite nonce domain is a separate counting invariant. -/
theorem row_freedman (lower : Bool) (G N a : ℝ)
    (hG : 0 < G) (hg : ∀ i, w.g i ≤ G) (hN : 0 < N) (ha : 0 < a)
    (oa : OracleComp OptimalOTS.Spec α) (s₀ : S)
    (hq0 : qCount s₀ = 0) (hk0 : counts s₀ = fun _ => 0) :
    let hit := fun (_ : ℕ) (s : S) =>
      (qCount s:ℝ) ≤ N ∧ a ≤ signedM1 w qCount counts lower s
    let kill := fun (_ : ℕ) (s : S) => N < (qCount s:ℝ)
    Pr[fun out => out.2.status = .hit |
      (simulateQ (stoppedImpl impl hit kill) oa).run (classify hit kill 0 s₀)] ≤
      ENNReal.ofReal (Real.exp (-a^2/(2*(G^2*N+G*a/3)))) := by
  dsimp only
  let hit := fun (_ : ℕ) (s : S) =>
    (qCount s:ℝ) ≤ N ∧ a ≤ signedM1 w qCount counts lower s
  let kill := fun (_ : ℕ) (s : S) => N < (qCount s:ℝ)
  have hm0 : 0 ≤ w.mean := by
    simpa only [mean_scoreJump] using w.expect_nonneg w.scoreJump
      (fun x => (w.scoreJump_bounds G hG.le hg x).1)
  have hmG : w.mean ≤ G := by
    simpa only [mean_scoreJump] using w.expect_le_const w.scoreJump G
      (fun x => (w.scoreJump_bounds G hG.le hg x).2)
  apply actual_stopped_freedman impl oa
    (fun _ s => signedM1 w qCount counts lower s)
    (fun _ s => G*w.mean*(qCount s:ℝ)) s₀ a (G^2*N) G ha (by positivity) hG.le
    (by cases lower <;> simp [signedM1, M1, score, hq0, hk0])
    (by simp [hq0]) hit kill
  · intro θ hθ hθG t n s _ _
    have he (r : ℝ) : θ^2*(G*w.mean*r)/(2*(1-θ*G/3)) = rate w θ G*r := by
      unfold rate
      ring
    simp only [he]
    exact query_mgf w impl qCount counts fresh hlaw lower G θ hG.le hg hθ.le hθG t s
  · intro n s hs
    exact hs.2
  · intro n s hs
    change G*w.mean*(qCount s:ℝ) ≤ G^2*N
    calc
      G*w.mean*(qCount s:ℝ) ≤ G*w.mean*N := mul_le_mul_of_nonneg_left hs.1 (mul_nonneg hG.le hm0)
      _ ≤ G*G*N := by gcongr
      _ = G^2*N := by ring

/-- Concrete global mixed72 margin, uniform in the program length and paid budget. -/
theorem mixed_global (κ : ℝ) (hκ : 0 < κ) (hm : w.mean ≤ κ)
    (hg : ∀ i, w.g i ≤ (2^20:ℝ)*κ/2)
    (oa : OracleComp OptimalOTS.Spec α) (s₀ : S)
    (hq0 : qCount s₀ = 0) (hk0 : counts s₀ = fun _ => 0) :
    let hit := fun (_ : ℕ) (s : S) =>
      (κ/100)*max (qCount s:ℝ) ((2^86:ℝ)/10) ≤ signedM1 w qCount counts false s
    let kill := fun (_ : ℕ) (_ : S) => False
    Pr[fun out => out.2.status = .hit |
      (simulateQ (stoppedImpl impl hit kill) oa).run (classify hit kill 0 s₀)] ≤
      ENNReal.ofReal (Real.exp (-(2^40:ℝ))) := by
  obtain ⟨hθ, hθG, hc, he⟩ := mixed_global_constants w κ hκ hm
  have hx := global_boundary w impl qCount counts fresh hlaw false
    ((2^20:ℝ)*κ/2) (mixedTheta κ) (κ/100) ((2^86:ℝ)/10)
    (by positivity) hg hθ.le hθG (by positivity) hc oa s₀ hq0 hk0
  apply hx.trans
  apply ENNReal.ofReal_le_ofReal
  exact Real.exp_le_exp.mpr (neg_le_neg he)

/-- Concrete row margin for either tail. Set G=1 for prefix indicators and
G=Lκ for rowS or rowU. The counted finite-domain restriction is explicit. -/
theorem mixed_row (lower : Bool) (G : ℝ) (hG : 0 < G) (hg : ∀ i, w.g i ≤ G)
    (oa : OracleComp OptimalOTS.Spec α) (s₀ : S)
    (hq0 : qCount s₀ = 0) (hk0 : counts s₀ = fun _ => 0) :
    let a := G*(2^86:ℝ)/(100*(2^20:ℝ))
    let hit := fun (_ : ℕ) (s : S) =>
      (qCount s:ℝ) ≤ 2^86 ∧ a ≤ signedM1 w qCount counts lower s
    let kill := fun (_ : ℕ) (s : S) => (2^86:ℝ) < (qCount s:ℝ)
    Pr[fun out => out.2.status = .hit |
      (simulateQ (stoppedImpl impl hit kill) oa).run (classify hit kill 0 s₀)] ≤
      ENNReal.ofReal (Real.exp (-(2^30:ℝ))) := by
  obtain ⟨ha, hv, he⟩ := mixed_row_exponent G hG
  have hx := row_freedman w impl qCount counts fresh hlaw lower G (2^86:ℝ)
    (G*(2^86:ℝ)/(100*(2^20:ℝ))) hG hg (by positivity) ha oa s₀ hq0 hk0
  apply hx.trans
  apply ENNReal.ofReal_le_ofReal
  apply Real.exp_le_exp.mpr
  simpa only [neg_div] using neg_le_neg he

#print axioms mixed_global
#print axioms mixed_row

#print axioms query_mgf
#print axioms global_boundary
#print axioms row_freedman
end WeightedActualScore
