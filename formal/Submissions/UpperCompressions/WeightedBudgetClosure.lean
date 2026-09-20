import Submissions.UpperCompressions.WideSecurityData
import Submissions.UpperCompressions.StoppingExpectation

/-! Final numerical budget implications. The game-to-payoff inequalities and
stochastic moments are explicit hypotheses; this file does not claim Secure. -/
noncomputable section
namespace WeightedBudgetClosure
open WeightedReference WeightedConstants
open OptimalOTS.WeightedConstruction.WeightedSchedule

def C : ℝ := 99/98
def postRate : ℝ := kappa/2+C*(kappa*(2/5)+kappa/100)

theorem postRate_ge_auth : kappa/2 ≤ postRate := by norm_num [postRate,C,kappa]
theorem postRate_le_large : postRate ≤ C*(91/100)*kappa := by norm_num [postRate,C,kappa]
theorem postRate_le_small : postRate ≤ C*(223/250)*(11/10)*kappa := by
  norm_num [postRate,C,kappa]

theorem actual_mean_nonneg : 0 ≤ mean := by
  unfold mean
  exact Finset.sum_nonneg fun i _ => mul_nonneg (classProbability_pos i).le (referenceWeight_nonneg i)

/-- All numerical hypotheses in the small-budget stopped estimate are now
theorems for the concrete decoder. Only its execution moments remain inputs. -/
theorem small_payoff {Ω : Type*} (E : (Ω → ℝ) →ₗ[ℝ] ℝ)
    (hmono : ∀ f g, (∀ ω, f ω ≤ g ω) → E f ≤ E g)
    (hnorm : E (fun _ => 1)=1)
    (τ S P : Ω → ℝ) (K : ℝ) (hK : 0 ≤ K) (hKN : K ≤ (2:ℝ)^86/10)
    (hτ0 : ∀ ω,0 ≤ τ ω) (hτK : ∀ ω,τ ω ≤ K)
    (hm1 : E (fun ω => S ω-mean*τ ω)=0)
    (hm2 : E (fun ω => P ω-τ ω*S ω+mean*τ ω*(τ ω+1)/2)=0)
    (hmSq : E (fun ω => (S ω-mean*τ ω)^2) ≤ K*((L:ℝ)*kappa/2)*mean) :
    E (fun ω => C*(S ω+2*P ω/(2:ℝ)^86)+postRate*(K-τ ω))+kappa*K/1000 ≤
      (243337:ℝ)/245000*kappa*K := by
  have hh : mean ≤ kappa := mean_le.trans (by
    have hk : 0 ≤ kappa := by unfold kappa; positivity
    nlinarith)
  have h := WeightedStopping.stopped_mixed72_payoff E hmono hnorm τ S P C mean postRate
    kappa K ((L:ℝ)*kappa/2) (by norm_num [C]) (by norm_num [C])
    actual_mean_nonneg (by unfold kappa; positivity) hK (by unfold kappa; positivity)
    hKN (by norm_num [L]) hh hτ0 hτK hm1 hm2 hmSq
  have hm : 11*C*mean/10 ≤ C*(223/250)*(11/10)*kappa := by
    have h := mul_le_mul_of_nonneg_left mean_le (show 0 ≤ 11*C/10 by norm_num [C])
    nlinarith
  have hb := mul_le_mul_of_nonneg_left (max_le postRate_le_small hm) hK
  have he : K*(C*(223/250)*(11/10)*kappa)+2*(kappa*K/1000) =
      (243337:ℝ)/245000*kappa*K := by unfold C; ring
  linarith

/-- The large-budget payoff combines cached replay, pre-sign authentication,
and the averaged post-sign continuation using their actual common budget. -/
theorem large_payoff (K q a t R : ℝ)
    (hq : 0 ≤ q) (ha : 0 ≤ a) (ht : 0 ≤ t) (hb : q+a+t ≤ K)
    (hR : R ≤ (91:ℝ)/100*kappa*q+(7:ℝ)/100*kappa*K) :
    C*R+(kappa/2)*a+postRate*t+kappa*K/1000 ≤ (991:ℝ)/1000*kappa*K := by
  have hCr := mul_le_mul_of_nonneg_left hR (show 0 ≤ C by norm_num [C])
  have hArate : kappa/2 ≤ C*(91/100)*kappa := by norm_num [C,kappa]
  have hA := mul_le_mul_of_nonneg_right hArate ha
  have hT := mul_le_mul_of_nonneg_right postRate_le_large ht
  have hB := mul_le_mul_of_nonneg_left hb
    (show 0 ≤ C*(91/100)*kappa by norm_num [C,kappa])
  have he : C*(91/100)*kappa*K+C*(7/100)*kappa*K+kappa*K/1000 =
      (991:ℝ)/1000*kappa*K := by unfold C; ring
  nlinarith

theorem small_below_security (K : ℝ) (hK : 0 ≤ K) :
    (243337:ℝ)/245000*kappa*K ≤ kappa*K := by
  have hk : 0 ≤ kappa*K := mul_nonneg (by unfold kappa; positivity) hK
  nlinarith

theorem large_below_security (K : ℝ) (hK : 0 ≤ K) :
    (991:ℝ)/1000*kappa*K ≤ kappa*K := by
  have hk : 0 ≤ kappa*K := mul_nonneg (by unfold kappa; positivity) hK
  nlinarith

#print axioms small_payoff
#print axioms large_payoff
end WeightedBudgetClosure
