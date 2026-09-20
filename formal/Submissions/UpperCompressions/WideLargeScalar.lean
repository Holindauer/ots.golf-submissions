import Submissions.UpperCompressions.WeightedBudgetClosure
import Submissions.UpperCompressions.WideHazardConstants

/-! ENNReal closure of the shared large-budget clock. -/
noncomputable section
open ENNReal
namespace WeightedBudgetClosure
open WeightedReference WeightedConstants

theorem large_shared_ennreal (B : ℕ) (q a t r e : ℝ≥0∞)
    (hclock : q+a+t ≤ B)
    (hr : r ≤ ENNReal.ofReal (C*(91/100)*kappa)*q +
      ENNReal.ofReal (C*(7/100)*kappa*(B:ℝ)))
    (he : e ≤ ENNReal.ofReal (kappa*(B:ℝ)/1000)) :
    ENNReal.ofReal (kappa/2)*a+r+ENNReal.ofReal postRate*t+e ≤
      ENNReal.ofReal ((991:ℝ)/1000*kappa*(B:ℝ)) := by
  have hk : 0 ≤ kappa := by norm_num [kappa]
  have hc : 0 ≤ C := by norm_num [C]
  have hrate : 0 ≤ C*(91/100)*kappa := by positivity
  have hshift : 0 ≤ C*(7/100)*kappa*(B:ℝ) := by positivity
  have herr : 0 ≤ kappa*(B:ℝ)/1000 := by positivity
  have ha : ENNReal.ofReal (kappa/2) ≤ ENNReal.ofReal (C*(91/100)*kappa) :=
    ofReal_le_ofReal (by norm_num [C,kappa])
  have ht : ENNReal.ofReal postRate ≤ ENNReal.ofReal (C*(91/100)*kappa) :=
    ofReal_le_ofReal postRate_le_large
  calc
    _ ≤ ENNReal.ofReal (C*(91/100)*kappa)*a+
        (ENNReal.ofReal (C*(91/100)*kappa)*q+ENNReal.ofReal (C*(7/100)*kappa*(B:ℝ)))+
        ENNReal.ofReal (C*(91/100)*kappa)*t+ENNReal.ofReal (kappa*(B:ℝ)/1000) :=
      add_le_add (add_le_add (add_le_add (mul_le_mul' ha le_rfl) hr)
        (mul_le_mul' ht le_rfl)) he
    _ = ENNReal.ofReal (C*(91/100)*kappa)*(q+a+t)+
        ENNReal.ofReal (C*(7/100)*kappa*(B:ℝ))+ENNReal.ofReal (kappa*(B:ℝ)/1000) := by ring
    _ ≤ ENNReal.ofReal (C*(91/100)*kappa)*B+
        ENNReal.ofReal (C*(7/100)*kappa*(B:ℝ))+ENNReal.ofReal (kappa*(B:ℝ)/1000) :=
      add_le_add (add_le_add (mul_le_mul' le_rfl hclock) le_rfl) le_rfl
    _ = _ := by
      rw [← ofReal_natCast B, ← ofReal_mul hrate,
        ← ofReal_add (mul_nonneg hrate (Nat.cast_nonneg B)) hshift,
        ← ofReal_add (add_nonneg (mul_nonneg hrate (Nat.cast_nonneg B)) hshift) herr]
      congr 1
      unfold C
      ring

theorem all_exception_margin_ennreal (B : ℕ) (hB : 995 ≤ B)
    (hcap : (B:ℝ) ≤ (2:ℝ)^127) :
    ENNReal.ofReal (((2:ℝ)^1792)⁻¹)+ENNReal.ofReal (((2:ℝ)^512)⁻¹)+
      (1+(B:ℝ≥0∞))*(2:ℝ≥0∞)⁻¹^761 ≤ ENNReal.ofReal (kappa*(B:ℝ)/1000) := by
  have h := ofReal_le_ofReal (WeightedHazardConstants.all_exception_margin (B:ℝ)
    (by exact_mod_cast hB) hcap)
  rw [ofReal_add (by positivity) (by positivity),
    ofReal_add (by positivity) (by positivity),
    ofReal_mul (by positivity), ofReal_add (by positivity) (by positivity)] at h
  norm_num only [ofReal_one, ofReal_natCast, ofReal_inv_of_pos (by norm_num : (0:ℝ)<2),
    ofReal_inv_of_pos (by positivity : (0:ℝ)<2^761),
    ofReal_pow (by norm_num : (0:ℝ)≤2), ofReal_ofNat, inv_pow] at h
  simpa only [ENNReal.inv_pow,
    add_comm (ENNReal.ofReal (((2:ℝ)^512)⁻¹)) (ENNReal.ofReal (((2:ℝ)^1792)⁻¹))] using h

#print axioms large_shared_ennreal
#print axioms all_exception_margin_ennreal
end WeightedBudgetClosure
