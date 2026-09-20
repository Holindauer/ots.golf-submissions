import Submissions.UpperCompressions.Availability
import Submissions.UpperCompressions.IUB

namespace WeightedAvailability
open ENNReal
noncomputable section

def miss : ℝ≥0∞ := 524243/524288

theorem replacement_envelope :
    (miss + (2:ℝ≥0∞)^20 / 2^86)^(2^20:ℕ) ≤ 1/(2:ℝ≥0∞)^129 := by
  have h := ENNReal.ofReal_le_ofReal empirical_failure
  rw [ENNReal.ofReal_pow (by norm_num : (0:ℝ) ≤ 1-8999/104857600)] at h
  have hb : ENNReal.ofReal (1-(8999:ℝ)/104857600) =
      (104848601:ℝ≥0∞)/104857600 := by norm_num [ENNReal.ofReal_div_of_pos]
  have ht : ENNReal.ofReal (((2:ℝ)^129)⁻¹) = 1/(2:ℝ≥0∞)^129 := by
    rw [ENNReal.ofReal_inv_of_pos (by positivity), ENNReal.ofReal_pow (by norm_num)]
    norm_num
  rw [hb,ht] at h
  have hbase : miss + (2:ℝ≥0∞)^20/2^86 ≤ (104848601:ℝ≥0∞)/104857600 := by
    have hr : (524243:ℝ)/524288+(2:ℝ)^20/2^86 ≤ 104848601/104857600 := by norm_num
    have he := ENNReal.ofReal_le_ofReal hr
    rw [ENNReal.ofReal_add (by positivity) (by positivity)] at he
    rw [ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ)<524288),
      ENNReal.ofReal_div_of_pos (by positivity : (0:ℝ)<2^86),
      ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ)<104857600)] at he
    simpa only [miss, ENNReal.ofReal_ofNat,
      ENNReal.ofReal_pow (by norm_num : (0:ℝ)≤2)] using he
  exact (pow_le_pow_left' hbase _).trans h

#print axioms replacement_envelope
end
end WeightedAvailability
