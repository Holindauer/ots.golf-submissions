import Submissions.UpperCompressions.ActualRealExpectation
import Submissions.UpperCompressions.WeightedMoments

noncomputable section
open OracleSpec OracleComp OracleComp.EvalDist
open scoped Classical ENNReal BigOperators
namespace WeightedRealExecution

set_option maxHeartbeats 800000
variable {α : Type} [Fintype α] [SampleableType α]

private theorem realEval_uniform_nonneg (f : α → ℝ) (hf : ∀ a, 0 ≤ f a) :
    realEval ($ᵗ α) f = (∑ a, f a) / Fintype.card α := by
  have hl := ofReal_realEval ($ᵗ α) f hf
  rw [expectedValue_def, tsum_fintype] at hl
  simp only [probOutput_uniformSample] at hl
  rw [← Finset.mul_sum] at hl
  have hc : 0 < (Fintype.card α:ℝ) := by positivity
  have hs : 0 ≤ ∑ a, f a := Finset.sum_nonneg (fun a _ => hf a)
  have he : ENNReal.ofReal (realEval ($ᵗ α) f) =
      ENNReal.ofReal ((∑ a, f a) / Fintype.card α) := by
    rw [hl, div_eq_mul_inv, ENNReal.ofReal_mul hs,
      ENNReal.ofReal_inv_of_pos hc, ENNReal.ofReal_natCast,
      ENNReal.ofReal_sum_of_nonneg (fun a _ => hf a), mul_comm]
  have hx := congrArg ENNReal.toReal he
  simpa only [ENNReal.toReal_ofReal (realEval_nonneg _ _ hf),
    ENNReal.toReal_ofReal (div_nonneg hs hc.le)] using hx

/-- The exact signed average for the library's actual uniform-sampling computation. -/
theorem realEval_uniform (f : α → ℝ) :
    realEval ($ᵗ α) f = (∑ a, f a) / Fintype.card α := by
  have hf : f = fun a => max (f a) 0 - max (-f a) 0 := by
    funext a
    rcases le_total (f a) 0 with h | h
    · simp [max_eq_right h, max_eq_left (neg_nonneg.mpr h)]
    · simp [max_eq_left h, max_eq_right (neg_nonpos.mpr h)]
  rw [hf, realEval_sub,
    realEval_uniform_nonneg _ (fun a => le_max_right _ _),
    realEval_uniform_nonneg _ (fun a => le_max_right _ _),
    Finset.sum_sub_distrib, sub_div]

@[simp] theorem realEval_map {β : Type} (oa : ProbComp α) (g : α → β) (f : β → ℝ) :
    realEval (g <$> oa) f = realEval oa (fun a => f (g a)) := by
  rw [map_eq_bind_pure_comp, realEval_bind]
  simp only [Function.comp_apply, realEval_pure]

theorem realEval_decoded_uniform {ι : Type} [Fintype ι] [DecidableEq ι]
    (w : WeightedRow.Weights ι) (decode : α → Option ι)
    (hfiber : ∀ x, ((Finset.univ.filter (fun b => decode b=x)).card:ℝ) /
      Fintype.card α = w.classMass x) (f : Option ι → ℝ) :
    realEval ($ᵗ α) (fun b => f (decode b)) = w.expect f :=
  (realEval_uniform _).trans (w.uniform_decoder_expect decode hfiber f)

#print axioms realEval_uniform
#print axioms realEval_decoded_uniform
end WeightedRealExecution
