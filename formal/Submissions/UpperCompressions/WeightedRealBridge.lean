import Submissions.UpperCompressions.ActualRealExpectation

/-! Real/ENNReal expectation transport on the actual supported execution. -/
noncomputable section
namespace WeightedRealExecution
open OracleSpec OracleComp OracleComp.EvalDist
open scoped Classical ENNReal
variable {α : Type}

theorem realEval_congr_on_support (oa : ProbComp α) (f g : α → ℝ)
    (h : ∀ a ∈ support oa,f a=g a) : realEval oa f=realEval oa g :=
  le_antisymm (realEval_mono_of_support oa f g (fun a ha => (h a ha).le))
    (realEval_mono_of_support oa g f (fun a ha => (h a ha).symm.le))

theorem ofReal_realEval_on_support (oa : ProbComp α) (f : α → ℝ)
    (hf : ∀ a ∈ support oa,0≤f a) :
    ENNReal.ofReal (realEval oa f)=expectedValue oa (fun a => ENNReal.ofReal (f a)) := by
  let g := fun a => max (f a) 0
  have hfg : realEval oa f=realEval oa g :=
    realEval_congr_on_support oa f g (fun a ha => (max_eq_left (hf a ha)).symm)
  rw [hfg,ofReal_realEval oa g (fun a => le_max_right _ _)]
  have hg : (fun a => ENNReal.ofReal (g a))=(fun a => ENNReal.ofReal (f a)) := by
    funext a
    by_cases h : 0≤f a
    · rw [show g a=f a from max_eq_left h]
    · have hn : f a≤0 := le_of_not_ge h
      rw [show g a=0 from max_eq_right hn,ENNReal.ofReal_zero,ENNReal.ofReal_of_nonpos hn]
  rw [hg]

theorem E_ofReal_ne_top (oa : ProbComp α) (f : α → ℝ) (hf : ∀ a ∈ support oa,0≤f a) :
    expectedValue oa (fun a => ENNReal.ofReal (f a))≠⊤ := by
  rw [← ofReal_realEval_on_support oa f hf]
  exact ENNReal.ofReal_ne_top

theorem realEval_nonneg_on_support (oa : ProbComp α) (f : α → ℝ)
    (hf : ∀ a ∈ support oa,0≤f a) : 0≤realEval oa f := by
  have h := realEval_mono_of_support oa (fun _ => 0) f hf
  rwa [realEval_const] at h

#print axioms ofReal_realEval_on_support
end WeightedRealExecution
