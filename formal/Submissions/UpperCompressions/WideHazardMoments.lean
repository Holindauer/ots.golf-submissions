import Submissions.UpperCompressions.WideHazardLaw

/-! Actual primitive-query drift and variance of the clipped row hazard.
The row-score premise is explicit; no complete-game security statement is made. -/
noncomputable section
open OracleSpec OracleComp
open scoped Classical BigOperators
namespace OptimalOTS.WeightedConstruction.WideHazard
open WeightedSchedule WideDomains WeightedRow.Weights
open WeightedRealExecution WeightedDualCache WeightedReference WeightedConstants
attribute [local irreducible] Finset.univ Finset.filter queryPhase rowCount globalCounts rowCounts

def gain (s : Phase) (m : Message) (c : hashSpec.QueryCache) : Option (Fin M) → ℝ :=
  match s with
  | .idle => fun _ => 0
  | .outside => securityWeights.positiveOutside N (rowCount m c) (globalCounts c) (rowCounts m c)
  | .inside => securityWeights.positiveInside N (rowCount m c) (globalCounts c) (rowCounts m c)

def shift (s : Phase) (c : hashSpec.QueryCache) : ℝ :=
  match s with
  | .inside => securityWeights.seen (globalCounts c)/N
  | _ => 0

def jumpBound : ℝ := (L:ℝ)*kappa/2+2*(L:ℝ)/N

def drift (m : Message) (t : Spec.Domain) (c : hashSpec.QueryCache) : ℝ :=
  realEval ((oracleImpl t).run c) (fun out => hazard m out.2-hazard m c)

theorem delta_gain_shift (s : Phase) (m : Message) (c : hashSpec.QueryCache)
    (x : Option (Fin M)) : delta s m c x = gain s m c x-shift s c := by
  cases s with
  | idle => simp [delta,nextHazard,after,hazard,gain,shift]
  | outside =>
    have h := securityWeights.increment_outside N (rowCount m c) (globalCounts c) (rowCounts m c) x
    cases x <;> simpa only [delta,nextHazard,after,advance,hazard,gain,shift,
      afterOutside,sub_zero] using h
  | inside =>
    have h := securityWeights.increment_inside N (rowCount m c) (globalCounts c) (rowCounts m c) x
    cases x <;> simpa only [delta,nextHazard,after,advance,hazard,gain,shift,
      afterInside] using h

theorem seen_le_one (c : hashSpec.QueryCache) : securityWeights.seen (globalCounts c) ≤ 1 := by
  calc
    securityWeights.seen (globalCounts c) ≤ ∑ i : Fin M,referenceWeight i := by
      apply Finset.sum_le_sum
      intro i hi
      split_ifs
      · exact referenceWeight_nonneg i
      · exact le_rfl
    _ = 1-failure := referenceWeight_sum
    _ ≤ 1 := sub_le_self _ failure_nonneg

theorem shift_le (s : Phase) (c : hashSpec.QueryCache) : shift s c ≤ 1/N := by
  cases s with
  | idle => exact le_of_lt (by norm_num [shift,N])
  | outside => exact le_of_lt (by norm_num [shift,N])
  | inside => exact div_le_div_of_nonneg_right (seen_le_one c) (by norm_num [N])

theorem gain_bounds (m : Message) (t : Spec.Domain) (c : hashSpec.QueryCache)
    (x : Option (Fin M)) :
    0 ≤ gain (queryPhase m t c) m c x ∧ gain (queryPhase m t c) m c x ≤ jumpBound := by
  cases hs : queryPhase m t c with
  | idle => constructor <;> norm_num [gain,jumpBound,L,kappa,N]
  | outside =>
    exact securityWeights.positiveOutside_bounds N (by norm_num [N]) (rowCount m c)
      (rowCount_le m c) (globalCounts c) (rowCounts m c) (row_le_global m c)
      ((L:ℝ)*kappa/2) L (by norm_num [L,kappa]) (by norm_num [L])
      referenceWeight_le weight_ratio_le x
  | inside =>
    exact securityWeights.positiveInside_bounds N (by norm_num [N]) (rowCount m c)
      (inside_rowCount_succ_le m t c hs) (globalCounts c) (rowCounts m c) (row_le_global m c)
      ((L:ℝ)*kappa/2) L (by norm_num [L,kappa]) (by norm_num [L])
      referenceWeight_le weight_ratio_le x

theorem delta_drift_le (m : Message) (t : Spec.Domain) (c : hashSpec.QueryCache)
    (η : ℝ) (hη : 0 ≤ η)
    (hscore : securityWeights.score (rowCounts m c) ≤
      (rowCount m c : ℝ)*securityWeights.mean+η*kappa*N) :
    securityWeights.expect (delta (queryPhase m t c) m c) ≤ securityWeights.mean+η*kappa := by
  cases hs : queryPhase m t c with
  | idle =>
    have hz : delta Phase.idle m c = fun _ => 0 := by
      funext x
      exact sub_self _
    rw [hz,expect_const]
    have hm : 0 ≤ securityWeights.mean := by
      exact Finset.sum_nonneg (fun i _ => mul_nonneg (securityWeights.p_pos i).le
        (securityWeights.g_nonneg i))
    exact add_nonneg hm (mul_nonneg hη (by norm_num [kappa]))
  | outside =>
    exact securityWeights.drift_outside_le N (by norm_num [N]) (rowCount m c)
      (rowCount_le m c) (globalCounts c) (rowCounts m c) η kappa hscore
  | inside =>
    exact securityWeights.drift_inside_le N (by norm_num [N]) (rowCount m c)
      (rowCount_le m c) (globalCounts c) (rowCounts m c) η kappa hscore

theorem drift_eq (m : Message) (t : Spec.Domain) (c : hashSpec.QueryCache) :
    drift m t c = securityWeights.expect (delta (queryPhase m t c) m c) :=
  primitive_delta_law m t c id

theorem actual_drift_le (m : Message) (t : Spec.Domain) (c : hashSpec.QueryCache)
    (η : ℝ) (hη : 0 ≤ η)
    (hscore : securityWeights.score (rowCounts m c) ≤
      (rowCount m c : ℝ)*securityWeights.mean+η*kappa*N) :
    drift m t c ≤ securityWeights.mean+η*kappa := by
  rw [drift_eq]
  exact delta_drift_le m t c η hη hscore

theorem gain_mean_le (m : Message) (t : Spec.Domain) (c : hashSpec.QueryCache)
    (η : ℝ) (hη : 0 ≤ η)
    (hscore : securityWeights.score (rowCounts m c) ≤
      (rowCount m c : ℝ)*securityWeights.mean+η*kappa*N) :
    securityWeights.expect (gain (queryPhase m t c) m c) ≤
      securityWeights.mean+η*kappa+1/N := by
  have h := delta_drift_le m t c η hη hscore
  simp only [show delta (queryPhase m t c) m c =
      (fun x => gain (queryPhase m t c) m c x-shift (queryPhase m t c) c) from
    funext (delta_gain_shift _ _ _),expect_sub,expect_const] at h
  linarith [shift_le (queryPhase m t c) c]

theorem centered_delta (m : Message) (t : Spec.Domain) (c : hashSpec.QueryCache)
    (x : Option (Fin M)) :
    delta (queryPhase m t c) m c x-drift m t c =
      gain (queryPhase m t c) m c x-securityWeights.expect (gain (queryPhase m t c) m c) := by
  rw [drift_eq]
  simp only [show delta (queryPhase m t c) m c =
      (fun x => gain (queryPhase m t c) m c x-shift (queryPhase m t c) c) from
    funext (delta_gain_shift _ _ _)]
  exact securityWeights.center_predictable_shift _ _ x

theorem centered_delta_abs_le (m : Message) (t : Spec.Domain) (c : hashSpec.QueryCache)
    (x : Option (Fin M)) : |delta (queryPhase m t c) m c x-drift m t c| ≤ jumpBound := by
  rw [centered_delta]
  exact securityWeights.centered_abs_le _ _ (gain_bounds m t c) x

theorem actual_variance_le (m : Message) (t : Spec.Domain) (c : hashSpec.QueryCache)
    (η : ℝ) (hη : 0 ≤ η)
    (hscore : securityWeights.score (rowCounts m c) ≤
      (rowCount m c : ℝ)*securityWeights.mean+η*kappa*N) :
    realEval ((oracleImpl t).run c)
      (fun out => (hazard m out.2-hazard m c-drift m t c)^2) ≤
    jumpBound*(securityWeights.mean+η*kappa+1/N) := by
  rw [primitive_delta_law m t c (fun z => (z-drift m t c)^2)]
  simp only [centered_delta]
  exact (securityWeights.centered_variance_le _ _ (gain_bounds m t c)).trans
    (mul_le_mul_of_nonneg_left (gain_mean_le m t c η hη hscore)
      (by norm_num [jumpBound,L,kappa,N]))

theorem actual_centered_abs_le (m : Message) (t : Spec.Domain) (c : hashSpec.QueryCache)
    (out : Spec.Range t × hashSpec.QueryCache)
    (hout : out ∈ support ((oracleImpl t).run c)) :
    |hazard m out.2-hazard m c-drift m t c| ≤ jumpBound := by
  obtain ⟨x,hx⟩ := primitive_delta_support m t c out hout
  rw [hx]
  exact centered_delta_abs_le m t c x

#print axioms actual_drift_le
#print axioms gain_bounds
#print axioms actual_variance_le
#print axioms centered_delta_abs_le
#print axioms actual_centered_abs_le
end OptimalOTS.WeightedConstruction.WideHazard
