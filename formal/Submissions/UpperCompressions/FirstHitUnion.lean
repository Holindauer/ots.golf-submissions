import Submissions.UpperCompressions.OracleExecutionConcentration
import Submissions.UpperCompressions.RowConcentrationConstants
noncomputable section
open OracleSpec OracleComp OracleComp.EvalDist
open scoped Classical BigOperators ENNReal
namespace WeightedOracleExecution
open WeightedFirstHit
set_option maxHeartbeats 800000
variable {ι S α I : Type} {spec : OracleSpec ι} [spec.Inhabited] [Fintype I]

theorem firstHitRun_of_hit (impl : QueryImpl spec (StateT S ProbComp))
    (hit kill : ℕ → S → Prop) (oa : OracleComp spec α) (t : ℕ) (s : S)
    (hh : hit t s) : firstHitRun impl hit kill oa t s = pure true := by
  induction oa using OracleComp.inductionOn with
  | pure a => simp [hh]
  | query_bind q k ih => simp only [firstHitRun_query_bind, if_pos hh]

/-- Finite union of maximal events in actual execution. The differently stopped
programs are related by structural induction, so no common-law assumption or
time-prefix union factor is needed. -/
theorem firstHitRun_union_le (impl : QueryImpl spec (StateT S ProbComp))
    (hit : I → ℕ → S → Prop) (oa : OracleComp spec α) (t : ℕ) (s : S) :
    Pr[= true | firstHitRun impl (fun n s => ∃ i, hit i n s) (fun _ _ => False) oa t s] ≤
      ∑ i, Pr[= true | firstHitRun impl (hit i) (fun _ _ => False) oa t s] := by
  induction oa using OracleComp.inductionOn generalizing t s with
  | pure a =>
    by_cases hh : ∃ i, hit i t s
    · obtain ⟨i,hi⟩ := hh
      have hall : Pr[= true | firstHitRun impl (fun n s => ∃ i, hit i n s)
          (fun _ _ => False) (pure a) t s] = 1 := by simp [show ∃ i, hit i t s from ⟨i,hi⟩]
      have hone : Pr[= true | firstHitRun impl (hit i) (fun _ _ => False) (pure a) t s] = 1 := by simp [hi]
      rw [hall, ← hone]
      exact Finset.single_le_sum (s := Finset.univ)
        (f := fun j : I => Pr[= true | firstHitRun impl (hit j) (fun _ _ => False) (pure a) t s])
        (fun j _ => zero_le) (Finset.mem_univ i)
    · simp [hh]
  | query_bind q k ih =>
    by_cases hh : ∃ i, hit i t s
    · obtain ⟨i,hi⟩ := hh
      have hall : Pr[= true | firstHitRun impl (fun n s => ∃ i, hit i n s)
          (fun _ _ => False) ((liftM (spec.query q) : OracleComp spec (spec.Range q)) >>= k) t s] = 1 := by
        rw [firstHitRun_of_hit _ _ _ _ _ _ ⟨i,hi⟩]
        simp
      have hone : Pr[= true | firstHitRun impl (hit i) (fun _ _ => False)
          ((liftM (spec.query q) : OracleComp spec (spec.Range q)) >>= k) t s] = 1 := by
        rw [firstHitRun_of_hit _ _ _ _ _ _ hi]
        simp
      rw [hall, ← hone]
      exact Finset.single_le_sum (s := Finset.univ)
        (f := fun j : I => Pr[= true | firstHitRun impl (hit j) (fun _ _ => False)
          ((liftM (spec.query q) : OracleComp spec (spec.Range q)) >>= k) t s])
        (fun j _ => zero_le) (Finset.mem_univ i)
    · have hnone : ∀ i, ¬hit i t s := fun i hi => hh ⟨i,hi⟩
      rw [firstHitRun_query_bind, if_neg hh, if_false]
      simp only [firstHitRun_query_bind, hnone, if_false, probOutput_bind_eq_expectedValue]
      rw [← expectedValue_finsetSum]
      apply expectedValue_mono
      intro out
      exact ih out.1 (t+1) out.2

/-- Finite union bound stated in the stopped-flag API used by concentration. -/
theorem stopped_hit_union_le (impl : QueryImpl spec (StateT S ProbComp))
    (hit : I → ℕ → S → Prop) (oa : OracleComp spec α) (t : ℕ) (s : S) :
    Pr[fun out => out.2.status = .hit |
      (simulateQ (stoppedImpl impl (fun n s => ∃ i, hit i n s) (fun _ _ => False)) oa).run
        (classify (fun n s => ∃ i, hit i n s) (fun _ _ => False) t s)] ≤
      ∑ i, Pr[fun out => out.2.status = .hit |
        (simulateQ (stoppedImpl impl (hit i) (fun _ _ => False)) oa).run
          (classify (hit i) (fun _ _ => False) t s)] := by
  simp only [prob_stopped_hit_eq_firstHitRun]
  exact firstHitRun_union_le impl hit oa t s

theorem stopped_hit_union_uniform (impl : QueryImpl spec (StateT S ProbComp))
    (hit : I → ℕ → S → Prop) (oa : OracleComp spec α) (t : ℕ) (s : S)
    (ε : ℝ≥0∞)
    (hbound : ∀ i, Pr[fun out => out.2.status = .hit |
      (simulateQ (stoppedImpl impl (hit i) (fun _ _ => False)) oa).run
        (classify (hit i) (fun _ _ => False) t s)] ≤ ε) :
    Pr[fun out => out.2.status = .hit |
      (simulateQ (stoppedImpl impl (fun n s => ∃ i, hit i n s) (fun _ _ => False)) oa).run
        (classify (fun n s => ∃ i, hit i n s) (fun _ _ => False) t s)] ≤
      (Fintype.card I:ℝ≥0∞)*ε := by
  apply (stopped_hit_union_le impl hit oa t s).trans
  calc
    (∑ i, Pr[fun out => out.2.status = .hit |
      (simulateQ (stoppedImpl impl (hit i) (fun _ _ => False)) oa).run
        (classify (hit i) (fun _ _ => False) t s)]) ≤ ∑ _i : I, ε :=
      Finset.sum_le_sum (fun i _ => hbound i)
    _ = (Fintype.card I:ℝ≥0∞)*ε := by simp [nsmul_eq_mul]

/-- Actual mixed72 Good-event union, including all message rows and the global
boundary, once the explicit per-event crossing bounds are supplied. -/
theorem stopped_mixed_union (impl : QueryImpl spec (StateT S ProbComp))
    (hit : I → ℕ → S → Prop) (oa : OracleComp spec α) (t : ℕ) (s : S)
    (hcard : Fintype.card I ≤ 74*2^256+1)
    (hbound : ∀ i, Pr[fun out => out.2.status = .hit |
      (simulateQ (stoppedImpl impl (hit i) (fun _ _ => False)) oa).run
        (classify (hit i) (fun _ _ => False) t s)] ≤
          ENNReal.ofReal (Real.exp (-(2^30:ℝ)))) :
    Pr[fun out => out.2.status = .hit |
      (simulateQ (stoppedImpl impl (fun n s => ∃ i, hit i n s) (fun _ _ => False)) oa).run
        (classify (fun n s => ∃ i, hit i n s) (fun _ _ => False) t s)] ≤
      ENNReal.ofReal (((2:ℝ)^512)⁻¹) := by
  have hn : (Fintype.card I:ℝ) ≤ 74*(2^256:ℝ)+1 := by exact_mod_cast hcard
  calc
    _ ≤ (Fintype.card I:ℝ≥0∞)*ENNReal.ofReal (Real.exp (-(2^30:ℝ))) :=
      stopped_hit_union_uniform impl hit oa t s _ hbound
    _ = ENNReal.ofReal ((Fintype.card I:ℝ)*Real.exp (-(2^30:ℝ))) := by
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal ((74*(2^256:ℝ)+1)*Real.exp (-(2^30:ℝ))) :=
      ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hn (Real.exp_nonneg _))
    _ ≤ ENNReal.ofReal (((2:ℝ)^512)⁻¹) :=
      ENNReal.ofReal_le_ofReal WeightedEmpirical.mixed_row_union_margin

/-- A terminal violation in the actual unmodified execution is included in a
first hit of the same state predicate. No transcript or stopping coupling is assumed. -/
theorem terminal_bad_le_firstHit (impl : QueryImpl spec (StateT S ProbComp))
    (bad : S → Prop) (oa : OracleComp spec α) (t : ℕ) (s : S) :
    Pr[fun out => bad out.2 | (simulateQ impl oa).run s] ≤
      Pr[= true | firstHitRun impl (fun _ s => bad s) (fun _ _ => False) oa t s] := by
  induction oa using OracleComp.inductionOn generalizing t s with
  | pure a =>
    by_cases hh : bad s <;> simp [hh]
  | query_bind q k ih =>
    by_cases hh : bad s
    · rw [firstHitRun_of_hit _ _ _ _ _ _ hh]
      simpa using (probEvent_le_one (mx := (simulateQ impl
        ((liftM (spec.query q) : OracleComp spec (spec.Range q)) >>= k)).run s)
        (p := fun out => bad out.2))
    · rw [firstHitRun_query_bind, if_neg hh, if_false]
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
        probEvent_bind_eq_expectedValue, probOutput_bind_eq_expectedValue]
      apply expectedValue_mono
      intro out
      exact ih out.1 (t+1) out.2

#print axioms stopped_hit_union_uniform
#print axioms stopped_mixed_union
#print axioms terminal_bad_le_firstHit

#print axioms firstHitRun_union_le
#print axioms stopped_hit_union_le
end WeightedOracleExecution
