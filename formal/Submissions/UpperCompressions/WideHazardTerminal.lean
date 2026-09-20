import Submissions.UpperCompressions.WideHazardFreedman
import Submissions.UpperCompressions.FirstHitTerminalUnion

/-! Uniform actual pre-sign hazard control for every message, with one common
empirical exception and one union over message rows. -/
noncomputable section
open OracleSpec OracleComp OracleComp.EvalDist
open scoped Classical BigOperators ENNReal
namespace OptimalOTS.WeightedConstruction.WideHazard
open WeightedSchedule WideDomains WeightedReference WeightedConstants WeightedOracleExecution
attribute [local irreducible] Finset.univ Finset.filter

theorem common_kill_bound {β : Type} (oa : OracleComp Spec β) (c : hashSpec.QueryCache)
    (hf : ∀ q : Query,q.1=342 → c q=none) :
    Pr[=true | firstHitRun oracleImpl kill (fun _ _ => False) oa 0 c] ≤
      ENNReal.ofReal (((2:ℝ)^512)⁻¹) := by
  have h := WideEmpirical.all_crossings oa c hf
  unfold WideConcentration.crossing at h
  rw [prob_stopped_hit_eq_firstHitRun] at h
  have he : kill = fun (_ : ℕ) d => ∃ i : WideEmpirical.BadIndex,WideEmpirical.event i d := by
    funext n d
    simp only [kill,WideEmpirical.Good,not_forall,not_not]
  rw [he]
  exact h

theorem terminal_hits_bound {β : Type} (B : ℕ) (hB : N/10≤(B:ℝ))
    (oa : OracleComp Spec β) (c : hashSpec.QueryCache)
    (hf : ∀ q : Query,q.1=342 → c q=none) :
    Pr[fun out => ∃ m : Message,hit B m 0 out.2 | (simulateQ oracleImpl oa).run c] ≤
      ENNReal.ofReal (((2:ℝ)^1792)⁻¹)+ENNReal.ofReal (((2:ℝ)^512)⁻¹) := by
  have h := terminal_union_le_stopped oracleImpl (fun m : Message => hit B m 0)
    (fun d => ¬WideEmpirical.Good d) oa 0 c
  have hm (m : Message) :
      Pr[=true | firstHitRun oracleImpl (hit B m) kill oa 0 c] ≤
        ENNReal.ofReal (Real.exp (-(2048:ℝ))) := by
    have h := stopped_large_bound B hB m oa c hf
    rw [prob_stopped_hit_eq_firstHitRun] at h
    exact h
  have hsum : (∑ m : Message,Pr[=true | firstHitRun oracleImpl (hit B m) kill oa 0 c]) ≤
      ENNReal.ofReal (((2:ℝ)^1792)⁻¹) := by
    calc
      _ ≤ ∑ _m : Message,ENNReal.ofReal (Real.exp (-(2048:ℝ))) :=
        Finset.sum_le_sum (fun m _ => hm m)
      _ = (Fintype.card Message:ℝ≥0∞)*ENNReal.ofReal (Real.exp (-(2048:ℝ))) := by
        rw [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
      _ = ENNReal.ofReal ((2:ℝ)^256*Real.exp (-(2048:ℝ))) := by
        rw [ENNReal.ofReal_mul (by positivity)]
        congr 1
        norm_num [Message,msgBits,Fintype.card_bitVec]
      _ ≤ _ := ENNReal.ofReal_le_ofReal WeightedHazardConstants.message_union_margin
  exact h.trans (add_le_add hsum (common_kill_bound oa c hf))

theorem terminal_hits_or_bad_bound {β : Type} (B : ℕ) (hB : N/10≤(B:ℝ))
    (oa : OracleComp Spec β) (c : hashSpec.QueryCache)
    (hf : ∀ q : Query,q.1=342 → c q=none) :
    Pr[fun out => (∃ m : Message,hit B m 0 out.2) ∨ ¬WideEmpirical.Good out.2 | (simulateQ oracleImpl oa).run c] ≤
      ENNReal.ofReal (((2:ℝ)^1792)⁻¹)+ENNReal.ofReal (((2:ℝ)^512)⁻¹) := by
  have h := terminal_union_or_kill_le_stopped oracleImpl (fun m : Message => hit B m 0)
    (fun d => ¬WideEmpirical.Good d) oa 0 c
  have hm (m : Message) :
      Pr[=true | firstHitRun oracleImpl (hit B m) kill oa 0 c] ≤
        ENNReal.ofReal (Real.exp (-(2048:ℝ))) := by
    have h := stopped_large_bound B hB m oa c hf
    rw [prob_stopped_hit_eq_firstHitRun] at h
    exact h
  have hsum : (∑ m : Message,Pr[=true | firstHitRun oracleImpl (hit B m) kill oa 0 c]) ≤
      ENNReal.ofReal (((2:ℝ)^1792)⁻¹) := by
    calc
      _ ≤ ∑ _m : Message,ENNReal.ofReal (Real.exp (-(2048:ℝ))) :=
        Finset.sum_le_sum (fun m _ => hm m)
      _ = (Fintype.card Message:ℝ≥0∞)*ENNReal.ofReal (Real.exp (-(2048:ℝ))) := by
        rw [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
      _ = ENNReal.ofReal ((2:ℝ)^256*Real.exp (-(2048:ℝ))) := by
        rw [ENNReal.ofReal_mul (by positivity)]
        congr 1
        norm_num [Message,msgBits,Fintype.card_bitVec]
      _ ≤ _ := ENNReal.ofReal_le_ofReal WeightedHazardConstants.message_union_margin
  exact h.trans (add_le_add hsum (common_kill_bound oa c hf))

def LargeBad (B : ℕ) (c : hashSpec.QueryCache) : Prop :=
  ∃ m : Message,alpha*(globalCount c:ℝ)+(7/100)*kappa*(B:ℝ)≤hazard m c

theorem actual_large_hazard_bound {β : Type} (B : ℕ) (hB : N/10≤(B:ℝ))
    (oa : OracleComp Spec β) (hbudget : CostAtMost oa B) (c : hashSpec.QueryCache)
    (hf : ∀ q : Query,q.1=342 → c q=none) :
    Pr[fun out => LargeBad B out.2 | (simulateQ oracleImpl oa).run c] ≤
      ENNReal.ofReal (((2:ℝ)^1792)⁻¹)+ENNReal.ofReal (((2:ℝ)^512)⁻¹) := by
  apply (probEvent_mono (fun out hout hbad => ?_)).trans
    (terminal_hits_bound B hB oa c hf)
  obtain ⟨m,hm⟩ := hbad
  have hcount := WeightedProtectedCache.count_bound indexDomain oa B hbudget c out hout
  have hzero : (WeightedCacheCounts.seen indexDomain c).card=0 :=
    (WidePreSign.index_initial c hf).1
  have hn : globalCount out.2≤B := by
    exact (hcount.trans (min_le_right _ _)).trans_eq (by rw [hzero,zero_add])
  refine ⟨m,?_,?_⟩
  · exact Nat.cast_le.mpr hn
  · change (7/100)*kappa*(B:ℝ)≤hazard m out.2-alpha*(globalCount out.2:ℝ)
    linarith

theorem actual_large_good_hazard_bound {β : Type} (B : ℕ) (hB : N/10≤(B:ℝ))
    (oa : OracleComp Spec β) (hbudget : CostAtMost oa B) (c : hashSpec.QueryCache)
    (hf : ∀ q : Query,q.1=342 → c q=none) :
    Pr[fun out => ¬WideEmpirical.Good out.2 ∨ LargeBad B out.2 | (simulateQ oracleImpl oa).run c] ≤
      ENNReal.ofReal (((2:ℝ)^1792)⁻¹)+ENNReal.ofReal (((2:ℝ)^512)⁻¹) := by
  apply (probEvent_mono (fun out hout hbad => ?_)).trans
    (terminal_hits_or_bad_bound B hB oa c hf)
  rcases hbad with hbad | hbad
  · exact Or.inr hbad
  · obtain ⟨m,hm⟩ := hbad
    have hcount := WeightedProtectedCache.count_bound indexDomain oa B hbudget c out hout
    have hzero : (WeightedCacheCounts.seen indexDomain c).card=0 :=
      (WidePreSign.index_initial c hf).1
    have hn : globalCount out.2≤B :=
      (hcount.trans (min_le_right _ _)).trans_eq (by rw [hzero,zero_add])
    refine Or.inl ⟨m,?_,?_⟩
    · exact Nat.cast_le.mpr hn
    · change (7/100)*kappa*(B:ℝ)≤hazard m out.2-alpha*(globalCount out.2:ℝ)
      linarith

#print axioms terminal_hits_or_bad_bound
#print axioms actual_large_good_hazard_bound
#print axioms terminal_hits_bound
#print axioms actual_large_hazard_bound
end OptimalOTS.WeightedConstruction.WideHazard
