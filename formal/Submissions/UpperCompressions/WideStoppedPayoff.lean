import Submissions.UpperCompressions.WidePreSign
import Submissions.UpperCompressions.WeightedHazardPair
import Submissions.UpperCompressions.WeightedBudgetClosure

/-! Small-budget stopped payoff on the actual protected shared oracle.
Only a fresh initial index domain and the actual program budget are assumed. -/
noncomputable section
namespace OptimalOTS.WeightedConstruction.WideStoppedPayoff
open OracleSpec OracleComp
open WeightedReference WeightedConstants WeightedBudgetClosure
open WeightedSchedule WideDomains WeightedCacheCounts WeightedRow.Weights
open WeightedRealExecution
open scoped Classical
set_option maxHeartbeats 1000000

def queryCount (c : hashSpec.QueryCache) : ℕ := (seen indexDomain c).card
def counts (c : hashSpec.QueryCache) : Fin M → ℕ := classCounts indexDomain c decode
def score (c : hashSpec.QueryCache) : ℝ := securityWeights.score (counts c)
def pairs (c : hashSpec.QueryCache) : ℝ := securityWeights.pairScore (counts c)

theorem moments {α : Type} (oa : OracleComp Spec α) (B : ℕ) (hB : CostAtMost oa B)
    (c : hashSpec.QueryCache) (hf : ∀ q : Query,q.1=342 → c q=none) :
    let run := (simulateQ oracleImpl oa).run c
    realEval run (fun out => score out.2-mean*(queryCount out.2:ℝ))=0 ∧
    realEval run (fun out => pairs out.2-(queryCount out.2:ℝ)*score out.2+
      mean*(queryCount out.2:ℝ)*((queryCount out.2:ℝ)+1)/2)=0 ∧
    realEval run (fun out => (score out.2-mean*(queryCount out.2:ℝ))^2) ≤
      (B:ℝ)*((L:ℝ)*kappa/2)*mean := by
  obtain ⟨hq,hk⟩ := WidePreSign.index_initial c hf
  exact WeightedProtectedCache.stopped_moments securityWeights indexDomain decode decoder_law
    ((L:ℝ)*kappa/2) (by norm_num [L,kappa]) referenceWeight_le oa B hB c hq hk

theorem realEval_congr_support {α : Type} (oa : ProbComp α) (f g : α → ℝ)
    (h : ∀ a ∈ support oa,f a=g a) : realEval oa f=realEval oa g :=
  le_antisymm (realEval_mono_of_support oa f g (fun a ha => (h a ha).le))
    (realEval_mono_of_support oa g f (fun a ha => (h a ha).symm.le))

theorem small_payoff_actual {α : Type} (oa : OracleComp Spec α) (B : ℕ)
    (hB : CostAtMost oa B) (hBN : (B:ℝ) ≤ (2:ℝ)^86/10)
    (c : hashSpec.QueryCache) (hf : ∀ q : Query,q.1=342 → c q=none) :
    realEval ((simulateQ oracleImpl oa).run c) (fun out =>
      C*(score out.2+2*pairs out.2/(2:ℝ)^86)+postRate*((B:ℝ)-(queryCount out.2:ℝ)))+
        kappa*(B:ℝ)/1000 ≤ (243337:ℝ)/245000*kappa*(B:ℝ) := by
  let run := (simulateQ oracleImpl oa).run c
  let τ : α × hashSpec.QueryCache → ℝ := fun out => min (queryCount out.2:ℝ) (B:ℝ)
  have hq0 := (WidePreSign.index_initial c hf).1
  have hcap (out) (ho : out ∈ support run) : queryCount out.2 ≤ B := by
    have h := WeightedProtectedCache.count_bound indexDomain oa B hB c out ho
    rw [hq0,zero_add] at h
    exact h.trans (min_le_right _ _)
  have hτ (out) (ho : out ∈ support run) : τ out=(queryCount out.2:ℝ) := by
    exact min_eq_left (by exact_mod_cast hcap out ho)
  obtain ⟨hm1,hm2,hmSq⟩ := moments oa B hB c hf
  have hm1' : realEval run (fun out => score out.2-mean*τ out)=0 := by
    rw [realEval_congr_support run _ _ (fun out ho => by rw [hτ out ho])]
    exact hm1
  have hm2' : realEval run (fun out => pairs out.2-τ out*score out.2+mean*τ out*(τ out+1)/2)=0 := by
    rw [realEval_congr_support run _ _ (fun out ho => by rw [hτ out ho])]
    exact hm2
  have hmSq' : realEval run (fun out => (score out.2-mean*τ out)^2) ≤
      (B:ℝ)*((L:ℝ)*kappa/2)*mean := by
    rw [realEval_congr_support run _ _ (fun out ho => by rw [hτ out ho])]
    exact hmSq
  have h := WeightedBudgetClosure.small_payoff (realEval run) (realEval_mono run)
    (realEval_const run 1) τ (fun out => score out.2) (fun out => pairs out.2) (B:ℝ)
    (Nat.cast_nonneg B) hBN
    (fun out => le_min (Nat.cast_nonneg _) (Nat.cast_nonneg B))
    (fun out => min_le_right _ _) hm1' hm2' hmSq'
  rw [realEval_congr_support run _ _ (fun out ho => by rw [hτ out ho])] at h
  exact h

#print axioms moments
#print axioms small_payoff_actual
end OptimalOTS.WeightedConstruction.WideStoppedPayoff
