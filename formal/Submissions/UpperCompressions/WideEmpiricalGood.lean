import Submissions.UpperCompressions.WideConcentration
import Submissions.UpperCompressions.FirstHitUnion

/-! A single actual pre-sign Good event, simultaneously over all messages and
72 tier prefixes, row scores, row excess scores, and the global score. -/
noncomputable section
namespace OptimalOTS.WeightedConstruction.WideEmpirical
open OracleSpec OracleComp OracleComp.EvalDist
open WeightedReference WeightedConstants WeightedSchedule WideDomains WideConcentration
open WeightedCacheCounts WeightedRow.Weights WeightedOracleExecution WeightedFirstHit
open scoped Classical ENNReal
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
attribute [local irreducible] Finset.univ Finset.filter

def prefixClasses (j : Fin 72) : Finset (Fin M) := Finset.univ.filter (fun i => tier i ≤ j.val)
def prefixWeight (j : Fin 72) : WeightedRow.Weights (Fin M) := securityWeights.prefixWeights (prefixClasses j)

def globalBad (c : hashSpec.QueryCache) : Prop :=
  (kappa/100)*max ((seen indexDomain c).card:ℝ) ((2:ℝ)^86/10) ≤
    securityWeights.M1 (seen indexDomain c).card (classCounts indexDomain c decode)
def prefixBad (m : Message) (j : Fin 72) (c : hashSpec.QueryCache) : Prop :=
  (2:ℝ)^86/(100*(2:ℝ)^20) ≤
    -(prefixWeight j).M1 (seen (rowDomain m) c).card (classCounts (rowDomain m) c decode)
def scoreBad (m : Message) (c : hashSpec.QueryCache) : Prop :=
  kappa*(2:ℝ)^86/100 ≤ securityWeights.M1
    (seen (rowDomain m) c).card (classCounts (rowDomain m) c decode)
def excessBad (m : Message) (c : hashSpec.QueryCache) : Prop :=
  kappa*(2:ℝ)^86/100 ≤ excessWeights.M1
    (seen (rowDomain m) c).card (classCounts (rowDomain m) c decode)

theorem prefix_bound {α : Type} (m : Message) (j : Fin 72) (oa : OracleComp Spec α)
    (c : hashSpec.QueryCache) (hf : ∀ q : Query,q.1=342 → c q=none) :
    crossing oa c (prefixBad m j) ≤ ENNReal.ofReal (Real.exp (-(2^30:ℝ))) := by
  obtain ⟨hq,hk⟩ := row_initial m c hf
  have h := row_withScore_bound (fun i => if i ∈ prefixClasses j then 1 else 0)
    (fun i => by split_ifs <;> norm_num) 1 (by norm_num)
    (securityWeights.prefix_weight_bound (prefixClasses j)) true m oa c hf
  simp only [WeightedActualScore.signedM1,ite_true,one_mul] at h
  exact h

theorem score_bound {α : Type} (m : Message) (oa : OracleComp Spec α)
    (c : hashSpec.QueryCache) (hf : ∀ q : Query,q.1=342 → c q=none) :
    crossing oa c (scoreBad m) ≤ ENNReal.ofReal (Real.exp (-(2^30:ℝ))) := by
  obtain ⟨hq,hk⟩ := row_initial m c hf
  have hg (i : Fin M) : securityWeights.g i ≤ (L:ℝ)*kappa := by
    have h := referenceWeight_le i
    change referenceWeight i ≤ _
    have hn : 0 ≤ (L:ℝ)*kappa := by norm_num [L,kappa]
    linarith
  have h : crossing oa c (fun d => ((L:ℝ)*kappa)*(2:ℝ)^86/(100*(2:ℝ)^20) ≤
      WeightedActualScore.signedM1 securityWeights
        (fun d => (seen (rowDomain m) d).card)
        (fun d => classCounts (rowDomain m) d decode) false d) ≤
        ENNReal.ofReal (Real.exp (-(2^30:ℝ))) :=
    WeightedProtectedCache.row_score securityWeights (rowDomain m) (row_card m).le
      decode decoder_law false ((L:ℝ)*kappa) (by norm_num [L,kappa]) hg oa c hq hk
  have he : ((L:ℝ)*kappa)*(2:ℝ)^86/(100*(2:ℝ)^20)=kappa*(2:ℝ)^86/100 := by norm_num [L,kappa]
  simp only [WeightedActualScore.signedM1,Bool.false_eq_true,ite_false,he] at h
  exact h

abbrev BadIndex := Unit ⊕ (Message × Fin 74)
def event : BadIndex → hashSpec.QueryCache → Prop
  | .inl _ => globalBad
  | .inr (m,j) => if h : j.val < 72 then prefixBad m ⟨j.val,h⟩
      else if j.val=72 then scoreBad m else excessBad m

theorem event_bound {α : Type} (oa : OracleComp Spec α) (c : hashSpec.QueryCache)
    (hf : ∀ q : Query,q.1=342 → c q=none) (i : BadIndex) :
    crossing oa c (event i) ≤ ENNReal.ofReal (Real.exp (-(2^30:ℝ))) := by
  cases i with
  | inl u =>
    apply (global_bound oa c hf).trans
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    norm_num
  | inr p =>
    obtain ⟨m,j⟩ := p
    dsimp only [event]
    split_ifs with h h'
    · exact prefix_bound m ⟨j.val,h⟩ oa c hf
    · exact score_bound m oa c hf
    · exact row_excess_bound m oa c hf

def Good (c : hashSpec.QueryCache) : Prop := ∀ i : BadIndex,¬ event i c

theorem all_crossings {α : Type} (oa : OracleComp Spec α) (c : hashSpec.QueryCache)
    (hf : ∀ q : Query,q.1=342 → c q=none) :
    crossing oa c (fun d => ∃ i : BadIndex,event i d) ≤ ENNReal.ofReal (((2:ℝ)^512)⁻¹) := by
  have hc : Fintype.card BadIndex ≤ 74*2^256+1 := by
    norm_num [BadIndex,Message,msgBits,Fintype.card_sum,Fintype.card_prod,Fintype.card_bitVec]
  exact stopped_mixed_union oracleImpl (fun i _ c => event i c) oa 0 c hc (event_bound oa c hf)

theorem terminal_bad {α : Type} (oa : OracleComp Spec α) (c : hashSpec.QueryCache)
    (hf : ∀ q : Query,q.1=342 → c q=none) :
    Pr[fun out => ¬Good out.2 | (simulateQ oracleImpl oa).run c] ≤
      ENNReal.ofReal (((2:ℝ)^512)⁻¹) := by
  have hgood (d : hashSpec.QueryCache) : (¬Good d) = (∃ i : BadIndex,event i d) := by
    simp only [Good,not_forall,not_not]
  simp only [hgood]
  apply (terminal_bad_le_firstHit oracleImpl (fun d => ∃ i : BadIndex,event i d) oa 0 c).trans
  have h := all_crossings oa c hf
  simpa only [crossing,prob_stopped_hit_eq_firstHitRun] using h

#print axioms all_crossings
#print axioms terminal_bad
end OptimalOTS.WeightedConstruction.WideEmpirical
