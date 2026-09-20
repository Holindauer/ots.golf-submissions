import Submissions.UpperCompressions.WidePreSign
import Submissions.UpperCompressions.ProtectedConcentration
import Submissions.UpperCompressions.ReweightedScores
import Submissions.UpperCompressions.WideCountRelations

/-! Concrete time-uniform pre-sign score bounds for every message row.
The underlying execution is the contract's actual shared oracle throughout. -/
noncomputable section
open OracleSpec OracleComp
open scoped Classical
namespace WeightedProtectedCache
variable {ι α : Type} [Fintype ι] [DecidableEq ι]
theorem row_reweighted (w : WeightedRow.Weights ι)
    (A : Finset OptimalOTS.Query) (hcard : A.card ≤ 2^86)
    (decode : BitVec OptimalOTS.hashBits → Option ι)
    (hfiber : ∀ x, ((Finset.univ.filter (fun b => decode b=x)).card:ℝ) /
      Fintype.card (BitVec OptimalOTS.hashBits) = w.classMass x)
    (g : ι → ℝ) (hg0 : ∀ i,0 ≤ g i)
    (lower : Bool) (G : ℝ) (hG : 0 < G) (hg : ∀ i,g i ≤ G)
    (oa : OracleComp OptimalOTS.Spec α) (cache : OptimalOTS.hashSpec.QueryCache)
    (hq0 : (WeightedCacheCounts.seen A cache).card=0)
    (hk0 : WeightedCacheCounts.classCounts A cache decode=(fun _ => 0)) :
    let hit := fun (_ : ℕ) (c : OptimalOTS.hashSpec.QueryCache) =>
      G*(2^86:ℝ)/(100*(2^20:ℝ)) ≤ WeightedActualScore.signedM1 (w.withScore g hg0)
        (fun c => (WeightedCacheCounts.seen A c).card)
        (fun c => WeightedCacheCounts.classCounts A c decode) lower c
    let kill := fun (_ : ℕ) (_ : OptimalOTS.hashSpec.QueryCache) => False
    Pr[fun out => out.2.status = .hit |
      (simulateQ (WeightedOracleExecution.stoppedImpl OptimalOTS.oracleImpl hit kill) oa).run
        (WeightedFirstHit.classify hit kill 0 cache)] ≤
      ENNReal.ofReal (Real.exp (-(2^30:ℝ))) := by
  apply row_score (w.withScore g hg0) A hcard decode _ lower G hG hg oa cache hq0 hk0
  intro x
  exact (hfiber x).trans (WeightedRow.Weights.withScore_classMass w g hg0 x).symm
end WeightedProtectedCache
namespace OptimalOTS.WeightedConstruction.WideConcentration
open OracleSpec OracleComp OracleComp.EvalDist
open WeightedReference WeightedConstants WeightedSchedule WideDomains
open WeightedCacheCounts WeightedRow.Weights WeightedOracleExecution WeightedFirstHit
open scoped Classical ENNReal
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
attribute [local irreducible] Finset.univ Finset.filter

def crossing {α : Type} (oa : OracleComp Spec α) (c : hashSpec.QueryCache)
    (bad : hashSpec.QueryCache → Prop) : ℝ≥0∞ :=
  Pr[fun out => out.2.status = .hit |
    (simulateQ (stoppedImpl oracleImpl (fun _ c => bad c) (fun _ _ => False)) oa).run
      (classify (fun _ c => bad c) (fun _ _ => False) 0 c)]

theorem row_initial (m : Message) (c : hashSpec.QueryCache)
    (hf : ∀ q : Query,q.1=342 → c q=none) :
    (seen (rowDomain m) c).card=0 ∧ classCounts (rowDomain m) c decode=(fun _ => 0) := by
  obtain ⟨hq,hk⟩ := WidePreSign.index_initial c hf
  constructor
  · have h := Finset.card_le_card (seen_row_subset m c)
    rw [hq] at h
    exact Nat.eq_zero_of_le_zero h
  · funext i
    have h := row_class_le_global m c i
    rw [hk] at h
    exact Nat.eq_zero_of_le_zero h

theorem global_bound {α : Type} (oa : OracleComp Spec α) (c : hashSpec.QueryCache)
    (hf : ∀ q : Query,q.1=342 → c q=none) :
    crossing oa c (fun d => (kappa/100)*max ((seen indexDomain d).card:ℝ) ((2:ℝ)^86/10) ≤
      securityWeights.M1 (seen indexDomain d).card (classCounts indexDomain d decode)) ≤
        ENNReal.ofReal (Real.exp (-(2^40:ℝ))) := by
  obtain ⟨hq,hk⟩ := WidePreSign.index_initial c hf
  have hm : securityWeights.mean ≤ kappa := securityWeights_mean.trans (by norm_num [kappa])
  exact WeightedProtectedCache.global_score securityWeights indexDomain decode decoder_law kappa
    (by norm_num [kappa]) hm (fun i => by
      simpa only [securityWeights,L,Nat.cast_pow,Nat.cast_ofNat] using referenceWeight_le i) oa c hq hk

theorem row_withScore_bound {α : Type} (g : Fin M → ℝ) (hg0 : ∀ i,0 ≤ g i)
    (G : ℝ) (hG : 0 < G) (hg : ∀ i,g i ≤ G) (lower : Bool)
    (m : Message) (oa : OracleComp Spec α) (c : hashSpec.QueryCache)
    (hf : ∀ q : Query,q.1=342 → c q=none) :
    crossing oa c (fun d => G*(2:ℝ)^86/(100*(2:ℝ)^20) ≤
      WeightedActualScore.signedM1 (securityWeights.withScore g hg0)
        (fun d => (seen (rowDomain m) d).card)
        (fun d => classCounts (rowDomain m) d decode) lower d) ≤
      ENNReal.ofReal (Real.exp (-(2^30:ℝ))) := by
  obtain ⟨hq,hk⟩ := row_initial m c hf
  exact WeightedProtectedCache.row_reweighted securityWeights (rowDomain m)
    (row_card m).le decode decoder_law g hg0 lower G hG hg oa c hq hk

def excessWeights : WeightedRow.Weights (Fin M) := securityWeights.withScore
  (fun i => referenceWeight i*excess i/classProbability i) excessScore_nonneg

theorem excessWeights_mean : excessWeights.mean=(∑ i : Fin M,referenceWeight i*excess i) := by
  unfold WeightedRow.Weights.mean
  apply Finset.sum_congr rfl
  intro i hi
  change classProbability i*(referenceWeight i*excess i/classProbability i)=_
  field_simp [(classProbability_pos i).ne']

theorem row_excess_bound {α : Type} (m : Message) (oa : OracleComp Spec α)
    (c : hashSpec.QueryCache) (hf : ∀ q : Query,q.1=342 → c q=none) :
    crossing oa c (fun d => kappa*(2:ℝ)^86/100 ≤
      excessWeights.M1 (seen (rowDomain m) d).card (classCounts (rowDomain m) d decode)) ≤
      ENNReal.ofReal (Real.exp (-(2^30:ℝ))) := by
  have h := row_withScore_bound
    (fun i => referenceWeight i*excess i/classProbability i) excessScore_nonneg
    ((L:ℝ)*kappa) (by norm_num [L,kappa]) excessScore_le false m oa c hf
  have he : ((L:ℝ)*kappa)*(2:ℝ)^86/(100*(2:ℝ)^20)=kappa*(2:ℝ)^86/100 := by
    norm_num [L,kappa]
  simp only [WeightedActualScore.signedM1,Bool.false_eq_true,ite_false,he] at h
  exact h

#print axioms global_bound
#print axioms row_withScore_bound
#print axioms row_excess_bound
end OptimalOTS.WeightedConstruction.WideConcentration
