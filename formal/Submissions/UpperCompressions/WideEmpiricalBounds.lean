import Submissions.UpperCompressions.WideEmpiricalGood
import Submissions.UpperCompressions.WideReplayBounds

/-! Pointwise consequences of the single concrete empirical Good event. -/
noncomputable section
namespace OptimalOTS.WeightedConstruction.WideEmpirical
open WeightedReference WeightedConstants WeightedSchedule WideDomains WideConcentration
open WeightedCacheCounts WeightedRow.Weights
open scoped Classical
set_option maxHeartbeats 1000000

theorem good_global (c : hashSpec.QueryCache) (hc : Good c) :
    securityWeights.score (classCounts indexDomain c decode) ≤
      mean*(seen indexDomain c).card+(kappa/100)*max ((seen indexDomain c).card:ℝ) ((2:ℝ)^86/10) := by
  have h := hc (.inl ())
  change ¬((kappa/100)*max ((seen indexDomain c).card:ℝ) ((2:ℝ)^86/10) ≤
    securityWeights.M1 (seen indexDomain c).card (classCounts indexDomain c decode)) at h
  have hh := lt_of_not_ge h
  change securityWeights.score _-mean*(seen indexDomain c).card < _ at hh
  linarith

theorem good_row_score (c : hashSpec.QueryCache) (hc : Good c) (m : Message) :
    securityWeights.score (classCounts (rowDomain m) c decode) ≤
      mean*(seen (rowDomain m) c).card+kappa*(2:ℝ)^86/100 := by
  have h := hc (.inr (m,⟨72,by decide⟩))
  change ¬scoreBad m c at h
  have hh := lt_of_not_ge h
  change securityWeights.score _-mean*(seen (rowDomain m) c).card < _ at hh
  linarith

theorem good_row_excess (c : hashSpec.QueryCache) (hc : Good c) (m : Message) :
    excessWeights.score (classCounts (rowDomain m) c decode) ≤
      (∑ i : Fin M,referenceWeight i*excess i)*(seen (rowDomain m) c).card+kappa*(2:ℝ)^86/100 := by
  have h := hc (.inr (m,⟨73,by decide⟩))
  change ¬excessBad m c at h
  have hh := lt_of_not_ge h
  unfold excessBad WeightedRow.Weights.M1 at hh
  rw [excessWeights_mean] at hh
  linarith

theorem good_prefix (c : hashSpec.QueryCache) (hc : Good c) (m : Message) (j : Fin 72) :
    (∑ i ∈ prefixClasses j,classProbability i)*(seen (rowDomain m) c).card -
      ∑ i ∈ prefixClasses j,(classCounts (rowDomain m) c decode i:ℝ) ≤
        (2:ℝ)^86/(100*(2:ℝ)^20) := by
  have h := hc (.inr (m,⟨j.val,by have := j.isLt; omega⟩))
  have he : event (.inr (m,⟨j.val,by have := j.isLt; omega⟩)) c = prefixBad m j c := by
    dsimp only [event]
    rw [dif_pos j.isLt]
  rw [he] at h
  have hh := (lt_of_not_ge h).le
  change -(securityWeights.prefixWeights (prefixClasses j)).M1 _ _ ≤ _ at hh
  rw [prefix_deficit] at hh
  exact hh

/-- On Good, the full-completion expected excess has a common class-independent
ceiling. The failure-table allowance remains explicit and joint. -/
theorem good_excess_payoff (c : hashSpec.QueryCache) (hc : Good c) (m : Message) :
    (1-((seen (rowDomain m) c).card:ℝ)/(2:ℝ)^86)*(∑ i : Fin M,referenceWeight i*excess i)+
      excessWeights.score (classCounts (rowDomain m) c decode)/(2:ℝ)^86 ≤
        kappa*(2/5)+kappa/100 := by
  have hs := good_row_excess c hc m
  have hn : (0:ℝ)<2^86 := by positivity
  have hd := (div_le_div_iff_of_pos_right hn).mpr hs
  have hm := excess_mean_le
  have he : (1-((seen (rowDomain m) c).card:ℝ)/(2:ℝ)^86)*(∑ i : Fin M,referenceWeight i*excess i)+
      ((∑ i : Fin M,referenceWeight i*excess i)*(seen (rowDomain m) c).card+kappa*(2:ℝ)^86/100)/(2:ℝ)^86 =
      (∑ i : Fin M,referenceWeight i*excess i)+kappa/100 := by ring
  linarith

#print axioms good_global
#print axioms good_row_score
#print axioms good_prefix
#print axioms good_excess_payoff
end OptimalOTS.WeightedConstruction.WideEmpirical
