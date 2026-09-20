import Submissions.UpperCompressions.WideSecurityData
import Submissions.UpperCompressions.WeightedUniform
import Submissions.UpperCompressions.WeightedMoments

/-! The actual256-bit decoder law, including the rejection atom. -/
noncomputable section
namespace OptimalOTS.WeightedConstruction.WeightedSchedule
open scoped Classical
open WeightedReference WeightedRow.Weights
attribute [local irreducible] Finset.univ Finset.filter

theorem card_decode_none :
    (Finset.univ.filter fun b : BitVec 256 => decode b=none).card =
      2^256-A*2^127 := by
  have h := WeightedSampling.Availability.card_option_none decode (A*2^127) accepted_decode_count
  have hs : (Finset.univ.filter fun b : BitVec 256 => decode b=none) =
      Finset.univ.filter fun b : BitVec 256 => (decode b).isNone := by
    apply Finset.filter_congr
    intro b hb
    cases decode b <;> simp
  exact (congrArg Finset.card hs).trans h

theorem decoder_law (x : Option (Fin M)) :
    ((Finset.univ.filter fun b : BitVec 256 => decode b=x).card:ℝ)/
      Fintype.card (BitVec 256) = securityWeights.classMass x := by
  cases x with
  | none =>
    rw [card_decode_none,Fintype.card_bitVec]
    change ((2^256-A*2^127:ℕ):ℝ)/(2^256:ℕ) = 1-∑ i : Fin M,classProbability i
    rw [classProbability_sum]
    change ((2^256-WeightedResearch92.acceptedAliases*2^127:ℕ):ℝ)/(2^256:ℕ) = _
    rw [WeightedResearch92.aliases_exact]
    norm_num [acceptance]
  | some i =>
    change ((Finset.univ.filter fun b : BitVec 256 => decode b=some i).card:ℝ)/
      Fintype.card (BitVec 256) = classProbability i
    rw [Fintype.card_bitVec,Nat.cast_pow,Nat.cast_ofNat]
    exact class_probability_real i

#print axioms decoder_law
end OptimalOTS.WeightedConstruction.WeightedSchedule
