import Submissions.UpperCompressions.WideScheme
import Submissions.UpperCompressions.WireAdapter

/-! The concrete92 research construction on raw bit-string signatures.
All resources and perfect correctness are checked. Signing availability and
strong unforgeability are deliberately absent until their proofs are complete. -/

open OracleComp ENNReal
noncomputable section
open scoped Classical
set_option maxRecDepth 10000

namespace OptimalOTS.WeightedConstruction.WideWire
open WideForest

abbrev typed := forestScheme.toAlgorithm

def decode (bits : List Bool) : WeightedScheme.Signature := NonceCodec.decode 86 bits

theorem decode_encode (σ : WeightedScheme.Signature) :
    decode (typed.encodeSignature σ) = σ := NonceCodec.decode_encode σ

theorem accepted_payload_positive (pk : PublicKey) (m : Message) (σ : WeightedScheme.Signature)
    (h : true ∈ support (forestScheme.verify pk m σ)) : 0 < σ.2.length := by
  rw [WeightedScheme.Scheme.verify,support_bind] at h
  simp only [Set.mem_iUnion] at h
  obtain ⟨w,_,h⟩ := h
  cases hd : forestScheme.decode w with
  | none => simp [hd] at h
  | some i =>
    simp only [hd] at h
    by_cases hlen : σ.2.length = forestScheme.graph.revealBits (forestScheme.sets i)
    · rw [hlen,forestScheme_revealBits]
      norm_num
    · simp [hlen] at h

theorem canonical (pk : PublicKey) (m : Message) (bits : List Bool)
    (h : true ∈ support (typed.verify pk m (decode bits))) :
    typed.encodeSignature (decode bits) = bits := by
  exact NonceCodec.canonical_of_payload_positive
    (accepted_payload_positive pk m (decode bits) h)

def scheme : OracleAlgorithm.Scheme := WireAdapter.scheme typed decode

theorem cost : scheme.VerifyCostAtMost 92 :=
  WireAdapter.verifyCost typed decode 92 typed_cost

theorem correct : scheme.Correct := WireAdapter.correct typed decode decode_encode typed_correct

theorem signatureSize : scheme.SignatureSizeAtMost maxSignatureBits :=
  WireAdapter.signatureSize typed decode maxSignatureBits typed_signatureSize

theorem rejectsOversized : scheme.RejectsOversized maxSignatureBits :=
  WireAdapter.rejectsOversized typed decode canonical maxSignatureBits typed_rejectsOversized

theorem keygenCost : scheme.KeygenCostAtMost keygenBudget := typed_keygenCost

theorem signCost : scheme.SignCostAtMost signBudget :=
  fun sk m => AlgorithmCosts.CostAtMost.map (typed_signCost sk m) _

theorem verifyDeterministic : scheme.VerifyDeterministic :=
  fun pk m bits => typed_verifyDeterministic pk m (decode bits)

#print axioms cost
#print axioms correct
#print axioms signatureSize
#print axioms rejectsOversized
#print axioms keygenCost
#print axioms signCost
#print axioms verifyDeterministic

end OptimalOTS.WeightedConstruction.WideWire
