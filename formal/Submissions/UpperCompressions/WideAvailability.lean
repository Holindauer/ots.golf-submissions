import Submissions.UpperCompressions.WideWire
import Submissions.UpperCompressions.WeightedAvailability
import Submissions.UpperCompressions.WeightedUniform
import Submissions.UpperCompressions.WeightedFreshness
import Submissions.UpperCompressions.AvailabilityEnvelope
import Submissions.UpperCompressions.WeightedOutputFibers

/-! Honest signing availability for the concrete weighted92 construction.
The nonce draws may repeat; the proof uses the actual memoized random oracle.
Strong security remains a separate obligation. -/

open OracleSpec OracleComp OracleComp.EvalDist ENNReal
noncomputable section
open scoped Classical
set_option maxRecDepth 10000

namespace OptimalOTS.WeightedConstruction.WideHonest
open WideForest
open WeightedSampling.Availability
attribute [local irreducible] Finset.univ Finset.filter
attribute [local irreducible] WeightedResearch92.classes WeightedResearch92.acceptedAliases

theorem uniform_miss (a : ℝ≥0∞) :
    E ($ᵗ BitVec hashBits) (fun w => if (forestScheme.decode w).isNone then a else 0) =
      _root_.WeightedAvailability.miss*a := by
  change E ($ᵗ BitVec 256) (fun w => if (WeightedSchedule.decode w).isNone then a else 0) = _
  rw [uniform_option_miss WeightedSchedule.decode (WeightedSchedule.A*2^127)
    WeightedSchedule.accepted_decode_count a]
  have hA : WeightedSchedule.A = 45*2^110 := WeightedResearch92.aliases_exact
  rw [hA]
  congr 1
  unfold _root_.WeightedAvailability.miss
  apply (ENNReal.div_eq_div_iff (by norm_num) (by finiteness)
    (by norm_num) (by finiteness)).2
  norm_num

theorem sign_failure_fresh (x : forestScheme.graph.Assignment) (m : Message) (c : Cache)
    (hf : ∀ η : BitVec 86, c ⟨msgBits+86,m++η⟩ = none) :
    E (run (forestScheme.sign x m) c) (fun p => if p.1.isNone then 1 else 0) ≤
      1/(2:ℝ≥0∞)^129 := by
  rw [WeightedScheme.Scheme.sign,run_map,E_map]
  simp only [Option.isNone_map]
  have h := WeightedSampling.Availability.loop_failure 86 forestScheme.decode forestScheme.tier
    m signBudget _root_.WeightedAvailability.miss (fun a => (uniform_miss a).le)
    signBudget ∅ c (by simp) (fun η _ => hf η)
  have hh : (_root_.WeightedAvailability.miss+(signBudget:ℝ≥0∞)/2^86)^signBudget ≤
      1/(2:ℝ≥0∞)^129 := by
    simpa only [signBudget,Nat.cast_pow,Nat.cast_ofNat] using
      _root_.WeightedAvailability.replacement_envelope
  exact h.trans hh

theorem graph_hashInputsAvoid : WeightedFreshness.HashInputsAvoid graph (msgBits+86) := by
  intro v
  obtain ⟨n,rfl⟩ := nameEquiv.surjective v
  erw [graph_kind_fin]
  cases n <;> simp [kindOf,graph_len_fin,Name.len,msgBits]

theorem keygen_fresh (p : (PublicKey × forestScheme.graph.Assignment) × Cache)
    (hp : p ∈ support (run forestScheme.keygen ∅)) (q : Query) (hq : q.1 = msgBits+86) :
    p.2 q = none := by
  have h : WeightedFreshness.PreservesLength (msgBits+86) forestScheme.keygen :=
    WeightedFreshness.PreservesLength.bind
      (WeightedFreshness.graph_keygen_preservesLength graph graph_hashInputsAvoid)
      (fun _ => WeightedFreshness.PreservesLength.of_pure _)
  simpa using h ∅ p hp q hq

theorem signing_failure_half : forestScheme.toAlgorithm.SigningFailureAtMost (1/2^129) := by
  intro message
  change probTrue (do
    let kg ← forestScheme.keygen
    let σ ← forestScheme.sign kg.2 (message kg.1)
    pure σ.isNone) ≤ _
  rw [WeightedFreshness.probTrue_eq_E_run,run_bind,E_bind]
  simp only [run_bind,E_bind,run_pure,E_pure]
  calc
    _ ≤ E (run forestScheme.keygen ∅) (fun _ => (1/2^129 : ℝ≥0∞)) := by
      refine expectedValue_mono_of_support fun p hp => ?_
      apply sign_failure_fresh p.1.2 (message p.1.1) p.2
      intro η
      exact keygen_fresh p hp ⟨msgBits+86,message p.1.1++η⟩ rfl
    _ ≤ _ := E_const_le _ _

theorem signing_failure : forestScheme.toAlgorithm.SigningFailureAtMost (1/2^128) := by
  intro message
  apply (signing_failure_half message).trans
  rw [one_div,one_div]
  apply ENNReal.inv_le_inv.mpr
  norm_num

theorem typed_admissible : forestScheme.toAlgorithm.Admissible (1/2^128) where
  failure_lt_one := by norm_num
  correct := typed_correct
  verifyDeterministic := typed_verifyDeterministic
  signingFailure := signing_failure
  signatureSize := typed_signatureSize
  rejectsOversized := typed_rejectsOversized
  keygenCost := typed_keygenCost
  signCost := typed_signCost

theorem admissible : WideWire.scheme.Admissible :=
  WireAdapter.admissible WideWire.typed WideWire.decode WideWire.decode_encode
    WideWire.canonical typed_admissible

#print axioms uniform_miss
#print axioms signing_failure_half
#print axioms admissible
end OptimalOTS.WeightedConstruction.WideHonest
