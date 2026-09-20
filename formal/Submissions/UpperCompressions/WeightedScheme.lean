import Submissions.UpperCompressions.WeightedSampling
import Submissions.UpperCompressions.NonceCodec
import Submissions.UpperCompressions.GraphKeygenBridge
import Submissions.UpperCompressions.Resources
import Submissions.UpperCompressions.Deterministic
import Submissions.UpperCompressions.Correctness

/-! Generic graph scheme with an86-bit nonce and weighted all-trial signer.
The decoder and tier function are explicit parameters. These resource and
correctness lemmas do not establish availability or strong security. -/

open OracleSpec OracleComp OracleComp.EvalDist ENNReal
noncomputable section
open scoped Classical

namespace OptimalOTS.WeightedScheme

open WeightedConstruction
abbrev Signature := NonceCodec.Signature86

structure Scheme (M : ℕ) where
  graph : Dag.Graph
  sets : Fin M → Finset (Fin graph.size)
  decode : BitVec hashBits → Option (Fin M)
  tier : Fin M → ℕ
  root_not_mem : ∀ i, graph.root ∉ sets i
  no_hidden_source :
    ∀ i v, graph.Visited (sets i) v → v ∉ sets i → ¬ (graph.kind v).IsSource
  reveal_le : ∀ i, graph.revealBits (sets i) + 86 ≤ maxSignatureBits
  keygen_le : graph.keygenCost ≤ keygenBudget

namespace Scheme
variable {M : ℕ} (S : Scheme M)

def publicKey (x : S.graph.Assignment) : PublicKey := (x S.graph.root).setWidth pkBits

def keygen : OracleComp Spec (PublicKey × S.graph.Assignment) :=
  GraphKeygenBridge.keygen S.graph S.publicKey

def sign (x : S.graph.Assignment) (m : Message) : OracleComp Spec (Option Signature) :=
  (Option.map fun r : WeightedSampling.Winner 86 M =>
    (r.1, S.graph.encode (S.sets r.2) x)) <$>
      WeightedSampling.loop 86 S.decode S.tier m signBudget

def verify (pk : PublicKey) (m : Message) (σ : Signature) : OracleComp Spec Bool := do
  let w ← hash (m ++ σ.1)
  match S.decode w with
  | none => return false
  | some i =>
      if σ.2.length = S.graph.revealBits (S.sets i) then
        let y ← S.graph.reconstruct (S.sets i) (S.graph.decode (S.sets i) σ.2)
        return decide (S.publicKey y = pk)
      else
        return false

def toAlgorithm : TypedScheme where
  SecretKey := S.graph.Assignment
  Signature := Signature
  encodeSignature := NonceCodec.encode
  encodeSignature_injective := NonceCodec.encode_injective
  keygen := S.keygen
  sign := S.sign
  verify := S.verify

open AlgorithmCosts

theorem costAtMost_keygen_exact : CostAtMost S.keygen S.graph.keygenCost :=
  CostAtMost.bind_le (AlgorithmCosts.Dag.Graph.costAtMost_keygen S.graph)
    (fun _ => costAtMost_pure _ 0) (by simp)

theorem keygenCost : S.toAlgorithm.KeygenCostAtMost keygenBudget :=
  CostAtMost.mono S.costAtMost_keygen_exact S.keygen_le

theorem signCost : S.toAlgorithm.SignCostAtMost signBudget := fun _x m =>
  CostAtMost.map (WeightedSampling.costAtMost_loop86 S.decode S.tier m) _

theorem verifyCost {v : ℕ} (hv : ∀ i, S.graph.reconstructCost (S.sets i) ≤ v) :
    S.toAlgorithm.VerifyCostAtMost (1+v) := by
  change ∀ (pk : PublicKey) (m : Message) (σ : Signature),
    CostAtMost (S.verify pk m σ) (1+v)
  intro pk m σ
  unfold verify
  refine CostAtMost.bind_le (costAtMost_hash _ WeightedSampling.index86_cost.le)
    (b₂ := v) (fun w => ?_) le_rfl
  cases S.decode w with
  | none => exact costAtMost_pure _ _
  | some i =>
    dsimp only
    split_ifs
    · exact CostAtMost.bind_le
        (CostAtMost.mono
          (AlgorithmCosts.Dag.Graph.costAtMost_reconstruct S.graph (S.sets i) _) (hv i))
        (fun _ => costAtMost_pure _ 0) (by simp)
    · exact costAtMost_pure _ _

theorem verifyDeterministic : S.toAlgorithm.VerifyDeterministic := by
  change ∀ (pk : PublicKey) (m : Message) (σ : Signature),
    Deterministic (S.verify pk m σ)
  intro pk m σ
  unfold verify
  refine Deterministic.bind (Deterministic.hash _) fun w => ?_
  cases S.decode w with
  | none => exact Deterministic.of_pure _
  | some i =>
    dsimp only
    split_ifs
    · exact Deterministic.bind (S.graph.deterministic_reconstruct _ _)
        fun _ => Deterministic.of_pure _
    · exact Deterministic.of_pure _

theorem signatureSize : S.toAlgorithm.SignatureSizeAtMost maxSignatureBits := by
  change ∀ (x : S.graph.Assignment) (m : Message) (σ : Signature),
    some σ ∈ support (S.sign x m) → (NonceCodec.encode σ).length ≤ maxSignatureBits
  intro x m σ h
  change some σ ∈ support (S.sign x m) at h
  rw [sign, support_map, Set.mem_image] at h
  obtain ⟨r, _, hr⟩ := h
  cases r with
  | none => simp at hr
  | some r =>
    simp only [Option.map_some, Option.some.injEq] at hr
    subst σ
    rw [NonceCodec.length_encode, S.graph.length_encode]
    have := S.reveal_le r.2
    omega

theorem rejectsOversized : S.toAlgorithm.RejectsOversized maxSignatureBits := by
  change ∀ (pk : PublicKey) (m : Message) (σ : Signature),
    maxSignatureBits < (NonceCodec.encode σ).length → true ∉ support (S.verify pk m σ)
  intro pk m σ hlen hmem
  change maxSignatureBits < (NonceCodec.encode σ).length at hlen
  rw [NonceCodec.length_encode] at hlen
  change true ∈ support (S.verify pk m σ) at hmem
  rw [verify, support_bind] at hmem
  simp only [Set.mem_iUnion] at hmem
  obtain ⟨w, _, hmem⟩ := hmem
  cases hd : S.decode w with
  | none => simp [hd] at hmem
  | some i =>
    have hwrong : σ.2.length ≠ S.graph.revealBits (S.sets i) := by
      have := S.reveal_le i
      omega
    simp [hd, hwrong] at hmem

theorem keygen_cacheConsistent (c : Cache) :
    ∀ p ∈ support (run S.keygen c),
      p.1.1 = S.publicKey p.1.2 ∧ S.graph.CacheConsistent p.1.2 p.2 := by
  intro p hp
  simp only [keygen, GraphKeygenBridge.keygen, Dag.Graph.keygen,
    run_bind, support_bind, Set.mem_iUnion] at hp
  obtain ⟨⟨x,d⟩, ⟨⟨z,d'⟩, _, hx⟩, hp⟩ := hp
  rw [run_pure, support_pure, Set.mem_singleton_iff] at hp
  subst p
  exact ⟨rfl, S.graph.evaluate_cacheConsistent z d' _ hx⟩

theorem sign_result (x : S.graph.Assignment) (m : Message) (σ : Signature) (c d : Cache)
    (h : (some σ,d) ∈ support (run (S.sign x m) c)) :
    ∃ i : Fin M, ∃ w : BitVec hashBits,
      σ.2 = S.graph.encode (S.sets i) x ∧
      d ⟨msgBits+86,m++σ.1⟩ = some w ∧ S.decode w = some i := by
  rw [sign, run_map, support_map, Set.mem_image] at h
  obtain ⟨⟨r,d'⟩, hr, he⟩ := h
  cases r with
  | none => simp at he
  | some r =>
    obtain ⟨η,i⟩ := r
    simp only [Option.map_some, Prod.mk.injEq, Option.some.injEq] at he
    rcases he with ⟨he,rfl⟩
    obtain ⟨w,hw,hi⟩ :=
      (WeightedSampling.loop_support 86 S.decode S.tier m signBudget c _ hr).2 η i rfl
    cases he
    exact ⟨i,w,rfl,hw,hi⟩

theorem verify_accepts (x : S.graph.Assignment) (m : Message) (σ : Signature)
    (c : Cache) (hc : S.graph.CacheConsistent x c) (i : Fin M) (w : BitVec hashBits)
    (hσ : σ.2 = S.graph.encode (S.sets i) x)
    (hw : c ⟨msgBits+86,m++σ.1⟩ = some w) (hi : S.decode w = some i) :
    ∀ p ∈ support (run (S.verify (S.publicKey x) m σ) c), p.1 = true := by
  intro p hp
  unfold verify at hp
  rw [run_bind, WeightedSampling.run_hash_cached _ c w hw, pure_bind, hi] at hp
  dsimp only at hp
  have hlen : σ.2.length = S.graph.revealBits (S.sets i) := by
    rw [hσ,S.graph.length_encode]
  rw [if_pos hlen,run_bind,support_bind] at hp
  simp only [Set.mem_iUnion] at hp
  obtain ⟨⟨y,e⟩,hy,hp⟩ := hp
  obtain ⟨hce,he⟩ := S.graph.reconstruct_support _ _ c (y,e) hy
  rw [hσ] at he
  have hec := Dag.Graph.CacheConsistent.mono S.graph hce hc
  have hr := GenericCorrectness.reconstruct_eq S.graph (S.sets i) x y e hec
    (S.no_hidden_source i) he S.graph.root Dag.Graph.Visited.root
  rw [run_pure,support_pure,Set.mem_singleton_iff] at hp
  subst p
  simp only [publicKey,hr,decide_true]

/-- Perfect correctness, including public-key-dependent message choices. -/
theorem correct : S.toAlgorithm.Correct := by
  intro message
  dsimp only [toAlgorithm]
  unfold probTrue
  rw [StateT.run'_eq,probOutput_eq_zero_iff,support_map]
  rintro ⟨⟨b,e⟩,h,hb⟩
  change (b,e) ∈ support (run _ ∅) at h
  rw [run_bind,support_bind] at h
  simp only [Set.mem_iUnion] at h
  obtain ⟨⟨⟨pk,sk⟩,c⟩,hk,h⟩ := h
  rw [run_bind,support_bind] at h
  simp only [Set.mem_iUnion] at h
  obtain ⟨⟨σ,d⟩,hs,h⟩ := h
  obtain ⟨hpk,hkc⟩ := S.keygen_cacheConsistent ∅ _ hk
  dsimp only at hpk hkc
  subst pk
  change b = true at hb
  cases σ with
  | none =>
    simp only [run_pure,support_pure,Set.mem_singleton_iff,Prod.mk.injEq] at h
    cases h.1.symm.trans hb
  | some σ =>
    obtain ⟨i,w,hσ,hw,hi⟩ := S.sign_result sk (message (S.publicKey sk)) σ c d hs
    have hcd := sub_of_mem_support_run (S.sign sk (message (S.publicKey sk))) c _ hs
    have hdc := Dag.Graph.CacheConsistent.mono S.graph hcd hkc
    rw [run_bind,support_bind] at h
    simp only [Set.mem_iUnion] at h
    obtain ⟨⟨ok,f⟩,hv,h⟩ := h
    have hok : ok = true := S.verify_accepts sk (message (S.publicKey sk)) σ d hdc
      i w hσ hw hi _ hv
    simp only [hok,Bool.not_true,run_pure,support_pure,Set.mem_singleton_iff,
      Prod.mk.injEq] at h
    cases h.1.symm.trans hb

#print axioms correct

#print axioms keygenCost
#print axioms signCost
#print axioms verifyCost
#print axioms verifyDeterministic
#print axioms signatureSize
#print axioms rejectsOversized

end Scheme
end OptimalOTS.WeightedScheme
