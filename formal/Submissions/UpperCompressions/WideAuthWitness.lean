import Submissions.UpperCompressions.WideAuthGame

/-! Retain the actual forged input for the public-exposure posterior proof.
The terminal event is tied to that output, not an existential private-cache hit. -/
open OracleSpec OracleComp OracleComp.EvalDist ENNReal
noncomputable section
open scoped Classical
set_option maxRecDepth 10000
attribute [local irreducible] Finset.univ Finset.filter OptimalOTS.WeightedResearch92.classes
namespace OptimalOTS.WeightedConstruction.WideForest
open OptimalOTS.Dag Name
variable (A : forestScheme.toAlgorithm.Adversary)

abbrev ForgeryResult := Message × WeightedScheme.Signature × Bool

def stBWithForgery (pk : PublicKey) (m₁ : Message) (st : A.State)
    (σ : Option WeightedScheme.Signature) : OracleComp Spec ForgeryResult := do
  let (m₂, σ₂) ← A.forge st σ
  let ok ← forestScheme.verify pk m₂ σ₂
  return (m₂, σ₂, ok && decide (σ.map (fun s => (m₁, s)) ≠ some (m₂, σ₂)))

theorem stBWithForgery_map (pk : PublicKey) (m₁ : Message) (st : A.State)
    (σ : Option WeightedScheme.Signature) :
    (fun r : ForgeryResult => r.2.2) <$> stBWithForgery A pk m₁ st σ = stB A pk m₁ st σ := by
  unfold stBWithForgery stB
  simp only [map_bind, map_pure]

theorem stBWithForgery_support (pk : PublicKey) (m₁ : Message) (st : A.State)
    (σ : Option WeightedScheme.Signature) (c : Cache) (p : ForgeryResult × Cache)
    (hp : p ∈ support (run (stBWithForgery A pk m₁ st σ) c)) (hok : p.1.2.2 = true) :
    ∃ c₁, σ.map (fun s => (m₁, s)) ≠ some (p.1.1, p.1.2.1) ∧
      (true, p.2) ∈ support (run (forestScheme.verify pk p.1.1 p.1.2.1) c₁) := by
  unfold stBWithForgery at hp
  rw [run_bind, support_bind] at hp
  simp only [Set.mem_iUnion] at hp
  obtain ⟨⟨⟨m₂, σ₂⟩, c₁⟩, h₁, hp⟩ := hp
  dsimp only at hp
  rw [run_bind, support_bind] at hp
  simp only [Set.mem_iUnion] at hp
  obtain ⟨⟨ok, c₂⟩, h₂, hp⟩ := hp
  rw [run_pure, support_pure, Set.mem_singleton_iff] at hp
  subst p
  simp only [Bool.and_eq_true, decide_eq_true_iff] at hok
  obtain ⟨hok, hne⟩ := hok
  subst ok
  exact ⟨c₁, hne, h₂⟩

/-- The selected forged message/nonce is explicitly retained. Outside graph
badness its own verification query has the signed class and is a different input. -/
theorem stBWithForgery_index_witness (ξ : Rec) (i : Fin WeightedSchedule.M) (η : BitVec 86)
    (m₁ : Message) (st : A.State) (c : Cache) (p : ForgeryResult × Cache)
    (hp : p ∈ support (run (stBWithForgery A (pkOf ξ) m₁ st
      (some (η, revealed (setsName i) ξ))) c)) (hok : p.1.2.2 = true) :
    ∃ w, p.2 (encQuery (p.1.1, p.1.2.1.1)) = some w ∧
      (Spr p.2 ξ ∨ Cache.Hits p.2 (fHid (some (setsName i)) ξ) ∨
        (WeightedSchedule.decode w = some i ∧ (p.1.1, p.1.2.1.1) ≠ (m₁,η))) := by
  obtain ⟨c₁, hne, hv⟩ := stBWithForgery_support A (pkOf ξ) m₁ st _ c p hp hok
  obtain ⟨w, hw, j, hj, he | hs | hh⟩ :=
    accepted_class_cases ξ i p.1.1 p.1.2.1 c₁ p.2 hv
  · obtain ⟨rfl, hpayload⟩ := he
    refine ⟨w, hw, Or.inr (Or.inr ⟨hj, ?_⟩)⟩
    intro hinput
    have hm : p.1.1 = m₁ := congrArg (fun u : EncInput => u.1) hinput
    have hn : p.1.2.1.1 = η := congrArg (fun u : EncInput => u.2) hinput
    have hpair : (p.1.1, p.1.2.1) = (m₁, (η, revealed (setsName j) ξ)) :=
      Prod.ext hm (Prod.ext hn hpayload)
    exact hne (congrArg some hpair.symm)
  · exact ⟨w, hw, Or.inl hs⟩
  · exact ⟨w, hw, Or.inr (Or.inl hh)⟩

end OptimalOTS.WeightedConstruction.WideForest
#print axioms OptimalOTS.WeightedConstruction.WideForest.stBWithForgery_map
#print axioms OptimalOTS.WeightedConstruction.WideForest.stBWithForgery_index_witness
