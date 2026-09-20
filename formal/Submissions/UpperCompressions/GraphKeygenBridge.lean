import Submissions.UpperCompressions.Keygen

/-! Graph-only key generation wrappers. They deliberately require no scheme,
cut family, nonce width, or signature-size certificate. -/

open OracleSpec OracleComp OracleComp.EvalDist ENNReal
noncomputable section
open scoped Classical

namespace OptimalOTS.WeightedConstruction.GraphKeygenBridge

open OptimalOTS.Dag

/-- Attach any public-key projection to the protected graph key generator. -/
def keygen (G : Graph) {α : Type} (publicKey : G.Assignment → α) :
    OracleComp Spec (α × G.Assignment) := do
  let x ← G.keygen
  pure (publicKey x, x)

/-- The tagged graph's output and lazy-oracle cache are exactly a uniform record. -/
theorem E_run_keygen (G : Graph) {α : Type} (publicKey : G.Assignment → α)
    (T : G.Tagging) (g : (α × G.Assignment) × Cache → ℝ≥0∞) :
    E (run (keygen G publicKey) ∅) g =
      ∑ ξ : G.Rec, (Fintype.card G.Rec : ℝ≥0∞)⁻¹ *
        g ((publicKey (G.evalRec ξ), G.evalRec ξ), G.keygenCache ξ) := by
  have hA0 : (Fintype.card G.Assignment : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hAt : (Fintype.card G.Assignment : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  unfold keygen Graph.keygen
  rw [run_bind, E_bind]
  simp only [run_pure, E_pure]
  rw [run_bind, E_bind, G.E_run_sampleAssignment]
  simp only [G.E_run_evaluate T]
  rw [Fintype.sum_prod_type]
  simp only [Fintype.card_prod, Nat.cast_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun z _ => Finset.sum_congr rfl fun y _ => ?_
  rw [ENNReal.mul_inv (Or.inl hA0) (Or.inl hAt), mul_assoc]

/-- A pathwise budget pays the graph's exact keygen cost before every record's
continuation. This does not use the old fixed-width signature proxy. -/
theorem costAtMost_keygen_bind (G : Graph) {α β : Type}
    (publicKey : G.Assignment → α) (k : α × G.Assignment → OracleComp Spec β) {B : ℕ}
    (h : CostAtMost (keygen G publicKey >>= k) B) :
    G.keygenCost ≤ B ∧ ∀ ξ : G.Rec,
      CostAtMost (k (publicKey (G.evalRec ξ), G.evalRec ξ)) (B - G.keygenCost) := by
  have h' : CostAtMost (G.sampleAssignment >>= fun z =>
      G.evaluate z >>= fun x => k (publicKey x, x)) B := by
    simpa only [keygen, Graph.keygen, bind_assoc, pure_bind] using h
  unfold Graph.sampleAssignment at h'
  have hs := G.costAtMost_sampleFold_bind _ _ _ h'
  simp only [OptimalOTS.foldl_update_finRange] at hs
  have he : ∀ z : G.Assignment,
      ((List.finRange G.size).map G.nodeCost).sum ≤ B ∧
        ∀ y : Fin G.size → BitVec hashBits,
          CostAtMost (k (publicKey (G.evalRec (z, y)), G.evalRec (z, y)))
            (B - ((List.finRange G.size).map G.nodeCost).sum) := fun z =>
    G.costAtMost_evalFold_bind z (fun x => k (publicKey x, x)) _ _ B (hs z)
  have hK : G.keygenCost = ((List.finRange G.size).map G.nodeCost).sum := by
    rw [Graph.keygenCost, Fin.sum_univ_def]
  rw [hK]
  exact ⟨(he (fun _ => 0)).1, fun ξ => (he ξ.1).2 ξ.2⟩

end OptimalOTS.WeightedConstruction.GraphKeygenBridge

#print axioms OptimalOTS.WeightedConstruction.GraphKeygenBridge.E_run_keygen
#print axioms OptimalOTS.WeightedConstruction.GraphKeygenBridge.costAtMost_keygen_bind
