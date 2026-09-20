import Submissions.UpperCompressions.WideAuthWitness
import Submissions.UpperCompressions.ReplacementPublicUnion

/-! The actual forged input is the verifier's first public index query. -/
open OracleSpec OracleComp OracleComp.EvalDist ENNReal
noncomputable section
open scoped Classical
attribute [local irreducible] Finset.univ Finset.filter
namespace OptimalOTS.WeightedConstruction.WideForest
open WeightedReplacement

def verifyForgery (pk : PublicKey) (m₁ : Message) (σ : Option WeightedScheme.Signature)
    (z : Message × WeightedScheme.Signature) : OracleComp Spec ForgeryResult := do
  let ok ← forestScheme.verify pk z.1 z.2
  return (z.1,z.2,ok && decide (σ.map (fun s => (m₁,s)) ≠ some z))

theorem stBWithForgery_bind (A : forestScheme.toAlgorithm.Adversary)
    (pk : PublicKey) (m₁ : Message) (st : A.State) (σ : Option WeightedScheme.Signature) :
    stBWithForgery A pk m₁ st σ = A.forge st σ >>= verifyForgery pk m₁ σ := by
  unfold stBWithForgery verifyForgery
  congr 1
  funext z
  cases z
  dsimp only [WeightedScheme.Scheme.toAlgorithm]
  congr 1
  funext ok
  congr 3
  congr 1
  exact decide_eq_decide.mpr Iff.rfl

theorem verifyForgery_queries_chosen (pk : PublicKey) (m₁ : Message)
    (σ : Option WeightedScheme.Signature) (z : Message × WeightedScheme.Signature) (c : Cache) :
    publicHit (encQuery (z.1,z.2.1)) (verifyForgery pk m₁ σ z) c = 1 := by
  unfold verifyForgery WeightedScheme.Scheme.verify
  rw [bind_assoc]
  exact publicHit_hash_target (z.1++z.2.1) _ c

theorem stBWithForgery_selected_input_union (A : forestScheme.toAlgorithm.Adversary)
    (pk : PublicKey) (m₁ : Message) (st : A.State) (σ : Option WeightedScheme.Signature)
    (allowed good : EncInput → Prop) (c : Cache) :
    E (run (A.forge st σ) c)
      (fun p => if allowed (p.1.1,p.1.2.1) ∧ good (p.1.1,p.1.2.1) then 1 else 0) ≤
    ∑ u : EncInput, if allowed u ∧ good u then
      publicHit (encQuery u) (stBWithForgery A pk m₁ st σ) c else 0 := by
  have h := selected_input_union encQuery (fun z : Message × WeightedScheme.Signature => (z.1,z.2.1))
    allowed good (A.forge st σ) (verifyForgery pk m₁ σ) c
    (verifyForgery_queries_chosen pk m₁ σ)
  exact h.trans_eq (congrArg (fun oa => ∑ u : EncInput, if allowed u ∧ good u then
    publicHit (encQuery u) oa c else 0) (stBWithForgery_bind A pk m₁ st σ).symm)

#print axioms verifyForgery_queries_chosen
#print axioms stBWithForgery_selected_input_union
end OptimalOTS.WeightedConstruction.WideForest
