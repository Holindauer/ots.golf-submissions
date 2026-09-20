import Submissions.UpperCompressions.ReplacementPrefix
import Submissions.UpperCompressions.ReplacementMixture

/-! Compositional probability factorization: after fixing the returned signing
value, any adaptive public-prefix event contributes coordinate-independent
evidence. The equality is proved from actual `ProbComp` bind semantics. -/

open OracleSpec OracleComp OracleComp.EvalDist ENNReal
open OptimalOTS

namespace WeightedReplacement

noncomputable section
open scoped Classical
local instance stagedLocal_ReplacementFactorization_1 {α : Type*} : DecidableEq α := Classical.decEq α

def taggedBind {β α : Type} (p : ProbComp β) (post : β → ProbComp α) : ProbComp (β × α) := do
  let b ← p
  let a ← post b
  pure (b,a)

/-- Fixing the first computation's returned value factors its probability from
the conditional continuation. No independence of the unconditioned outcomes is asserted. -/
theorem E_taggedBind_event {β α : Type} (p : ProbComp β) (post : β → ProbComp α)
    (b : β) (event : α → Prop) :
    E (taggedBind p post) (fun r => if r.1 = b ∧ event r.2 then 1 else 0) =
      E p (fun b' => if b' = b then 1 else 0) *
        E (post b) (fun a => if event a then 1 else 0) := by
  calc
    _ = E p (fun b' => (if b' = b then 1 else 0) *
        E (post b) (fun a => if event a then 1 else 0)) := by
      rw [taggedBind, E_bind]
      congr 1
      funext b'
      simp only [E_bind, E_pure]
      by_cases hb : b' = b
      · subst b'
        simp
      · simp [hb, E, expectedValue_def]
    _ = _ := expectedValue_mul_const p _ _

/-- Actual adaptive post-sign evidence is unchanged when the hidden table cell
is resampled. The signer distribution p is allowed to depend on that cell. -/
theorem E_taggedPrefix_update {β α : Type} (p : ProbComp β)
    (post : β → OracleComp Spec α) (b : β) (u : Query)
    (table : Query → BitVec hashBits) (y : BitVec hashBits)
    (event : Option α × PublicTrace → Prop) :
    E (taggedBind p (fun b' => prefixRun u (Function.update table u y) (post b')))
        (fun r => if r.1 = b ∧ event r.2 then 1 else 0) =
      E p (fun b' => if b' = b then 1 else 0) *
        E (prefixRun u table (post b)) (fun a => if event a then 1 else 0) := by
  rw [E_taggedBind_event, prefix_event_update]

def prefixEvidence {α : Type} (u : Query) (table : Query → BitVec hashBits)
    (oa : OracleComp Spec α) (event : Option α × PublicTrace → Prop) : ℝ :=
  (E (prefixRun u table oa) (fun t => if event t then 1 else 0)).toReal

theorem prefixEvidence_nonneg {α : Type} (u : Query) (table : Query → BitVec hashBits)
    (oa : OracleComp Spec α) (event : Option α × PublicTrace → Prop) :
    0 ≤ prefixEvidence u table oa event := ENNReal.toReal_nonneg

theorem ofReal_prefixEvidence {α : Type} (u : Query) (table : Query → BitVec hashBits)
    (oa : OracleComp Spec α) (event : Option α × PublicTrace → Prop) :
    ENNReal.ofReal (prefixEvidence u table oa event) =
      E (prefixRun u table oa) (fun t => if event t then 1 else 0) := by
  apply ENNReal.ofReal_toReal
  apply ne_of_lt
  apply lt_of_le_of_lt (E_le_one _ (fun _ => by split_ifs <;> simp))
  simp

/-- Real-valued form of the actual program factorization, ready for the finite
Bayes mixture lemma. The supplied signing likelihood is an exact probability,
not an upper bound; the complete-row sampler theorem supplies this premise. -/
theorem E_taggedPrefix_ofReal {β α : Type} (p : ProbComp β)
    (post : β → OracleComp Spec α) (b : β) (u : Query)
    (table : Query → BitVec hashBits) (y : BitVec hashBits)
    (event : Option α × PublicTrace → Prop) (likelihood : ℝ)
    (hl : 0 ≤ likelihood)
    (hp : E p (fun b' => if b' = b then 1 else 0) = ENNReal.ofReal likelihood) :
    E (taggedBind p (fun b' => prefixRun u (Function.update table u y) (post b')))
        (fun r => if r.1 = b ∧ event r.2 then 1 else 0) =
      ENNReal.ofReal (likelihood * prefixEvidence u table (post b) event) := by
  rw [E_taggedPrefix_update, hp, ENNReal.ofReal_mul hl, ofReal_prefixEvidence]

#print axioms E_taggedBind_event
#print axioms E_taggedPrefix_update
#print axioms E_taggedPrefix_ofReal

end
end WeightedReplacement
