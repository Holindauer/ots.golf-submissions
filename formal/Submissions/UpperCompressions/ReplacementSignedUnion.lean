import Submissions.UpperCompressions.ReplacementPublicUnion
import Submissions.UpperCompressions.ReplacementActualPrefix

/-! Two-phase finite union, retaining the actual signer's terminal cache and
the signed value as a joint event. All costs refer to the same continuation. -/

open OracleSpec OracleComp OracleComp.EvalDist ENNReal
open OptimalOTS OptimalOTS.WeightedSampling
namespace WeightedReplacement
noncomputable section
open scoped Classical BigOperators
local instance (priority := 100000) stagedLocal_ReplacementSignedUnion_1 {α : Type*} : DecidableEq α := Classical.decEq α
attribute [local irreducible] hashBits msgBits signBudget

def signedHit {β γ : Type} (p : ProbComp (β × Cache)) (post : β → OracleComp Spec γ)
    (b : β) (q : Query) : ℝ≥0∞ :=
  E p (fun r => if r.1 = b then publicHit q (post r.1) r.2 else 0)

def signedCharge {β γ : Type} (p : ProbComp (β × Cache)) (post : β → OracleComp Spec γ)
    (b : β) (charge : Spec.Domain → ℝ≥0∞) : ℝ≥0∞ :=
  E p (fun r => if r.1 = b then expectedCharge charge (post r.1) r.2 else 0)

def signedChosen {D β α : Type} (p : ProbComp (β × Cache)) (forge : β → OracleComp Spec α)
    (chosen : α → D) (b : β) (allowed good : D → Prop) : ℝ≥0∞ :=
  E p (fun r => if r.1 = b then E (run (forge r.1) r.2)
    (fun s => if allowed (chosen s.1) ∧ good (chosen s.1) then 1 else 0) else 0)

theorem E_gate {α : Type} (p : ProbComp α) (P : Prop) (f : α → ℝ≥0∞) :
    E p (fun a => if P then f a else 0) = if P then E p f else 0 := by
  by_cases hP : P <;> simp [hP, E, expectedValue_def]

theorem signedChosen_union {D β α γ : Type} [Fintype D]
    (p : ProbComp (β × Cache)) (forge : β → OracleComp Spec α)
    (verify : β → α → OracleComp Spec γ) (e : D → Query) (chosen : α → D)
    (b : β) (allowed good : D → Prop)
    (hquery : ∀ s a c, publicHit (e (chosen a)) (verify s a) c = 1) :
    signedChosen p forge chosen b allowed good ≤
      ∑ d, if allowed d ∧ good d then signedHit p (fun s => forge s >>= verify s) b (e d) else 0 := by
  have hpoint (r : β × Cache) :
      (if r.1 = b then E (run (forge r.1) r.2)
        (fun s => if allowed (chosen s.1) ∧ good (chosen s.1) then 1 else 0) else 0) ≤
      ∑ d, if allowed d ∧ good d then (if r.1 = b then publicHit (e d) (forge r.1 >>= verify r.1) r.2 else 0) else 0 := by
    by_cases hr : r.1 = b
    · simp only [if_pos hr]
      exact selected_input_union e chosen allowed good (forge r.1) (verify r.1) r.2 (hquery r.1)
    · simp [hr]
  calc
    _ ≤ E p (fun r => ∑ d, if allowed d ∧ good d then
        (if r.1 = b then publicHit (e d) (forge r.1 >>= verify r.1) r.2 else 0) else 0) := E_mono p hpoint
    _ = ∑ d, E p (fun r => if allowed d ∧ good d then
        (if r.1 = b then publicHit (e d) (forge r.1 >>= verify r.1) r.2 else 0) else 0) :=
      expectedValue_finsetSum _ _ _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro d _
      by_cases hd : allowed d ∧ good d <;> simp [hd, signedHit, E, expectedValue_def]

theorem signedHit_sum_le_indexPaid {D β γ : Type} [Fintype D] (e : D → Query)
    (he : Function.Injective e) (isIndex : Spec.Domain → Prop)
    (hi : ∀ d, isIndex (.inr (e d))) (hpaid : ∀ d, 1 ≤ queryCost (.inr (e d)))
    (p : ProbComp (β × Cache)) (post : β → OracleComp Spec γ) (b : β) :
    (∑ d, signedHit p post b (e d)) ≤ signedCharge p post b (indexPaid isIndex) := by
  unfold signedHit signedCharge
  rw [← expectedValue_finsetSum p Finset.univ (fun d r => if r.1 = b then publicHit (e d) (post r.1) r.2 else 0)]
  apply E_mono p
  intro r
  by_cases hr : r.1 = b
  · simp only [if_pos hr]
    exact publicHit_sum_le_indexPaid e he isIndex hi hpaid (post r.1) r.2
  · simp [hr]

theorem signedHit_actual_eq {M : ℕ} {α : Type} (n : ℕ)
    (decode : BitVec hashBits → Option (Fin M)) (tier : Fin M → ℕ) (m : Message) (k : ℕ)
    (post : Option (Winner n M) → OracleComp Spec α) (b : Option (Winner n M)) (u : Query) (c : Cache) :
    signedHit (run (loop n decode tier m k) c) post b u =
      E (actualSignedPrefix n decode tier m k post u c)
        (fun r => if r.1 = b ∧ r.2.1 = none then 1 else 0) := by
  unfold signedHit actualSignedPrefix
  simp only [E_bind, E_pure]
  congr 1
  funext r
  by_cases hr : r.1 = b
  · simp only [hr, true_and, if_pos]
    exact publicHit_eq_prefix u (post b) r.2 []
  · simp [hr, E, expectedValue_def]

theorem signedHit_actual_gate {M : ℕ} {α : Type} (n : ℕ)
    (decode : BitVec hashBits → Option (Fin M)) (tier : Fin M → ℕ) (m : Message) (k : ℕ)
    (post : Option (Winner n M) → OracleComp Spec α) (b : Option (Winner n M))
    (u : Query) (c : Cache) (P : Prop) :
    (if P then signedHit (run (loop n decode tier m k) c) post b u else 0) =
      E (actualSignedPrefix n decode tier m k post u c)
        (fun r => if P ∧ r.1 = b ∧ r.2.1 = none then 1 else 0) := by
  by_cases hP : P
  · simp only [hP, true_and, if_true]
    exact signedHit_actual_eq n decode tier m k post b u c
  · simp [hP, E, expectedValue_def]

/-- Joint posterior estimates at each eligible coordinate combine with actual
public input selection and the shared paid-index cost. The estimates are later
instantiated with the checked same-row and cross-row sampler laws. -/
theorem integrated_signedChosen_bound {Z D β α γ : Type} [Fintype D]
    (latent : ProbComp Z) (p : Z → ProbComp (β × Cache))
    (forge : β → OracleComp Spec α) (verify : β → α → OracleComp Spec γ)
    (e : D → Query) (chosen : α → D) (b : β) (allowed : D → Prop) (good : Z → D → Prop)
    (isIndex : Spec.Domain → Prop) (rate : ℝ≥0∞)
    (he : Function.Injective e) (hi : ∀ d, isIndex (.inr (e d)))
    (hpaid : ∀ d, 1 ≤ queryCost (.inr (e d)))
    (hquery : ∀ s a c, publicHit (e (chosen a)) (verify s a) c = 1)
    (hposterior : ∀ d, allowed d →
      E latent (fun z => if good z d then signedHit (p z) (fun s => forge s >>= verify s) b (e d) else 0) ≤
        rate * E latent (fun z => signedHit (p z) (fun s => forge s >>= verify s) b (e d))) :
    E latent (fun z => signedChosen (p z) forge chosen b allowed (good z)) ≤
      rate * E latent (fun z => signedCharge (p z) (fun s => forge s >>= verify s) b (indexPaid isIndex)) := by
  calc
    _ ≤ E latent (fun z => ∑ d, if allowed d ∧ good z d then
        signedHit (p z) (fun s => forge s >>= verify s) b (e d) else 0) :=
      E_mono latent (fun z => signedChosen_union (p z) forge verify e chosen b allowed (good z) hquery)
    _ = ∑ d, E latent (fun z => if allowed d ∧ good z d then
        signedHit (p z) (fun s => forge s >>= verify s) b (e d) else 0) := expectedValue_finsetSum _ _ _
    _ ≤ ∑ d, rate * E latent (fun z => signedHit (p z) (fun s => forge s >>= verify s) b (e d)) := by
      apply Finset.sum_le_sum
      intro d _
      by_cases hd : allowed d
      · simpa only [hd, true_and] using hposterior d hd
      · simp only [hd, false_and, if_false]
        exact (E_const_le _ 0).trans bot_le
    _ = rate * E latent (fun z => ∑ d, signedHit (p z) (fun s => forge s >>= verify s) b (e d)) := by
      rw [← Finset.mul_sum]
      apply congrArg (rate * ·)
      exact (expectedValue_finsetSum latent Finset.univ
        (fun d z => signedHit (p z) (fun s => forge s >>= verify s) b (e d))).symm
    _ ≤ _ := mul_le_mul' le_rfl (E_mono latent
      (fun z => signedHit_sum_le_indexPaid e he isIndex hi hpaid (p z) (fun s => forge s >>= verify s) b))

#print axioms signedChosen_union
#print axioms signedHit_actual_eq
#print axioms integrated_signedChosen_bound

end
end WeightedReplacement
