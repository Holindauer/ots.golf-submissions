import Submissions.UpperCompressions.ReplacementSignedUnion
import Submissions.UpperCompressions.ReplacementCrossRow

/-! The actual all-L signer and adaptive forge/verify continuation satisfy a
joint fresh-index bound. Public freshness is measured before signing, so private
signing queries, including accepted nonwinners, do not invalidate the theorem. -/

open OracleSpec OracleComp OracleComp.EvalDist ENNReal
open OptimalOTS OptimalOTS.WeightedSampling
namespace WeightedReplacement
noncomputable section
open scoped Classical BigOperators
local instance (priority := 100000) stagedLocal_ReplacementFreshIndex_1 {α : Type*} : DecidableEq α := Classical.decEq α
attribute [local irreducible] hashBits msgBits signBudget

def indexInput (n : ℕ) (d : Message × Nonce n) : Query := ⟨msgBits+n,d.1++d.2⟩

def freshAlternative (n : ℕ) (c : Cache) (signed d : Message × Nonce n) : Prop :=
  c (indexInput n d) = none ∧ d ≠ signed

def isIndexLength (b : ℕ) : Spec.Domain → Prop
  | .inl _ => False
  | .inr q => q.1 = b

theorem indexInput_injective (n : ℕ) : Function.Injective (indexInput n) := by
  rintro ⟨m,u⟩ ⟨m',u'⟩ h
  have hmm : m = m' := by
    by_contra hne
    exact different_message_rows n m m' hne u' u h
  subst m'
  have huu : u = u' := rowQuery_injective n m h
  subst u'
  rfl

theorem indexInput_paid (n : ℕ) (d : Message × Nonce n) :
    1 ≤ queryCost (.inr (indexInput n d)) := le_max_left _ _

theorem class_prior_le_posterior {M : ℕ}
    (decode : BitVec hashBits → Option (Fin M)) (tier : Fin M → ℕ) (i : Fin M)
    (hmass : 0 < fraction (weakRank tier i ∘ decode)) :
    fraction (fun y => decode y = some i) ≤
      fraction (fun y => decode y = some i) / fraction (weakRank tier i ∘ decode) := by
  have hp : 0 ≤ fraction (fun y => decode y = some i) := by
    unfold fraction uniformMean
    exact div_nonneg (Finset.sum_nonneg (fun _ _ => by split_ifs <;> norm_num)) (Nat.cast_nonneg _)
  have hw : fraction (weakRank tier i ∘ decode) ≤ 1 := by
    unfold fraction
    calc
      _ ≤ uniformMean (fun _ : BitVec hashBits => (1:ℝ)) :=
        uniformMean_mono _ _ (fun _ => by split_ifs <;> norm_num)
      _ = _ := uniformMean_const 1
  exact (le_div_iff₀ hmass).2 ((mul_le_mul_of_nonneg_left hw hp).trans_eq (mul_one _))

/-- Every eligible public target, in the signing row or any other message row,
has the required joint first-exposure rate under the actual finite full table. -/
theorem eager_fresh_hit_bound {M : ℕ} {α : Type} (n : ℕ)
    (decode : BitVec hashBits → Option (Fin M)) (tier : Fin M → ℕ) (m : Message) (k : ℕ)
    (c : Cache) (post : Option (Winner n M) → OracleComp Spec α)
    (v : Nonce n) (i : Fin M) (d : Message × Nonce n)
    (hd : freshAlternative n c (m,v) d)
    (hmass : 0 < fraction (weakRank tier i ∘ decode)) :
    E ($ᵗ (BitVec (msgBits+n) → BitVec hashBits)) (fun g =>
      if decode (g (d.1++d.2)) = some i then
        signedHit (run (loop n decode tier m k) ((lengthSlice (msgBits+n)).preload c g))
          post (some (v,i)) (indexInput n d) else 0) ≤
      ENNReal.ofReal (fraction (fun y => decode y = some i) / fraction (weakRank tier i ∘ decode)) *
        E ($ᵗ (BitVec (msgBits+n) → BitVec hashBits)) (fun g =>
          signedHit (run (loop n decode tier m k) ((lengthSlice (msgBits+n)).preload c g))
            post (some (v,i)) (indexInput n d)) := by
  simp_rw [signedHit_actual_gate, signedHit_actual_eq]
  obtain ⟨m',u⟩ := d
  by_cases hmm : m = m'
  · subst m'
    have hvu : v ≠ u := by
      intro h
      exact hd.2 (by simp [h])
    exact eager_prefix_class_bound n decode tier m k c post u v i hvu hd.1
      (fun r => r.1 = none) hmass
  · have hh := eager_cross_row_class_bound n decode tier m m' k c post u v i hmm hd.1
      (fun r => r.1 = none)
    exact hh.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal (class_prior_le_posterior decode tier i hmass)) le_rfl)

/-- The fresh accepted class of the actual forged input is charged to the actual
paid index queries of the same forge/verify execution. Signing and its private
cache are kept intact, and the signed value remains a joint event throughout. -/
theorem eager_fresh_chosen_bound {M : ℕ} {α γ : Type} (n : ℕ)
    (decode : BitVec hashBits → Option (Fin M)) (tier : Fin M → ℕ) (m : Message) (k : ℕ)
    (c : Cache) (forge : Option (Winner n M) → OracleComp Spec α)
    (verify : Option (Winner n M) → α → OracleComp Spec γ)
    (chosen : α → Message × Nonce n) (v : Nonce n) (i : Fin M)
    (hmass : 0 < fraction (weakRank tier i ∘ decode))
    (hquery : ∀ s a d, publicHit (indexInput n (chosen a)) (verify s a) d = 1) :
    E ($ᵗ (BitVec (msgBits+n) → BitVec hashBits)) (fun g =>
      signedChosen (run (loop n decode tier m k) ((lengthSlice (msgBits+n)).preload c g))
        forge chosen (some (v,i)) (freshAlternative n c (m,v))
        (fun d => decode (g (d.1++d.2)) = some i)) ≤
      ENNReal.ofReal (fraction (fun y => decode y = some i) / fraction (weakRank tier i ∘ decode)) *
        E ($ᵗ (BitVec (msgBits+n) → BitVec hashBits)) (fun g =>
          signedCharge (run (loop n decode tier m k) ((lengthSlice (msgBits+n)).preload c g))
            (fun s => forge s >>= verify s) (some (v,i)) (indexPaid (isIndexLength (msgBits+n)))) := by
  apply integrated_signedChosen_bound
    ($ᵗ (BitVec (msgBits+n) → BitVec hashBits))
    (fun g => run (loop n decode tier m k) ((lengthSlice (msgBits+n)).preload c g))
    forge verify (indexInput n) chosen (some (v,i)) (freshAlternative n c (m,v))
    (fun g d => decode (g (d.1++d.2)) = some i) (isIndexLength (msgBits+n)) _
    (indexInput_injective n) (fun _ => rfl) (indexInput_paid n) hquery
  intro d hd
  exact eager_fresh_hit_bound n decode tier m k c (fun s => forge s >>= verify s) v i d hd hmass

#print axioms eager_fresh_hit_bound
#print axioms eager_fresh_chosen_bound
end
end WeightedReplacement
