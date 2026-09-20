import Submissions.UpperCompressions.ReplacementFreshIndex

/-! Aligning the fresh-index cost with the reduced graph-authentication
execution: a fixed graph cache can be exposed after the actual signer. -/

open OracleSpec OracleComp OracleComp.EvalDist ENNReal
open OptimalOTS OptimalOTS.WeightedSampling
namespace WeightedReplacement
noncomputable section
open scoped Classical BigOperators
local instance (priority := 100000) stagedLocal_ReplacementFreshOverlay_1 {α : Type*} : DecidableEq α := Classical.decEq α
attribute [local irreducible] hashBits msgBits signBudget

theorem preload_extend_commute (b : ℕ) (c f : Cache)
    (hf : ∀ q : Query, q.1 = b → f q = none)
    (g : BitVec b → BitVec hashBits) :
    (lengthSlice b).preload (Cache.extend c f) g =
      Cache.extend ((lengthSlice b).preload c g) f := by
  funext q
  unfold QuerySlice.preload
  by_cases hq : q.1 = b
  · simp [Cache.extend_apply, hf q hq]
  · simp [Cache.extend_apply, lengthSlice_outside b g q hq]

theorem freshAlternative_extend (n : ℕ) (c f : Cache)
    (hf : ∀ d : Message × Nonce n, f (indexInput n d) = none)
    (s d : Message × Nonce n) :
    freshAlternative n (Cache.extend c f) s d ↔ freshAlternative n c s d := by
  simp [freshAlternative, Cache.extend_apply, hf d]

def exposeCache {β : Type} (p : ProbComp (β × Cache)) (f : Cache) : ProbComp (β × Cache) :=
  (fun r => (r.1,Cache.extend r.2 f)) <$> p

theorem loop_preload_extend (n : ℕ) {M : ℕ}
    (decode : BitVec hashBits → Option (Fin M)) (tier : Fin M → ℕ) (m : Message) (k : ℕ)
    (c f : Cache) (hf : ∀ q : Query, q.1 = msgBits+n → f q = none)
    (g : BitVec (msgBits+n) → BitVec hashBits) :
    run (loop n decode tier m k) ((lengthSlice (msgBits+n)).preload (Cache.extend c f) g) =
      exposeCache (run (loop n decode tier m k) ((lengthSlice (msgBits+n)).preload c g)) f := by
  rw [preload_extend_commute (msgBits+n) c f hf]
  exact run_loop_extend n decode tier m f (fun η => hf _ rfl) k _

/-- The index charge uses exactly the signer terminal cache extended by the
fixed exposed graph cache, as in the recordwise graph authentication bound. -/
theorem eager_fresh_chosen_overlay_bound {M : ℕ} {α γ : Type} (n : ℕ)
    (decode : BitVec hashBits → Option (Fin M)) (tier : Fin M → ℕ) (m : Message) (k : ℕ)
    (c f : Cache) (hf : ∀ q : Query, q.1 = msgBits+n → f q = none)
    (forge : Option (Winner n M) → OracleComp Spec α)
    (verify : Option (Winner n M) → α → OracleComp Spec γ)
    (chosen : α → Message × Nonce n) (v : Nonce n) (i : Fin M)
    (hmass : 0 < fraction (weakRank tier i ∘ decode))
    (hquery : ∀ s a d, publicHit (indexInput n (chosen a)) (verify s a) d = 1) :
    E ($ᵗ (BitVec (msgBits+n) → BitVec hashBits)) (fun g =>
      signedChosen (exposeCache (run (loop n decode tier m k)
        ((lengthSlice (msgBits+n)).preload c g)) f)
        forge chosen (some (v,i)) (freshAlternative n c (m,v))
        (fun d => decode (g (d.1++d.2)) = some i)) ≤
      ENNReal.ofReal (fraction (fun y => decode y = some i) / fraction (weakRank tier i ∘ decode)) *
        E ($ᵗ (BitVec (msgBits+n) → BitVec hashBits)) (fun g =>
          signedCharge (exposeCache (run (loop n decode tier m k)
            ((lengthSlice (msgBits+n)).preload c g)) f)
            (fun s => forge s >>= verify s) (some (v,i)) (indexPaid (isIndexLength (msgBits+n)))) := by
  have h := eager_fresh_chosen_bound n decode tier m k (Cache.extend c f)
    forge verify chosen v i hmass hquery
  simp_rw [loop_preload_extend n decode tier m k c f hf] at h
  have he : freshAlternative n (Cache.extend c f) (m,v) = freshAlternative n c (m,v) := by
    funext d
    exact propext (freshAlternative_extend n c f (fun d => hf _ rfl) (m,v) d)
  rw [he] at h
  exact h

#print axioms loop_preload_extend
#print axioms eager_fresh_chosen_overlay_bound
end
end WeightedReplacement
