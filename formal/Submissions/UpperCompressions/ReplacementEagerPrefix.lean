import Submissions.UpperCompressions.ReplacementActualPrefix
import Submissions.UpperCompressions.ReplacementLengthSlice

/-! Averaging the actual first-exposure bound over the finite eager index table.
Initial cache entries retain priority. The distinguished input is required to
be absent before signing; signer-private visits are then handled by preloading. -/

open OracleSpec OracleComp OracleComp.EvalDist ENNReal
open OptimalOTS OptimalOTS.WeightedSampling
namespace WeightedReplacement
noncomputable section
open scoped Classical
local instance (priority := 100000) stagedLocal_ReplacementEagerPrefix_1 {α : Type*} : DecidableEq α := Classical.decEq α
attribute [local irreducible] hashBits msgBits signBudget

theorem E_left_mul {α : Type} (p : ProbComp α) (a : ℝ≥0∞) (f : α → ℝ≥0∞) :
    E p (fun x => a*f x) = a*E p f := by
  simpa only [mul_comm] using expectedValue_mul_const p f a

theorem preload_update_overwrite {D : Type} (S : QuerySlice D) (c : Cache)
    (g : D → BitVec hashBits) (q : Query) (d : D) (y : BitVec hashBits)
    (hc : c q = none) (hq : S.locate q = some d) :
    S.preload c (Function.update g d y) = overwrite (S.preload c g) q y := by
  funext r
  by_cases hr : r = q
  · subst r
    simp [overwrite, Function.update, QuerySlice.preload, Cache.extend, QuerySlice.tableCache, hc, hq]
  · have ho : overwrite (S.preload c g) q y r = S.preload c g r := by
      simp [overwrite, Function.update, hr, Ne.symm hr]
    rw [ho]
    unfold QuerySlice.preload Cache.extend QuerySlice.tableCache
    cases hrd : S.locate r with
    | none => simp [hrd]
    | some d' =>
      have hdd : d' ≠ d := by
        intro hd
        subst d'
        exact hr (S.unique hrd hq)
      simp [hrd, Function.update, hdd, Ne.symm hdd]

theorem E_preload_resampling {D : Type} [Fintype D] [SampleableType (D → BitVec hashBits)]
    (S : QuerySlice D) (c : Cache) (q : Query) (d : D)
    (hc : c q = none) (hq : S.locate q = some d)
    (F : BitVec hashBits → Cache → ℝ≥0∞) :
    E ($ᵗ (D → BitVec hashBits)) (fun g => E ($ᵗ BitVec hashBits)
      (fun y => F y (overwrite (S.preload c g) q y))) =
    E ($ᵗ (D → BitVec hashBits)) (fun g => F (g d) (S.preload c g)) := by
  rw [E_independent_swap]
  let ψ : (D → BitVec hashBits) → ℝ≥0∞ := fun g => F (g d) (S.preload c g)
  have he (y : BitVec hashBits) (g : D → BitVec hashBits) :
      F y (overwrite (S.preload c g) q y) = ψ (Function.update g d y) := by
    dsimp only [ψ]
    rw [Function.update_self, preload_update_overwrite S c g q d y hc hq]
  simp_rw [he]
  exact E_uniform_update d ψ

def cachedRow (n : ℕ) (m : Message) (c : Cache)
    (g : BitVec (msgBits+n) → BitVec hashBits) : Nonce n → BitVec hashBits :=
  fun η => (c ⟨msgBits+n,m++η⟩).getD (g (m++η))

theorem length_preload_row (n : ℕ) (m : Message) (c : Cache)
    (g : BitVec (msgBits+n) → BitVec hashBits) :
    ∀ η, (lengthSlice (msgBits+n)).preload c g ⟨msgBits+n,m++η⟩ =
      some (cachedRow n m c g η) := by
  intro η
  unfold QuerySlice.preload
  rw [Cache.extend_apply, lengthSlice_inside]
  cases hc : c ⟨msgBits+n,m++η⟩ <;> simp [cachedRow, hc]

theorem E_resampledActualPrefix {M : ℕ} {α : Type} (n : ℕ)
    (decode : BitVec hashBits → Option (Fin M)) (tier : Fin M → ℕ) (m : Message) (k : ℕ)
    (post : Option (Winner n M) → OracleComp Spec α) (u : Nonce n) (c : Cache)
    (hc : c ⟨msgBits+n,m++u⟩ = none)
    (F : BitVec hashBits → (Option (Winner n M) × (Option α × PublicTrace)) → ℝ≥0∞) :
    E ($ᵗ (BitVec (msgBits+n) → BitVec hashBits)) (fun g =>
      E (resampledActualPrefix n decode tier m k post u ((lengthSlice (msgBits+n)).preload c g))
        (fun r => F r.1 r.2)) =
    E ($ᵗ (BitVec (msgBits+n) → BitVec hashBits)) (fun g =>
      E (actualSignedPrefix n decode tier m k post ⟨msgBits+n,m++u⟩
        ((lengthSlice (msgBits+n)).preload c g)) (F (g (m++u)))) := by
  simp only [resampledActualPrefix, E_bind, E_pure]
  exact E_preload_resampling (lengthSlice (msgBits+n)) c ⟨msgBits+n,m++u⟩ (m++u) hc
    (queryAtLength_mk _ _) (fun y d => E (actualSignedPrefix n decode tier m k post ⟨msgBits+n,m++u⟩ d) (F y))

/-- The class posterior inequality under the actual uniformly preloaded finite
table, for every fixed pre-sign cache and adaptive public continuation. Input u
may be visited privately by signing, but has no pre-sign public cache entry. -/
theorem eager_prefix_class_bound {M : ℕ} {α : Type} (n : ℕ)
    (decode : BitVec hashBits → Option (Fin M)) (tier : Fin M → ℕ) (m : Message) (k : ℕ)
    (c : Cache) (post : Option (Winner n M) → OracleComp Spec α)
    (u v : Nonce n) (i : Fin M) (hvu : v ≠ u) (hc : c ⟨msgBits+n,m++u⟩ = none)
    (event : Option α × PublicTrace → Prop) (hmass : 0 < fraction (weakRank tier i ∘ decode)) :
    E ($ᵗ (BitVec (msgBits+n) → BitVec hashBits)) (fun g =>
      E (actualSignedPrefix n decode tier m k post ⟨msgBits+n,m++u⟩
        ((lengthSlice (msgBits+n)).preload c g))
        (fun r => if decode (g (m++u)) = some i ∧ r.1 = some (v,i) ∧ event r.2 then 1 else 0)) ≤
      ENNReal.ofReal (fraction (fun y => decode y = some i) / fraction (weakRank tier i ∘ decode)) *
        E ($ᵗ (BitVec (msgBits+n) → BitVec hashBits)) (fun g =>
          E (actualSignedPrefix n decode tier m k post ⟨msgBits+n,m++u⟩
            ((lengthSlice (msgBits+n)).preload c g))
            (fun r => if r.1 = some (v,i) ∧ event r.2 then 1 else 0)) := by
  have hpoint (g : BitVec (msgBits+n) → BitVec hashBits) :=
    actual_prefix_class_bound n decode tier m k (cachedRow n m c g)
      ((lengthSlice (msgBits+n)).preload c g) (length_preload_row n m c g)
      post u v i hvu event hmass
  have h := E_mono ($ᵗ (BitVec (msgBits+n) → BitVec hashBits)) hpoint
  rw [E_left_mul] at h
  have hn := E_resampledActualPrefix n decode tier m k post u c hc
    (fun y r => if decode y = some i ∧ r.1 = some (v,i) ∧ event r.2 then 1 else 0)
  have hd := E_resampledActualPrefix n decode tier m k post u c hc
    (fun _ r => if r.1 = some (v,i) ∧ event r.2 then 1 else 0)
  rw [hn, hd] at h
  exact h

#print axioms E_preload_resampling
#print axioms eager_prefix_class_bound

end
end WeightedReplacement
