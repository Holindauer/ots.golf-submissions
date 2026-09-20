import Submissions.UpperCompressions.ReplacementJointPosterior

/-! Actual all-trial signing followed by an adaptive stopped public prefix.
The prefix keeps the original mixed lazy oracle, and the final signer cache is
passed to it. On a complete row that cache is unchanged, including private hits. -/

open OracleSpec OracleComp OracleComp.EvalDist ENNReal
open OptimalOTS OptimalOTS.WeightedSampling
namespace WeightedReplacement
noncomputable section
open scoped Classical BigOperators
local instance (priority := 100000) stagedLocal_ReplacementActualPrefix_1 {α : Type*} : DecidableEq α := Classical.decEq α
attribute [local irreducible] hashBits msgBits signBudget

theorem rowQuery_injective (n : ℕ) (m : Message) :
    Function.Injective (fun η : Nonce n => (⟨msgBits+n,m++η⟩ : Query)) := by
  intro a b h
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have hh := congrArg (fun q : Query => q.2.getLsbD j) h
  simpa only [BitVec.getLsbD_append, if_pos hj] using hh

theorem overwrite_complete_row (n : ℕ) (m : Message) (table : Nonce n → BitVec hashBits)
    (c : Cache) (hc : ∀ η, c ⟨msgBits+n,m++η⟩ = some (table η))
    (u : Nonce n) (y : BitVec hashBits) :
    ∀ η, overwrite c ⟨msgBits+n,m++u⟩ y ⟨msgBits+n,m++η⟩ =
      some (Function.update table u y η) := by
  intro η
  by_cases hη : η = u
  · subst η
    simp [overwrite]
  · have hq : (⟨msgBits+n,m++η⟩ : Query) ≠ ⟨msgBits+n,m++u⟩ := by
      intro h
      exact hη (rowQuery_injective n m h)
    simp [overwrite, Function.update, hq, Ne.symm hq, hη, Ne.symm hη, hc]

def actualSignedPrefix {M : ℕ} {α : Type} (n : ℕ)
    (decode : BitVec hashBits → Option (Fin M)) (tier : Fin M → ℕ) (m : Message) (k : ℕ)
    (post : Option (Winner n M) → OracleComp Spec α) (u : Query) (c : Cache) :
    ProbComp (Option (Winner n M) × (Option α × PublicTrace)) := do
  let r ← run (loop n decode tier m k) c
  let t ← hybridPrefix u (post r.1) r.2 []
  pure (r.1,t)

theorem actualSignedPrefix_fixed_row {M : ℕ} {α : Type} (n : ℕ)
    (decode : BitVec hashBits → Option (Fin M)) (tier : Fin M → ℕ) (m : Message) (k : ℕ)
    (table : Nonce n → BitVec hashBits) (c : Cache)
    (hc : ∀ η, c ⟨msgBits+n,m++η⟩ = some (table η))
    (post : Option (Winner n M) → OracleComp Spec α) (u : Query) :
    actualSignedPrefix n decode tier m k post u c =
      taggedBind (Prod.fst <$> run (loop n decode tier m k) c)
        (fun b => hybridPrefix u (post b) c []) := by
  rw [actualSignedPrefix, taggedBind, run_loop_fixed_row n decode tier m table c hc k]
  simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def]

def resampledActualPrefix {M : ℕ} {α : Type} (n : ℕ)
    (decode : BitVec hashBits → Option (Fin M)) (tier : Fin M → ℕ) (m : Message) (k : ℕ)
    (post : Option (Winner n M) → OracleComp Spec α) (u : Nonce n) (c : Cache) :
    ProbComp (BitVec hashBits × Option (Winner n M) × (Option α × PublicTrace)) := do
  let y ← $ᵗ BitVec hashBits
  let r ← actualSignedPrefix n decode tier m k post ⟨msgBits+n,m++u⟩
    (overwrite c ⟨msgBits+n,m++u⟩ y)
  pure (y,r)

theorem resampledActualPrefix_eq {M : ℕ} {α : Type} (n : ℕ)
    (decode : BitVec hashBits → Option (Fin M)) (tier : Fin M → ℕ) (m : Message) (k : ℕ)
    (table : Nonce n → BitVec hashBits) (c : Cache)
    (hc : ∀ η, c ⟨msgBits+n,m++η⟩ = some (table η))
    (post : Option (Winner n M) → OracleComp Spec α) (u : Nonce n) :
    resampledActualPrefix n decode tier m k post u c =
      resampledSignedPrefix
        (fun y => Prod.fst <$> run (loop n decode tier m k) (overwrite c ⟨msgBits+n,m++u⟩ y))
        post ⟨msgBits+n,m++u⟩ c := by
  unfold resampledActualPrefix resampledSignedPrefix
  apply bind_congr
  intro y
  rw [actualSignedPrefix_fixed_row n decode tier m k (Function.update table u y)
    (overwrite c ⟨msgBits+n,m++u⟩ y) (overwrite_complete_row n m table c hc u y)]

theorem loop_cached_target_zero {M : ℕ} (n : ℕ)
    (decode : BitVec hashBits → Option (Fin M)) (tier : Fin M → ℕ) (m : Message) (k : ℕ)
    (v : Nonce n) (i : Fin M) (c : Cache) (w : BitVec hashBits)
    (hc : c ⟨msgBits+n,m++v⟩ = some w) (hw : decode w ≠ some i) :
    E (Prod.fst <$> run (loop n decode tier m k) c) (fun b => if b = some (v,i) then 1 else 0) = 0 := by
  rw [E_map]
  apply le_antisymm _ bot_le
  apply (expectedValue_mono_of_support (mx := run (loop n decode tier m k) c)
    (h := fun _ => (0:ℝ≥0∞)) ?_).trans (E_const_le _ 0)
  intro p hp
  by_cases hret : p.1 = some (v,i)
  · obtain ⟨hsub, hwin⟩ := loop_support n decode tier m k c p hp
    obtain ⟨w', hw', hd⟩ := hwin v i hret
    have he : w' = w := Option.some.inj (hw'.symm.trans (hsub _ _ hc))
    exact False.elim (hw (he ▸ hd))
  · simp [Function.comp_def, hret]

/-- A fresh uniform resampling of one publicly unexposed row coordinate, then
the actual all-L signer and actual adaptive mixed-oracle prefix. The joint class
and prefix probability is at most p_i/(1-F_i) times the prefix probability.
The returned nonce is fixed to v≠u; there is no Good-event conditioning and no
assumption that u is absent from the implementation cache. -/
theorem actual_prefix_class_bound {M : ℕ} {α : Type} (n : ℕ)
    (decode : BitVec hashBits → Option (Fin M)) (tier : Fin M → ℕ) (m : Message) (k : ℕ)
    (table : Nonce n → BitVec hashBits) (c : Cache)
    (hc : ∀ η, c ⟨msgBits+n,m++η⟩ = some (table η))
    (post : Option (Winner n M) → OracleComp Spec α) (u v : Nonce n) (i : Fin M)
    (hvu : v ≠ u) (event : Option α × PublicTrace → Prop)
    (hmass : 0 < fraction (weakRank tier i ∘ decode)) :
    E (resampledActualPrefix n decode tier m k post u c)
      (fun r => if decode r.1 = some i ∧ r.2.1 = some (v,i) ∧ event r.2.2 then 1 else 0) ≤
      ENNReal.ofReal (fraction (fun y => decode y = some i) / fraction (weakRank tier i ∘ decode)) *
        E (resampledActualPrefix n decode tier m k post u c)
          (fun r => if r.2.1 = some (v,i) ∧ event r.2.2 then 1 else 0) := by
  rw [resampledActualPrefix_eq n decode tier m k table c hc post u]
  have hrate : 0 ≤ fraction (fun y => decode y = some i) / fraction (weakRank tier i ∘ decode) := by
    apply div_nonneg _ hmass.le
    unfold fraction uniformMean
    exact div_nonneg (Finset.sum_nonneg (fun _ _ => by split_ifs <;> norm_num)) (Nat.cast_nonneg _)
  by_cases hv : decode (table v) = some i
  · let A := fractionExcept (weakRank tier i ∘ decode ∘ table) u
    let B := fractionExcept (strictRank tier i ∘ decode ∘ table) u
    let lik := coordinateLikelihood k A B (1/(Fintype.card (Nonce n):ℝ)) (Fintype.card (Nonce n))
      (weakRank tier i ∘ decode) (strictRank tier i ∘ decode)
    have hl : ∀ y, 0 ≤ lik y := coordinateLikelihood_nonneg k A B _ _ _ _
      (fractionExcept_nonneg _ _) (fractionExcept_nonneg _ _) (by positivity) (by positivity)
    have hp : ∀ y, E (Prod.fst <$> run (loop n decode tier m k) (overwrite c ⟨msgBits+n,m++u⟩ y))
        (fun b => if b = some (v,i) then 1 else 0) = ENNReal.ofReal (lik y) := by
      intro y
      rw [E_map]
      have hv' : decode (Function.update table u y v) = some i := by
        rw [Function.update_of_ne hvu]
        exact hv
      have hh := E_loop_fixed_row_target n M k decode tier m (Function.update table u y)
        (overwrite c ⟨msgBits+n,m++u⟩ y) (overwrite_complete_row n m table c hc u y) v i hv'
      rw [← tableWinnerLikelihood_eq k (Function.update table u y) decode tier v i hv',
        tableWinnerLikelihood_update k table decode tier u v i hvu hv y] at hh
      convert hh using 1
      congr 1
      funext r
      split_ifs <;> rfl
    have hb : uniformMean (fun y => if decode y = some i then lik y else 0) ≤
        (fraction (fun y => decode y = some i) / fraction (weakRank tier i ∘ decode))*uniformMean lik := by
      exact coordinate_uniform_joint k A B _ _ _ _ _
        (fractionExcept_nonneg _ _) (fractionExcept_nonneg _ _) (by positivity) (by positivity)
        (fun y hy => by simp [hy, weakRank, strictRank]) hmass
    have hh := resampledSignedPrefix_bound
      (fun y => Prod.fst <$> run (loop n decode tier m k) (overwrite c ⟨msgBits+n,m++u⟩ y))
      post (some (v,i)) ⟨msgBits+n,m++u⟩ c event (fun y => decode y = some i) lik _ hl hrate hp hb
    convert hh using 1 <;> congr 1 <;> (try funext r) <;> split_ifs <;> rfl
  · have hp : ∀ y, E (Prod.fst <$> run (loop n decode tier m k) (overwrite c ⟨msgBits+n,m++u⟩ y))
        (fun b => if b = some (v,i) then 1 else 0) = ENNReal.ofReal (0:ℝ) := by
      intro y
      rw [ENNReal.ofReal_zero]
      apply loop_cached_target_zero n decode tier m k v i _ (table v) _ hv
      have hq : (⟨msgBits+n,m++v⟩ : Query) ≠ ⟨msgBits+n,m++u⟩ :=
        fun h => hvu (rowQuery_injective n m h)
      simpa [overwrite, Function.update, hq, Ne.symm hq] using hc v
    have hh := resampledSignedPrefix_bound
      (fun y => Prod.fst <$> run (loop n decode tier m k) (overwrite c ⟨msgBits+n,m++u⟩ y))
      post (some (v,i)) ⟨msgBits+n,m++u⟩ c event (fun y => decode y = some i) (fun _ => 0) _
      (fun _ => le_rfl) hrate hp (by simp only [ite_self, uniformMean_const, mul_zero, le_refl])
    convert hh using 1 <;> congr 1 <;> (try funext r) <;> split_ifs <;> rfl

#print axioms actualSignedPrefix_fixed_row
#print axioms actual_prefix_class_bound

end
end WeightedReplacement
