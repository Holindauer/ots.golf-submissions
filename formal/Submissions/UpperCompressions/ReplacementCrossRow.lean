import Submissions.UpperCompressions.ReplacementEagerPrefix

/-! A publicly unexposed coordinate in another message row is unaffected by
the signing likelihood. Its joint post-sign class rate is the original prior. -/

open OracleSpec OracleComp OracleComp.EvalDist ENNReal
open OptimalOTS OptimalOTS.WeightedSampling
namespace WeightedReplacement
noncomputable section
open scoped Classical
local instance (priority := 100000) stagedLocal_ReplacementCrossRow_1 {α : Type*} : DecidableEq α := Classical.decEq α
attribute [local irreducible] hashBits msgBits signBudget

def resampledQueryPrefix {M : ℕ} {α : Type} (n : ℕ)
    (decode : BitVec hashBits → Option (Fin M)) (tier : Fin M → ℕ) (m : Message) (k : ℕ)
    (post : Option (Winner n M) → OracleComp Spec α) (q : Query) (c : Cache) :
    ProbComp (BitVec hashBits × Option (Winner n M) × (Option α × PublicTrace)) := do
  let y ← $ᵗ BitVec hashBits
  let r ← actualSignedPrefix n decode tier m k post q (overwrite c q y)
  pure (y,r)

theorem overwrite_other_row (n : ℕ) (m : Message) (table : Nonce n → BitVec hashBits)
    (c : Cache) (hc : ∀ η, c ⟨msgBits+n,m++η⟩ = some (table η))
    (q : Query) (hq : ∀ η : Nonce n, (⟨msgBits+n,m++η⟩ : Query) ≠ q) (y : BitVec hashBits) :
    ∀ η, overwrite c q y ⟨msgBits+n,m++η⟩ = some (table η) := by
  intro η
  simpa [overwrite, Function.update, hq η] using hc η

theorem other_row_class_bound {M : ℕ} {α : Type} (n : ℕ)
    (decode : BitVec hashBits → Option (Fin M)) (tier : Fin M → ℕ) (m : Message) (k : ℕ)
    (table : Nonce n → BitVec hashBits) (c : Cache)
    (hc : ∀ η, c ⟨msgBits+n,m++η⟩ = some (table η))
    (post : Option (Winner n M) → OracleComp Spec α) (q : Query)
    (hq : ∀ η : Nonce n, (⟨msgBits+n,m++η⟩ : Query) ≠ q)
    (v : Nonce n) (i : Fin M) (event : Option α × PublicTrace → Prop) :
    E (resampledQueryPrefix n decode tier m k post q c)
      (fun r => if decode r.1 = some i ∧ r.2.1 = some (v,i) ∧ event r.2.2 then 1 else 0) ≤
      ENNReal.ofReal (fraction (fun y => decode y = some i)) *
        E (resampledQueryPrefix n decode tier m k post q c)
          (fun r => if r.2.1 = some (v,i) ∧ event r.2.2 then 1 else 0) := by
  have heq : resampledQueryPrefix n decode tier m k post q c =
      resampledSignedPrefix (fun y => Prod.fst <$> run (loop n decode tier m k) (overwrite c q y)) post q c := by
    unfold resampledQueryPrefix resampledSignedPrefix
    apply bind_congr
    intro y
    rw [actualSignedPrefix_fixed_row n decode tier m k table (overwrite c q y)
      (overwrite_other_row n m table c hc q hq y)]
  rw [heq]
  let base := E (Prod.fst <$> run (loop n decode tier m k) c) (fun b => if b = some (v,i) then 1 else 0)
  let μ := base.toReal
  have hμ : 0 ≤ μ := ENNReal.toReal_nonneg
  have hbase : ENNReal.ofReal μ = base := by
    apply ENNReal.ofReal_toReal
    exact ne_of_lt (lt_of_le_of_lt (E_le_one _ (fun _ => by split_ifs <;> simp)) (by simp))
  have hp : ∀ y, E (Prod.fst <$> run (loop n decode tier m k) (overwrite c q y))
      (fun b => if b = some (v,i) then 1 else 0) = ENNReal.ofReal μ := by
    intro y
    rw [hbase]
    dsimp only [base]
    rw [run_loop_fixed_row n decode tier m table (overwrite c q y)
      (overwrite_other_row n m table c hc q hq y) k, run_loop_fixed_row n decode tier m table c hc k]
    simp only [E_map]
  have hrate : 0 ≤ fraction (fun y => decode y = some i) := by
    unfold fraction uniformMean
    exact div_nonneg (Finset.sum_nonneg (fun _ _ => by split_ifs <;> norm_num)) (Nat.cast_nonneg _)
  have hb : uniformMean (fun y => if decode y = some i then μ else 0) ≤
      fraction (fun y => decode y = some i)*uniformMean (fun _ : BitVec hashBits => μ) := by
    rw [uniformMean_gate, uniformMean_const]
  have hh := resampledSignedPrefix_bound
    (fun y => Prod.fst <$> run (loop n decode tier m k) (overwrite c q y))
    post (some (v,i)) q c event (fun y => decode y = some i) (fun _ => μ) _
    (fun _ => hμ) hrate hp hb
  convert hh using 1

theorem different_message_rows (n : ℕ) (m m' : Message) (hne : m ≠ m') (u : Nonce n) :
    ∀ η : Nonce n, (⟨msgBits+n,m++η⟩ : Query) ≠ ⟨msgBits+n,m'++u⟩ := by
  intro η h
  apply hne
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have hh := congrArg (fun q : Query => q.2.getLsbD (j+n)) h
  simpa only [BitVec.getLsbD_append, Nat.not_lt.mpr (Nat.le_add_left n j), if_false, Nat.add_sub_cancel] using hh

theorem E_resampledQueryPrefix {M : ℕ} {α : Type} (n : ℕ)
    (decode : BitVec hashBits → Option (Fin M)) (tier : Fin M → ℕ) (m : Message) (k : ℕ)
    (post : Option (Winner n M) → OracleComp Spec α) (x : BitVec (msgBits+n)) (c : Cache)
    (hc : c ⟨msgBits+n,x⟩ = none)
    (F : BitVec hashBits → (Option (Winner n M) × (Option α × PublicTrace)) → ℝ≥0∞) :
    E ($ᵗ (BitVec (msgBits+n) → BitVec hashBits)) (fun g =>
      E (resampledQueryPrefix n decode tier m k post ⟨msgBits+n,x⟩ ((lengthSlice (msgBits+n)).preload c g))
        (fun r => F r.1 r.2)) =
    E ($ᵗ (BitVec (msgBits+n) → BitVec hashBits)) (fun g =>
      E (actualSignedPrefix n decode tier m k post ⟨msgBits+n,x⟩
        ((lengthSlice (msgBits+n)).preload c g)) (F (g x))) := by
  simp only [resampledQueryPrefix, E_bind, E_pure]
  exact E_preload_resampling (lengthSlice (msgBits+n)) c ⟨msgBits+n,x⟩ x hc
    (queryAtLength_mk _ _) (fun y d => E (actualSignedPrefix n decode tier m k post ⟨msgBits+n,x⟩ d) (F y))

/-- Different message rows have the ordinary prior class rate. No nonce
inequality is imposed: the two messages already distinguish the hash inputs. -/
theorem eager_cross_row_class_bound {M : ℕ} {α : Type} (n : ℕ)
    (decode : BitVec hashBits → Option (Fin M)) (tier : Fin M → ℕ) (m m' : Message) (k : ℕ)
    (c : Cache) (post : Option (Winner n M) → OracleComp Spec α)
    (u v : Nonce n) (i : Fin M) (hmm : m ≠ m') (hc : c ⟨msgBits+n,m'++u⟩ = none)
    (event : Option α × PublicTrace → Prop) :
    E ($ᵗ (BitVec (msgBits+n) → BitVec hashBits)) (fun g =>
      E (actualSignedPrefix n decode tier m k post ⟨msgBits+n,m'++u⟩
        ((lengthSlice (msgBits+n)).preload c g))
        (fun r => if decode (g (m'++u)) = some i ∧ r.1 = some (v,i) ∧ event r.2 then 1 else 0)) ≤
      ENNReal.ofReal (fraction (fun y => decode y = some i)) *
        E ($ᵗ (BitVec (msgBits+n) → BitVec hashBits)) (fun g =>
          E (actualSignedPrefix n decode tier m k post ⟨msgBits+n,m'++u⟩
            ((lengthSlice (msgBits+n)).preload c g))
            (fun r => if r.1 = some (v,i) ∧ event r.2 then 1 else 0)) := by
  have hpoint (g : BitVec (msgBits+n) → BitVec hashBits) :=
    other_row_class_bound n decode tier m k (cachedRow n m c g)
      ((lengthSlice (msgBits+n)).preload c g) (length_preload_row n m c g)
      post ⟨msgBits+n,m'++u⟩ (different_message_rows n m m' hmm u) v i event
  have h := E_mono ($ᵗ (BitVec (msgBits+n) → BitVec hashBits)) hpoint
  rw [E_left_mul] at h
  have hn := E_resampledQueryPrefix n decode tier m k post (m'++u) c hc
    (fun y r => if decode y = some i ∧ r.1 = some (v,i) ∧ event r.2 then 1 else 0)
  have hd := E_resampledQueryPrefix n decode tier m k post (m'++u) c hc
    (fun _ r => if r.1 = some (v,i) ∧ event r.2 then 1 else 0)
  rw [hn, hd] at h
  exact h

#print axioms other_row_class_bound
#print axioms eager_cross_row_class_bound

end
end WeightedReplacement
