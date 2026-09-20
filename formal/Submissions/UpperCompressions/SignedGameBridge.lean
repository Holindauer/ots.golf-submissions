import Submissions.UpperCompressions.AuthPreSignExpected
import Submissions.UpperCompressions.ExpectedSigningCharge
import Submissions.UpperCompressions.ReplacementConcreteRate
import Submissions.UpperCompressions.WidePublicForgery

/-! Concrete successful-signature bridge: the retained actual forged input is
either an old public-cache replay or an eligible fresh target. The fresh target
is fed to the checked all-L posterior/public-query theorem on the same cache. -/
open OracleSpec OracleComp OracleComp.EvalDist ENNReal
noncomputable section
open scoped Classical
set_option maxRecDepth 10000
namespace OptimalOTS.WeightedConstruction.WideForest
open OptimalOTS.Dag Name WeightedReplacement WeightedSampling
set_option maxHeartbeats 1000000
attribute [local irreducible] Finset.univ Finset.filter

def signatureFromWinner (ξ : Rec) (s : Option (Winner 86 WeightedSchedule.M)) :
    Option WeightedScheme.Signature :=
  s.map fun r => (r.1, revealed (setsName r.2) ξ)

def forgedInput (z : Message × WeightedScheme.Signature) : EncInput := (z.1,z.2.1)

theorem fExp_indexLength_none (A? : Option (Finset Name)) (ξ : Rec)
    (q : Query) (hq : q.1 = msgBits+86) : fExp A? ξ q = none := by
  have hk : kc ξ q = none := by
    cases hc : kc ξ q with
    | none => rfl
    | some u =>
      obtain ⟨h,p,hp,he,_⟩ := (kc_apply_iff ξ q u).mp hc
      exact False.elim (len_hashParent_ne_enc hp ((congrArg Sigma.fst he).symm.trans hq))
  unfold fExp
  split_ifs
  · exact hk
  · rfl

/-- This adapter supplies the concrete forge/verify/strong-check continuation
to FreshOverlay. The actual query-prefix, graph exposure, and positive weak-rank
mass premises are all discharged. -/
theorem concrete_fresh_overlay (A : forestScheme.toAlgorithm.Adversary)
    (ξ : Rec) (m : Message) (st : A.State) (c : Cache) (k : ℕ)
    (v : Nonce 86) (i : Fin WeightedSchedule.M) :
    E ($ᵗ (BitVec (msgBits+86) → BitVec hashBits)) (fun g =>
      signedChosen (exposeCache (run (loop 86 WeightedSchedule.decode WeightedSchedule.tier m k)
        ((lengthSlice (msgBits+86)).preload c g)) (fExp (some (setsName i)) ξ))
        (fun s => A.forge st (signatureFromWinner ξ s)) forgedInput (some (v,i))
        (freshAlternative 86 c (m,v))
        (fun d => WeightedSchedule.decode (g (d.1++d.2)) = some i)) ≤
      ENNReal.ofReal (fraction (fun y => WeightedSchedule.decode y = some i) /
        fraction (weakRank WeightedSchedule.tier i ∘ WeightedSchedule.decode)) *
        E ($ᵗ (BitVec (msgBits+86) → BitVec hashBits)) (fun g =>
          signedCharge (exposeCache (run (loop 86 WeightedSchedule.decode WeightedSchedule.tier m k)
            ((lengthSlice (msgBits+86)).preload c g)) (fExp (some (setsName i)) ξ))
            (fun s => stBWithForgery A (pkOf ξ) m st (signatureFromWinner ξ s))
            (some (v,i)) (indexPaid (isIndexLength (msgBits+86)))) := by
  have h := eager_fresh_chosen_overlay_bound 86 WeightedSchedule.decode WeightedSchedule.tier m k
    c (fExp (some (setsName i)) ξ) (fExp_indexLength_none _ ξ)
    (fun s => A.forge st (signatureFromWinner ξ s))
    (fun s => verifyForgery (pkOf ξ) m (signatureFromWinner ξ s))
    forgedInput v i (concrete_weak_mass_pos i)
    (fun s z d => verifyForgery_queries_chosen (pkOf ξ) m (signatureFromWinner ξ s) z d)
  have he : (fun s => A.forge st (signatureFromWinner ξ s) >>=
      verifyForgery (pkOf ξ) m (signatureFromWinner ξ s)) =
      (fun s => stBWithForgery A (pkOf ξ) m st (signatureFromWinner ξ s)) :=
    funext fun s => (stBWithForgery_bind A (pkOf ξ) m st (signatureFromWinner ξ s)).symm
  rw [he] at h
  exact h

/-- A completed table is stable under the actual public execution. An accepted
different-input forgery therefore uses either the original public cache or a
fresh coordinate of this same completed table. -/
theorem forgery_replay_or_fresh (A : forestScheme.toAlgorithm.Adversary)
    (ξ : Rec) (i : Fin WeightedSchedule.M) (η : Nonce 86) (m : Message) (st : A.State)
    (c d : Cache) (g : BitVec (msgBits+86) → BitVec hashBits)
    (hsub : Cache.Sub ((lengthSlice (msgBits+86)).preload c g) d)
    (p : ForgeryResult × Cache)
    (hp : p ∈ support (run (stBWithForgery A (pkOf ξ) m st
      (some (η,revealed (setsName i) ξ))) d)) (hok : p.1.2.2 = true) :
    Cache.Hits p.2 (fHid (some (setsName i)) ξ) ∨ Spr p.2 ξ ∨
      AlternateClass c (m,η) i ∨
      (freshAlternative 86 c (m,η) (p.1.1,p.1.2.1.1) ∧
        WeightedSchedule.decode (g (p.1.1++p.1.2.1.1)) = some i) := by
  obtain ⟨u,hu,hs | hh | hi⟩ := stBWithForgery_index_witness A ξ i η m st d p hp hok
  · exact Or.inr (Or.inl hs)
  · exact Or.inl hh
  · have hmono := sub_of_mem_support_run _ d p hp
    let q : Query := encQuery (p.1.1,p.1.2.1.1)
    cases hc : c q with
    | some y =>
      have hpq := hmono q y (hsub q y ((lengthSlice (msgBits+86)).preload_some c g q y hc))
      have hy : y = u := Option.some.inj (hpq.symm.trans hu)
      exact Or.inr (Or.inr (Or.inl ⟨_,hi.2,y,hc,hy ▸ hi.1⟩))
    | none =>
      have hpre : (lengthSlice (msgBits+86)).preload c g q =
          some (g (p.1.1++p.1.2.1.1)) := by
        unfold QuerySlice.preload
        rw [Cache.extend_apply, hc, Option.none_or]
        exact lengthSlice_inside _ g _
      have hpq := hmono q _ (hsub q _ hpre)
      have hu' : g (p.1.1++p.1.2.1.1) = u := Option.some.inj (hpq.symm.trans hu)
      exact Or.inr (Or.inr (Or.inr ⟨⟨hc,hi.2⟩,hu' ▸ hi.1⟩))

def forgerySuccess (p : ForgeryResult × Cache) : ℝ≥0∞ := if p.1.2.2 = true then 1 else 0

/-- Hidden graph removal keeps the forged input, which is needed for the
posterior event. This is the existing checked IUB theorem on the actual program. -/
theorem graph_iub_forgery (oa : OracleComp Spec ForgeryResult) (ξ : Rec)
    (A? : Option (Finset Name)) (d d' : Cache)
    (hd' : IndexExtension d d') (hξ : ¬ Cache.Hits d (kc ξ)) :
    E (run oa (Cache.extend d' (kc ξ))) forgerySuccess ≤
      E (run oa (Cache.extend d' (fExp A? ξ)))
        (fun p => if Cache.Hits p.2 (fHid A? ξ) then 1 else forgerySuccess p) := by
  have hkc : Cache.extend d' (kc ξ) =
      Cache.extend (Cache.extend d' (fExp A? ξ)) (fHid A? ξ) := by
    rw [Cache.extend_assoc, extend_fExp_fHid]
  have hdisj : Cache.Disjoint (Cache.extend d' (fExp A? ξ)) (fHid A? ξ) := by
    intro q hq
    have hkq : (kc ξ q).isSome := by
      obtain ⟨h,p,hp,_,hqp⟩ := (fHid_isSome_iff _ ξ q).mp hq
      exact (kc_isSome_iff ξ q).mpr ⟨h,p,hp,hqp⟩
    rw [Cache.extend_apply, indexExtension_kc_none hd' hξ hkq, Option.none_or]
    exact disjoint_fExp_fHid _ ξ q hq
  rw [hkc]
  exact iub oa (fHid A? ξ) forgerySuccess
    (fun p => by unfold forgerySuccess; split_ifs <;> simp) _ hdisj

/-- Concrete game-to-events bound. Replay is measured in the original public
cache; private signer entries are part of the fresh-table term, not replay. -/
theorem signed_success_replay_fresh (A : forestScheme.toAlgorithm.Adversary)
    (ξ : Rec) (i : Fin WeightedSchedule.M) (η : Nonce 86) (m : Message) (st : A.State)
    (c d' : Cache) (g : BitVec (msgBits+86) → BitVec hashBits)
    (hd' : IndexExtension c d') (hξ : ¬ Cache.Hits c (kc ξ))
    (hsub : Cache.Sub ((lengthSlice (msgBits+86)).preload c g) d') :
    E (run (stBWithForgery A (pkOf ξ) m st (some (η,revealed (setsName i) ξ)))
      (Cache.extend d' (kc ξ))) forgerySuccess ≤
      E (run (stBWithForgery A (pkOf ξ) m st (some (η,revealed (setsName i) ξ)))
        (Cache.extend d' (fExp (some (setsName i)) ξ)))
        (fun p => ind (Cache.Hits p.2 (fHid (some (setsName i)) ξ)) + ind (Spr p.2 ξ) +
          ind (AlternateClass c (m,η) i) +
          ind (freshAlternative 86 c (m,η) (p.1.1,p.1.2.1.1) ∧
            WeightedSchedule.decode (g (p.1.1++p.1.2.1.1)) = some i)) := by
  refine (graph_iub_forgery _ ξ (some (setsName i)) c d' hd' hξ).trans ?_
  apply expectedValue_mono_of_support
  intro p hp
  by_cases hh : Cache.Hits p.2 (fHid (some (setsName i)) ξ)
  · rw [if_pos hh, ind_of hh]
    exact le_add_right (le_add_right le_self_add)
  · rw [if_neg hh]
    by_cases hok : p.1.2.2 = true
    · rw [forgerySuccess, if_pos hok]
      have hsub' : Cache.Sub ((lengthSlice (msgBits+86)).preload c g)
          (Cache.extend d' (fExp (some (setsName i)) ξ)) :=
        fun q u h => Cache.extend_apply_of_some (hsub q u h)
      rcases forgery_replay_or_fresh A ξ i η m st c _ g hsub' p hp hok with hh' | hs | ho | hf
      · exact absurd hh' hh
      · rw [ind_of hs]
        exact le_add_right (le_add_right le_add_self)
      · rw [ind_of ho]
        exact le_add_right le_add_self
      · rw [ind_of hf]
        exact le_add_self
    · rw [forgerySuccess, if_neg hok]
      exact zero_le

#print axioms concrete_fresh_overlay
#print axioms forgery_replay_or_fresh
#print axioms signed_success_replay_fresh
end OptimalOTS.WeightedConstruction.WideForest
