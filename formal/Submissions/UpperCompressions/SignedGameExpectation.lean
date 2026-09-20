import Submissions.UpperCompressions.SignedGameBridge
import Submissions.UpperCompressions.ReplacementSignedBudget

/-! Actual game-to-payoff leaves and the completed-table cache invariants needed
to integrate those leaves over the real all-L signer. -/
open OracleSpec OracleComp OracleComp.EvalDist ENNReal
noncomputable section
open scoped Classical
set_option maxRecDepth 10000
namespace OptimalOTS.WeightedConstruction.WideForest
open OptimalOTS.Dag Name WeightedReplacement WeightedSampling
set_option maxHeartbeats 1000000
attribute [local irreducible] Finset.univ Finset.filter

theorem exists_encQuery_of_length (q : Query) (hq : q.1 = msgBits+86) :
    ∃ u : EncInput, q = encQuery u := by
  rcases q with ⟨n,x⟩
  dsimp only at hq
  subst n
  refine ⟨(x.extractLsb' 86 msgBits,x.extractLsb' 0 86), ?_⟩
  exact congrArg (fun y : BitVec (msgBits+86) => (⟨msgBits+86,y⟩ : Query))
    BitVec.extractLsb'_append_extractLsb'.symm

theorem indexExtension_trans {c d e : Cache} (hcd : IndexExtension c d)
    (hde : IndexExtension d e) : IndexExtension c e := by
  refine ⟨fun q u h => hde.1 q u (hcd.1 q u h), ?_⟩
  intro q u hc he
  cases hd : d q with
  | none => exact hde.2 q u hd he
  | some v => exact hcd.2 q v hc hd

theorem indexExtension_preload (c : Cache) (g : BitVec (msgBits+86) → BitVec hashBits) :
    IndexExtension c ((lengthSlice (msgBits+86)).preload c g) := by
  refine ⟨fun q u h => (lengthSlice (msgBits+86)).preload_some c g q u h, ?_⟩
  intro q u hc he
  by_cases hq : q.1 = msgBits+86
  · exact exists_encQuery_of_length q hq
  · unfold QuerySlice.preload at he
    rw [Cache.extend_apply, hc, Option.none_or, lengthSlice_outside _ g q hq] at he
    cases he

theorem loop_indexExtension {M : ℕ}
    (decode : BitVec hashBits → Option (Fin M)) (tier : Fin M → ℕ) (m : Message)
    (k : ℕ) (c : Cache) (p : Option (Winner 86 M) × Cache)
    (hp : p ∈ support (run (loop 86 decode tier m k) c)) : IndexExtension c p.2 := by
  refine ⟨sub_of_mem_support_run _ c p hp, ?_⟩
  intro q u hc he
  obtain ⟨η,hη⟩ := ReplacementLocality.loop_new_cache_row 86 decode tier m k c p hp q u hc he
  exact ⟨(m,η),hη⟩

theorem preloaded_loop_indexExtension {M : ℕ}
    (decode : BitVec hashBits → Option (Fin M)) (tier : Fin M → ℕ) (m : Message)
    (k : ℕ) (c : Cache) (g : BitVec (msgBits+86) → BitVec hashBits)
    (p : Option (Winner 86 M) × Cache)
    (hp : p ∈ support (run (loop 86 decode tier m k) ((lengthSlice (msgBits+86)).preload c g))) :
    IndexExtension c p.2 :=
  indexExtension_trans (indexExtension_preload c g) (loop_indexExtension decode tier m k _ p hp)

theorem auth_E_add {α : Type} (p : ProbComp α) (f g : α → ℝ≥0∞) :
    E p (fun x => f x+g x) = E p f+E p g := by
  simp only [E, expectedValue_def, mul_add, ENNReal.tsum_add]

/-- Verifying a forged pair keeps its chosen input unchanged. Dropping the
verification outcome converts the terminal fresh event to the exact forge
expectation used in FreshOverlay's `signedChosen`. -/
theorem terminal_chosen_le_forge (A : forestScheme.toAlgorithm.Adversary)
    (pk : PublicKey) (m : Message) (st : A.State) (σ : Option WeightedScheme.Signature)
    (c : Cache) (P : EncInput → Prop) :
    E (run (stBWithForgery A pk m st σ) c) (fun p => ind (P (p.1.1,p.1.2.1.1))) ≤
      E (run (A.forge st σ) c) (fun p => ind (P (forgedInput p.1))) := by
  rw [stBWithForgery_bind]
  dsimp only [WeightedScheme.Scheme.toAlgorithm] at A ⊢
  rw [run_bind, E_bind]
  apply E_mono
  intro p
  unfold verifyForgery
  rw [run_bind, E_bind]
  simp only [run_pure, E_pure]
  exact E_const_le _ _

/-- Pointwise actual signed-game master. Its replay and fresh payoffs are
measured before signing and before final verification respectively, and graph
costs use exactly the same reduced continuation/cache as the fresh-index cost. -/
theorem signed_game_leaf (A : forestScheme.toAlgorithm.Adversary)
    (ξ : Rec) (i : Fin WeightedSchedule.M) (η : Nonce 86) (m : Message) (st : A.State)
    (c d' : Cache) (g : BitVec (msgBits+86) → BitVec hashBits)
    (hd' : IndexExtension c d') (hξ : ¬ Cache.Hits c (kc ξ))
    (hsub : Cache.Sub ((lengthSlice (msgBits+86)).preload c g) d') :
    E (run (stBWithForgery A (pkOf ξ) m st (some (η,revealed (setsName i) ξ)))
      (Cache.extend d' (kc ξ))) forgerySuccess ≤
      E (run (stBWithForgery A (pkOf ξ) m st (some (η,revealed (setsName i) ξ)))
        (Cache.extend d' (fExp (some (setsName i)) ξ)))
        (fun p => ind (Cache.Hits p.2 (fHid (some (setsName i)) ξ))+ind (Spr p.2 ξ)) +
      ind (AlternateClass c (m,η) i) +
      E (run (A.forge st (some (η,revealed (setsName i) ξ)))
        (Cache.extend d' (fExp (some (setsName i)) ξ)))
        (fun p => ind (freshAlternative 86 c (m,η) (forgedInput p.1) ∧
          WeightedSchedule.decode (g (p.1.1++p.1.2.1)) = some i)) := by
  have h := signed_success_replay_fresh A ξ i η m st c d' g hd' hξ hsub
  rw [auth_E_add, auth_E_add] at h
  refine h.trans (add_le_add (add_le_add le_rfl (E_const_le _ _)) ?_)
  exact terminal_chosen_le_forge A (pkOf ξ) m st _ _
    (fun u => freshAlternative 86 c (m,η) u ∧ WeightedSchedule.decode (g (u.1++u.2)) = some i)

theorem retained_success_eq (A : forestScheme.toAlgorithm.Adversary)
    (pk : PublicKey) (m : Message) (st : A.State) (σ : Option WeightedScheme.Signature)
    (c : Cache) :
    E (run (stBWithForgery A pk m st σ) c) forgerySuccess =
      E (run (stB A pk m st σ) c) successValue := by
  rw [← stBWithForgery_map A pk m st σ, run_map, E_map]
  rfl

#print axioms exists_encQuery_of_length
#print axioms preloaded_loop_indexExtension
#print axioms signed_game_leaf
#print axioms retained_success_eq
end OptimalOTS.WeightedConstruction.WideForest
