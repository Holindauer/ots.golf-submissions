import Submissions.UpperCompressions.AlgorithmCosts
import Submissions.UpperCompressions.Cache
import Submissions.UpperCompressions.KeygenSupport

/-! First-minimum selection with replacement. This is an executable oracle program
and basic structural/resource lemmas, not a security certificate. All trials run;
equal tiers retain their first occurrence. -/

open OracleSpec OracleComp ENNReal
noncomputable section
open scoped Classical

namespace OptimalOTS.WeightedSampling

variable {α : Type}

/-- Choose the lower rank; in a tie the left (earlier) value wins. -/
def best (rank : α → ℕ) : Option α → Option α → Option α
  | none, b => b
  | some a, none => some a
  | some a, some b => if rank a ≤ rank b then some a else some b

@[simp] theorem best_none_left (rank : α → ℕ) (b : Option α) :
    best rank none b = b := rfl

@[simp] theorem best_none_right (rank : α → ℕ) (a : Option α) :
    best rank a none = a := by cases a <;> rfl

theorem best_some_source (rank : α → ℕ) (a b : Option α) (v : α)
    (h : best rank a b = some v) : a = some v ∨ b = some v := by
  cases a with
  | none => exact Or.inr h
  | some a =>
    cases b with
    | none => exact Or.inl h
    | some b =>
      simp only [best] at h
      split_ifs at h <;> simp_all

theorem best_eq_none (rank : α → ℕ) (a b : Option α) :
    best rank a b = none ↔ a = none ∧ b = none := by
  cases a <;> cases b <;> simp [best]
  split_ifs <;> simp

/-- Process the whole list; recursive unwinding keeps the earliest minimum. -/
def select (rank : α → ℕ) : List (Option α) → Option α
  | [] => none
  | a :: xs => best rank a (select rank xs)

theorem select_source (rank : α → ℕ) (xs : List (Option α)) (v : α)
    (h : select rank xs = some v) : some v ∈ xs := by
  induction xs with
  | nil => simp [select] at h
  | cons a xs ih =>
    rcases best_some_source rank a (select rank xs) v h with ha | ht
    · exact List.mem_cons.mpr (Or.inl ha.symm)
    · exact List.mem_cons.mpr (Or.inr (ih ht))

theorem select_none_iff (rank : α → ℕ) (xs : List (Option α)) :
    select rank xs = none ↔ ∀ a ∈ xs, a = none := by
  induction xs with
  | nil => simp [select]
  | cons a xs ih => simp only [select, best_eq_none, ih, List.forall_mem_cons]

theorem select_rank_le (rank : α → ℕ) (xs : List (Option α)) (v : α)
    (h : select rank xs = some v) :
    ∀ a, some a ∈ xs → rank v ≤ rank a := by
  induction xs generalizing v with
  | nil => simp [select] at h
  | cons b xs ih =>
    intro a ha
    rcases ht : select rank xs with _ | t
    · have hb : b = some v := by simpa [select, ht] using h
      rcases List.mem_cons.mp ha with ha | ha
      · rw [hb] at ha
        cases Option.some.inj ha
        exact le_rfl
      · have hn := (select_none_iff rank xs).mp ht _ ha
        cases hn
    · cases b with
      | none =>
        have hv : t = v := Option.some.inj (by simpa [select, ht] using h)
        subst v
        exact ih t ht a (by simpa using ha)
      | some b =>
        by_cases hb : rank b ≤ rank t
        · have hv : b = v := Option.some.inj (by simpa [select, best, ht, hb] using h)
          subst v
          rcases List.mem_cons.mp ha with ha | ha
          · cases Option.some.inj ha
            exact le_rfl
          · exact hb.trans (ih t ht a ha)
        · have hv : t = v := Option.some.inj (by simpa [select, best, ht, hb] using h)
          subst v
          rcases List.mem_cons.mp ha with ha | ha
          · cases Option.some.inj ha
            exact (lt_of_not_ge hb).le
          · exact ih t ht a ha

/-- Adding a first occurrence whose rank is no larger than the whole suffix
retains that occurrence, including ties and duplicate nonce draws. -/
theorem select_first (rank : α → ℕ) (v : α) (xs : List (Option α))
    (h : ∀ a, some a ∈ xs → rank v ≤ rank a) :
    select rank (some v :: xs) = some v := by
  rcases ht : select rank xs with _ | t
  · simp [select, ht]
  · have hvt := h t (select_source rank xs t ht)
    simp [select, best, ht, hvt]

variable {M : ℕ}

abbrev Nonce (n : ℕ) := BitVec n
abbrev Winner (n M : ℕ) := Nonce n × Fin M

def candidate (decode : BitVec hashBits → Option (Fin M)) (η : Nonce n)
    (w : BitVec hashBits) : Option (Winner n M) :=
  (fun i => (η, i)) <$> decode w

/-- Every recursive step samples one nonce independently, pays one hash query,
then chooses the earliest minimum after completing all remaining steps. -/
def loop (n : ℕ) (decode : BitVec hashBits → Option (Fin M))
    (tier : Fin M → ℕ) (m : Message) : ℕ → OracleComp Spec (Option (Winner n M))
  | 0 => pure none
  | k + 1 => do
      let η ← sampleBits n
      let w ← hash (m ++ η)
      let rest ← loop n decode tier m k
      return best (fun r => tier r.2) (candidate decode η w) rest

open AlgorithmCosts

theorem costAtMost_loop (n : ℕ) (decode : BitVec hashBits → Option (Fin M))
    (tier : Fin M → ℕ) (m : Message) (hc : blockCost (msgBits + n) = 1) :
    ∀ k, CostAtMost (loop n decode tier m k) k
  | 0 => costAtMost_pure _ _
  | k + 1 => by
    rw [loop]
    refine CostAtMost.bind_le (costAtMost_liftM_probComp _ 0) (b₂ := k+1)
      (fun η => ?_) (by omega)
    refine CostAtMost.bind_le (costAtMost_hash _ hc.le) (b₂ := k)
      (fun w => ?_) (by omega)
    exact CostAtMost.bind_le (costAtMost_loop n decode tier m hc k)
      (fun _ => costAtMost_pure _ 0) (by simp)

theorem index86_cost : blockCost (msgBits + 86) = 1 := by
  norm_num [blockCost, msgBits, blockBits]

theorem costAtMost_loop86 (decode : BitVec hashBits → Option (Fin M))
    (tier : Fin M → ℕ) (m : Message) :
    CostAtMost (loop 86 decode tier m signBudget) signBudget :=
  costAtMost_loop 86 decode tier m index86_cost signBudget

theorem run_loop_succ (n : ℕ) (decode : BitVec hashBits → Option (Fin M))
    (tier : Fin M → ℕ) (m : Message) (k : ℕ) (c : Cache) :
    run (loop n decode tier m (k+1)) c =
      ($ᵗ BitVec n : ProbComp (BitVec n)) >>= fun η =>
      run (hash (m ++ η)) c >>= fun q =>
      run (loop n decode tier m k) q.2 >>= fun r =>
      pure (best (fun s => tier s.2) (candidate decode η q.1) r.1, r.2) := by
  simp only [loop, run_bind, sampleBits, run_liftM, map_eq_bind_pure_comp,
    Function.comp_def, bind_assoc, pure_bind, run_pure]

/-- A returned nonce/class agrees with the actual shared-oracle cache. -/
theorem loop_support (n : ℕ) (decode : BitVec hashBits → Option (Fin M))
    (tier : Fin M → ℕ) (m : Message) :
    ∀ k c p, p ∈ support (run (loop n decode tier m k) c) →
      Cache.Sub c p.2 ∧
      (∀ η i, p.1 = some (η,i) →
        ∃ w, p.2 ⟨msgBits+n, m ++ η⟩ = some w ∧ decode w = some i) := by
  intro k
  induction k with
  | zero =>
    intro c p hp
    rw [loop, run_pure, support_pure, Set.mem_singleton_iff] at hp
    subst p
    exact ⟨Cache.Sub.refl c, fun η i h => by cases h⟩
  | succ k ih =>
    intro c p hp
    rw [run_loop_succ, support_bind] at hp
    simp only [Set.mem_iUnion] at hp
    obtain ⟨η, _, hp⟩ := hp
    rw [support_bind] at hp
    simp only [Set.mem_iUnion] at hp
    obtain ⟨⟨w,d⟩, hd, hp⟩ := hp
    rw [support_bind] at hp
    simp only [Set.mem_iUnion] at hp
    obtain ⟨⟨r,e⟩, hr, hp⟩ := hp
    rw [support_pure, Set.mem_singleton_iff] at hp
    subst p
    obtain ⟨hcd, hwd⟩ := Dag.Graph.hash_support (m ++ η) c (w,d) hd
    obtain ⟨hde, hret⟩ := ih d (r,e) hr
    refine ⟨hcd.trans hde, ?_⟩
    intro ζ i hi
    rcases best_some_source (fun s : Winner n M => tier s.2)
      (candidate decode η w) r (ζ,i) hi with hf | ht
    · cases hw : decode w with
      | none => simp [candidate, hw] at hf
      | some j =>
        simp only [candidate, hw, Functor.map, Option.map, Option.some.injEq,
          Prod.mk.injEq] at hf
        obtain ⟨rfl,rfl⟩ := hf
        exact ⟨w, hde _ _ hwd, hw⟩
    · exact hret ζ i ht

theorem run_hash_extend {b : ℕ} (u : BitVec b) (c f : Cache)
    (hf : f ⟨b,u⟩ = none) :
    run (hash u) (Cache.extend c f) =
      (fun p => (p.1, Cache.extend p.2 f)) <$> run (hash u) c := by
  unfold hash run
  rw [simulateQ_spec_query]
  rcases hc : c ⟨b,u⟩ with _ | w
  · have he : Cache.extend c f ⟨b,u⟩ = none := by
      rw [Cache.extend_apply_of_none hc, hf]
    rw [oracleImpl_run_inr_none hc, oracleImpl_run_inr_none he]
    simp only [map_bind, map_pure]
    exact bind_congr fun w => congrArg pure (congrArg (w, ·)
      (Cache.extend_cacheQuery c f ⟨b,u⟩ w).symm)
  · have he := Cache.extend_apply_of_some (f := f) hc
    rw [oracleImpl_run_inr_some hc, oracleImpl_run_inr_some he]
    rfl

/-- Graph caches are irrelevant when their input lengths differ from the
message/nonce input. No early-exit rejection assumption is used. -/
theorem run_loop_extend (n : ℕ) (decode : BitVec hashBits → Option (Fin M))
    (tier : Fin M → ℕ) (m : Message) (f : Cache)
    (hf : ∀ η : Nonce n, f ⟨msgBits+n,m++η⟩ = none) :
    ∀ k c, run (loop n decode tier m k) (Cache.extend c f) =
      (fun p => (p.1, Cache.extend p.2 f)) <$> run (loop n decode tier m k) c := by
  intro k
  induction k with
  | zero => intro c; simp [loop, run_pure]
  | succ k ih =>
    intro c
    rw [run_loop_succ, run_loop_succ, map_bind]
    refine bind_congr fun η => ?_
    rw [run_hash_extend _ c f (hf η)]
    simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
    refine bind_congr fun q => ?_
    rw [ih]
    simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]

/-- The actual private randomness: independent uniform nonce draws, with repeats. -/
def drawList (n : ℕ) : ℕ → ProbComp (List (Nonce n))
  | 0 => pure []
  | k+1 => do
      let η ← ($ᵗ BitVec n : ProbComp (BitVec n))
      let xs ← drawList n k
      return η :: xs

theorem run_hash_cached {b : ℕ} (u : BitVec b) (c : Cache) (w : BitVec hashBits)
    (h : c ⟨b,u⟩ = some w) : run (hash u) c = pure (w,c) := by
  unfold hash run
  rw [simulateQ_spec_query]
  exact oracleImpl_run_inr_some h

/-- For a fixed complete oracle row, the executable loop is precisely iid nonce
sampling followed by the first-minimum selector. The shared cache is unchanged.
This does not assert that a lazy row has an unconditional independent posterior. -/
theorem run_loop_fixed_row (n : ℕ) (decode : BitVec hashBits → Option (Fin M))
    (tier : Fin M → ℕ) (m : Message) (table : Nonce n → BitVec hashBits) (c : Cache)
    (hc : ∀ η, c ⟨msgBits+n,m++η⟩ = some (table η)) :
    ∀ k, run (loop n decode tier m k) c =
      (fun xs => (select (fun r : Winner n M => tier r.2)
        (xs.map fun η => candidate decode η (table η)), c)) <$> drawList n k := by
  intro k
  induction k with
  | zero => simp [loop, drawList, select, run_pure]
  | succ k ih =>
    rw [run_loop_succ, drawList, map_bind]
    refine bind_congr fun η => ?_
    rw [run_hash_cached _ c (table η) (hc η), pure_bind, ih]
    simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind,
      List.map_cons, select]

#print axioms run_loop_fixed_row

#print axioms loop_support
#print axioms run_loop_extend

#print axioms select_source
#print axioms select_none_iff
#print axioms select_rank_le
#print axioms select_first
#print axioms costAtMost_loop86

end OptimalOTS.WeightedSampling
