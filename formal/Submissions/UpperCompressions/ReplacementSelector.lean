import Submissions.UpperCompressions.ReplacementSampling
import Submissions.UpperCompressions.WeightedSampling

/-! Bridge from the executable first-minimum selector to the exact iid finite
sampling law. Ranks may tie across arbitrary output labels; only ranks determine
priority, and nonce identity determines the target event. -/

namespace WeightedReplacement

open OptimalOTS.WeightedSampling
attribute [local instance] Classical.propDecidable

def weakRank {β : Type} (rank : β → ℕ) (v : β) : Option β → Prop
  | none => True
  | some a => rank v ≤ rank a

def strictRank {β : Type} (rank : β → ℕ) (v : β) : Option β → Prop
  | none => True
  | some a => rank v < rank a

theorem select_weakRank_iff {β : Type} (rank : β → ℕ) (v : β)
    (xs : List (Option β)) :
    weakRank rank v (select rank xs) ↔ ∀ a ∈ xs, weakRank rank v a := by
  cases hs : select rank xs with
  | none =>
    have hh := (select_none_iff rank xs).mp hs
    simp only [weakRank, true_iff]
    intro a ha
    rw [hh a ha]
    trivial
  | some w =>
    constructor
    · intro hv a ha
      cases a with
      | none => trivial
      | some a => exact hv.trans (select_rank_le rank xs w hs a ha)
    · intro hall
      exact hall (some w) (select_source rank xs w hs)

theorem best_eq_target_iff {β : Type} (rank : β → ℕ) (v : β) (a b : Option β) :
    best rank a b = some v ↔
      (a = some v ∧ weakRank rank v b) ∨ (strictRank rank v a ∧ b = some v) := by
  cases a with
  | none => simp [best, strictRank]
  | some a =>
    cases b with
    | none => simp [best, weakRank]
    | some b =>
      by_cases h : rank a ≤ rank b
      · simp only [best, if_pos h, Option.some.injEq, weakRank, strictRank]
        constructor
        · rintro rfl
          exact Or.inl ⟨rfl, h⟩
        · rintro (⟨rfl, _⟩ | ⟨hv, rfl⟩)
          · rfl
          · omega
      · simp only [best, if_neg h, Option.some.injEq, weakRank, strictRank]
        constructor
        · rintro rfl
          exact Or.inr ⟨by omega, rfl⟩
        · rintro (⟨rfl, hv⟩ | ⟨_, rfl⟩)
          · omega
          · rfl

theorem select_eq_firstMinimumEvent {β : Type} (rank : β → ℕ) (v : β)
    (xs : List (Option β)) :
    select rank xs = some v ↔
      FirstMinimumEvent (some v) (weakRank rank v) (strictRank rank v) xs := by
  induction xs with
  | nil => simp [select, firstMinimumEvent_nil]
  | cons a xs ih =>
    rw [select, best_eq_target_iff, firstMinimumEvent_cons, select_weakRank_iff, ih]

theorem firstMinimumEvent_map_iff {α β : Type*} (f : α → β) (v : α) (w : β)
    (weak strict : β → Prop) (hf : ∀ a, f a = w ↔ a = v) (xs : List α) :
    FirstMinimumEvent w weak strict (xs.map f) ↔
      FirstMinimumEvent v (weak ∘ f) (strict ∘ f) xs := by
  induction xs with
  | nil => simp [firstMinimumEvent_nil]
  | cons a xs ih =>
    simp only [List.map_cons, firstMinimumEvent_cons, hf, ih,
      List.forall_mem_map, Function.comp_apply]

/-- Exact iid probability of the executable selector returning one labeled
target. The target output must identify precisely its nonce; other outputs may
have the same tier without any restriction. -/
theorem iid_select_probability {α β : Type} [Fintype α]
    (rank : β → ℕ) (candidate : α → Option β) (v : α) (w : β)
    (hc : ∀ a, candidate a = some w ↔ a = v) (n : ℕ) :
    iidMean n (fun xs => if select rank (xs.map candidate) = some w then (1 : ℝ) else 0) =
      kernel n (fraction (weakRank rank w ∘ candidate))
        (fraction (strictRank rank w ∘ candidate)) / Fintype.card α := by
  classical
  have hev (xs : List α) : select rank (xs.map candidate) = some w ↔
      FirstMinimumEvent v (weakRank rank w ∘ candidate) (strictRank rank w ∘ candidate) xs := by
    rw [select_eq_firstMinimumEvent]
    exact firstMinimumEvent_map_iff candidate v (some w) _ _ hc xs
  have hv : ¬ (strictRank rank w ∘ candidate) v := by
    simp [Function.comp_def, (hc v).mpr rfl, strictRank]
  simp_rw [hev]
  exact iid_first_minimum_event_probability v _ _ hv n

/-- Attaching the nonce to its decoded class gives the exact label-injectivity
premise, without assuming classes or tiers distinguish nonce positions. -/
theorem tagged_candidate_target_iff {α γ : Type} (table : α → Option γ)
    (v : α) (i : γ) (hv : table v = some i) (a : α) :
    (fun j => (a,j)) <$> table a = some (v,i) ↔ a = v := by
  cases ha : table a with
  | none =>
    have hav : a ≠ v := by
      intro he
      subst a
      rw [hv] at ha
      cases ha
    simp [ha, hav]
  | some j =>
    change (some (a,j) = some (v,i)) ↔ a = v
    simp only [Option.some.injEq, Prod.mk.injEq]
    constructor
    · exact fun h => h.1
    · intro he
      subst a
      exact ⟨rfl, Option.some.inj (ha.symm.trans hv)⟩

/-- Complete finite-table theorem: a nonce has the common tier kernel divided by
the number of nonces. Tiers may have any number of classes and aliases. -/
theorem iid_tagged_table_probability {α γ : Type} [Fintype α]
    (table : α → Option γ) (tier : γ → ℕ) (v : α) (i : γ)
    (hv : table v = some i) (n : ℕ) :
    iidMean n (fun xs =>
      if select (fun p : α × γ => tier p.2)
          (xs.map fun a => (fun j => (a,j)) <$> table a) = some (v,i)
      then (1 : ℝ) else 0) =
      kernel n (fraction (weakRank tier i ∘ table))
        (fraction (strictRank tier i ∘ table)) / Fintype.card α := by
  let cand : α → Option (α × γ) := fun a => (fun j => (a,j)) <$> table a
  have hw : weakRank (fun p : α × γ => tier p.2) (v,i) ∘ cand =
      weakRank tier i ∘ table := by
    funext a
    cases ht : table a <;> simp [cand, ht, weakRank]
  have hs : strictRank (fun p : α × γ => tier p.2) (v,i) ∘ cand =
      strictRank tier i ∘ table := by
    funext a
    cases ht : table a <;> simp [cand, ht, strictRank]
  have h := iid_select_probability (fun p : α × γ => tier p.2) cand v (v,i)
    (tagged_candidate_target_iff table v i hv) n
  rw [hw, hs] at h
  convert h using 1
  congr 1
  funext xs
  dsimp only [cand]
  split_ifs <;> rfl

#print axioms select_eq_firstMinimumEvent
#print axioms firstMinimumEvent_map_iff
#print axioms iid_select_probability
#print axioms tagged_candidate_target_iff
#print axioms iid_tagged_table_probability

end WeightedReplacement
