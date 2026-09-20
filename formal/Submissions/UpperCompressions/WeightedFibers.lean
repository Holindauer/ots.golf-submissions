import Submissions.UpperCompressions.WeightedSchedule

/-! Exact mixed72 decoder fibers, lifted from raw129 aliases to full256 oracle
answers. These are distributional counts, not adaptive security theorems. -/

namespace OptimalOTS.WeightedConstruction.WeightedSchedule
noncomputable section
open scoped Classical
attribute [local irreducible] WeightedResearch92.tierClasses WeightedResearch92.classes WeightedResearch92.acceptedAliases

/-- Every predicate on low bits leaves all high bits free. -/
def truncPredicateEquiv {n w : ℕ} (hw : w ≤ n) (p : BitVec w → Prop) :
    {x : BitVec n // p (x.setWidth w)} ≃ {x : BitVec w // p x} × BitVec (n-w) where
  toFun x := (⟨x.val.setWidth w, x.property⟩, (x.val >>> w).setWidth (n-w))
  invFun a := ⟨TruncFiber.join hw a.1.val a.2, by simpa using a.1.property⟩
  left_inv x := Subtype.ext (TruncFiber.join_high hw x.val rfl)
  right_inv a := by
    apply Prod.ext
    · exact Subtype.ext (TruncFiber.low_join hw a.1.val a.2)
    · exact TruncFiber.high_join hw a.1.val a.2

theorem card_truncPredicate {n w : ℕ} (hw : w ≤ n) (p : BitVec w → Prop) [dp : DecidablePred p] :
    (@Finset.filter (BitVec n) (fun x => p (x.setWidth w))
      (fun x => dp (x.setWidth w)) Finset.univ).card =
      (@Finset.filter (BitVec w) p dp Finset.univ).card * 2^(n-w) := by
  rw [← Fintype.card_subtype, Fintype.card_congr (truncPredicateEquiv hw p),
    Fintype.card_prod, Fintype.card_subtype, Fintype.card_bitVec]

theorem decodeRaw_eq_some (x : BitVec 129) (i : Fin M) :
    decodeRaw x = some i ↔ rawClass x = some (classEquiv.symm i) := by
  rw [decodeRaw, Option.map_eq_some_iff]
  constructor
  · rintro ⟨c, hc, hi⟩
    have he : c = classEquiv.symm i := by
      apply classEquiv.injective
      simpa using hi
    simpa [he] using hc
  · intro h
    exact ⟨classEquiv.symm i, h, classEquiv.apply_symm_apply i⟩

theorem decodeRaw_fiber (i : Fin M) :
    (Finset.univ.filter fun x : BitVec 129 => decodeRaw x = some i).card = 2^(tier i+1) := by
  have he : (Finset.univ.filter fun x : BitVec 129 => decodeRaw x = some i) =
      Finset.univ.filter fun x : BitVec 129 => rawClass x = some (classEquiv.symm i) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, decodeRaw_eq_some]
  rw [he, rawClass_fiber]
  rfl

/-- A raw decoder fiber for any projection of aliases. -/
def rawMapFiberEquiv {β : Type} (f : Alias → β) (b : β) :
    {x : BitVec 129 // (rawAlias x).map f = some b} ≃ {a : Alias // f a = b} :=
  (Equiv.ofBijective
    (fun a : {a : Alias // f a = b} =>
      (⟨aliasRaw a.val, by simp [a.property]⟩ :
        {x : BitVec 129 // (rawAlias x).map f = some b}))
    (by
      constructor
      · intro a c h
        apply Subtype.ext
        have he := congrArg (fun x : {x : BitVec 129 // (rawAlias x).map f = some b} =>
          rawAlias x.val) h
        simpa using he
      · intro x
        have hx := x.property
        rw [Option.map_eq_some_iff] at hx
        obtain ⟨a, ha, hb⟩ := hx
        exact ⟨⟨a, hb⟩, Subtype.ext (aliasRaw_of_rawAlias ha)⟩)).symm

def aliasTierFiberEquiv (j : Tier) :
    {a : Alias // a.1.1 = j} ≃ Fin (population j) × Fin (2^(j.val+1)) where
  toFun a := by
    rcases a with ⟨⟨⟨j', k⟩, r⟩, h⟩
    cases h
    exact (k, r)
  invFun a := ⟨⟨⟨j, a.1⟩, a.2⟩, rfl⟩
  left_inv := by rintro ⟨⟨⟨j', k⟩, r⟩, h⟩; cases h; rfl
  right_inv a := by cases a; rfl

def rawTier (x : BitVec 129) : Option Tier := (rawAlias x).map fun a => a.1.1

theorem rawTier_fiber (j : Tier) :
    (Finset.univ.filter fun x : BitVec 129 => rawTier x = some j).card =
      population j * 2^(j.val+1) := by
  change (Finset.univ.filter fun x : BitVec 129 =>
    (rawAlias x).map (fun a => a.1.1) = some j).card = _
  rw [← Fintype.card_subtype,
    Fintype.card_congr (rawMapFiberEquiv (fun a => a.1.1) j),
    Fintype.card_congr (aliasTierFiberEquiv j), Fintype.card_prod,
    Fintype.card_fin, Fintype.card_fin]

def acceptedEquiv : {x : BitVec 129 // (rawAlias x).isSome} ≃ Alias :=
  (Equiv.ofBijective
    (fun a : Alias => (⟨aliasRaw a, by simp⟩ : {x : BitVec 129 // (rawAlias x).isSome}))
    (by
      constructor
      · intro a b h
        have he := congrArg (fun x : {x : BitVec 129 // (rawAlias x).isSome} => rawAlias x.val) h
        simpa using he
      · intro x
        obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp x.property
        exact ⟨a, Subtype.ext (aliasRaw_of_rawAlias ha)⟩)).symm

theorem accepted_raw_count :
    (Finset.univ.filter fun x : BitVec 129 => (rawAlias x).isSome).card = A := by
  rw [← Fintype.card_subtype, Fintype.card_congr acceptedEquiv, card_alias]

theorem decodeRaw_isSome (x : BitVec 129) : (decodeRaw x).isSome = (rawAlias x).isSome := by
  simp [decodeRaw, rawClass]

theorem accepted_decodeRaw_count :
    (Finset.univ.filter fun x : BitVec 129 => (decodeRaw x).isSome).card = A := by
  simp only [decodeRaw_isSome]
  exact accepted_raw_count

/-- Every early tier has mass19/2^24, and the final tier has mass91/2^24. -/
theorem tier_alias_count (j : Tier) : population j * 2^(j.val+1) =
    (if j.val < 71 then 19 else 91) * 2^105 := by
  by_cases h : j.val < 71
  · change WeightedResearch92.tierClasses j.val * 2^(j.val+1) = _
    rw [WeightedResearch92.tierClasses, if_pos h, if_pos h, Nat.mul_assoc, ← pow_add]
    have he : 104 - j.val + (j.val+1) = 105 := by omega
    rw [he]
  · have hj : j.val = 71 := by have := j.isLt; omega
    norm_num [population, WeightedResearch92.tierClasses, hj]

theorem rawTier_fiber_exact (j : Tier) :
    (Finset.univ.filter fun x : BitVec 129 => rawTier x = some j).card =
      (if j.val < 71 then 19 else 91) * 2^105 := by
  rw [rawTier_fiber, tier_alias_count]


end
end OptimalOTS.WeightedConstruction.WeightedSchedule

#print axioms OptimalOTS.WeightedConstruction.WeightedSchedule.decodeRaw_fiber
#print axioms OptimalOTS.WeightedConstruction.WeightedSchedule.rawTier_fiber

