import Submissions.UpperCompressions.TruncFiber
import Submissions.UpperCompressions.Count92

/-! The concrete mixed72 schedule. Finite equivalences are fixed deterministic
pure computation; only the random oracle supplies the distribution. -/

namespace OptimalOTS.WeightedConstruction.WeightedSchedule

noncomputable section
open scoped Classical
set_option maxHeartbeats 400000
attribute [local irreducible] WeightedResearch92.tierClasses WeightedResearch92.classes WeightedResearch92.acceptedAliases

abbrev Tier := Fin 72
abbrev population (j : Tier) := WeightedResearch92.tierClasses j.val
abbrev Class := (j : Tier) × Fin (population j)
abbrev multiplicity (c : Class) : ℕ := 2 ^ (c.1.val + 1)
abbrev Alias := (c : Class) × Fin (multiplicity c)
abbrev M := WeightedResearch92.classes
abbrev A := WeightedResearch92.acceptedAliases

theorem card_class : Fintype.card Class = M := by
  simp only [Class, Fintype.card_sigma, Fintype.card_fin]
  unfold M WeightedResearch92.classes
  exact Fin.sum_univ_eq_sum_range _ 72

theorem card_alias : Fintype.card Alias = A := by
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fin]
  change (∑ c : Class, 2 ^ (c.1.val+1)) = A
  rw [Fintype.sum_sigma]
  have hsum (j : Tier) : (∑ _k : Fin (population j), 2 ^ (j.val+1)) =
      population j * 2 ^ (j.val+1) := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  simp only [hsum]
  unfold A WeightedResearch92.acceptedAliases
  exact Fin.sum_univ_eq_sum_range (fun j => WeightedResearch92.tierClasses j * 2 ^ (j+1)) 72

def classEquiv : Class ≃ Fin M := Fintype.equivFinOfCardEq card_class
def aliasEquiv : Alias ≃ Fin A := Fintype.equivFinOfCardEq card_alias

def tier (i : Fin M) : ℕ := (classEquiv.symm i).1.val

theorem tier_lt (i : Fin M) : tier i < 72 := (classEquiv.symm i).1.isLt

theorem aliases_lt : A < 2 ^ 129 := by
  change WeightedResearch92.acceptedAliases < 2 ^ 129
  rw [WeightedResearch92.aliases_exact]
  norm_num

/-- The accepted prefix is in fixed bijection with aliases. -/
def rawAlias (x : BitVec 129) : Option Alias :=
  if h : x.toNat < A then some (aliasEquiv.symm ⟨x.toNat, h⟩) else none

def rawClass (x : BitVec 129) : Option Class := (rawAlias x).map Sigma.fst

def decodeRaw (x : BitVec 129) : Option (Fin M) := (rawClass x).map classEquiv

def decode (x : BitVec 256) : Option (Fin M) := decodeRaw (x.setWidth 129)

def aliasRaw (a : Alias) : BitVec 129 := BitVec.ofNat 129 (aliasEquiv a).val

theorem aliasRaw_toNat (a : Alias) : (aliasRaw a).toNat = (aliasEquiv a).val := by
  rw [aliasRaw, BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
  exact Nat.lt_trans (aliasEquiv a).isLt aliases_lt

@[simp] theorem rawAlias_aliasRaw (a : Alias) : rawAlias (aliasRaw a) = some a := by
  simp only [rawAlias, aliasRaw_toNat, dif_pos (aliasEquiv a).isLt]
  rw [Equiv.symm_apply_apply]

theorem aliasRaw_of_rawAlias {x : BitVec 129} {a : Alias} (h : rawAlias x = some a) :
    aliasRaw a = x := by
  unfold rawAlias at h
  split_ifs at h with hx
  · simp only [Option.some.injEq] at h
    rw [← h]
    apply BitVec.eq_of_toNat_eq
    rw [aliasRaw_toNat, Equiv.apply_symm_apply]

/-- The class fiber inside the alias type is its multiplicity coordinate. -/
def aliasFiberEquiv (c : Class) : {a : Alias // a.1 = c} ≃ Fin (multiplicity c) where
  toFun a := a.property ▸ a.val.2
  invFun b := ⟨⟨c, b⟩, rfl⟩
  left_inv := by rintro ⟨⟨d, b⟩, h⟩; cases h; rfl
  right_inv _ := rfl

/-- Decoding preserves exactly the alias fiber of each class. -/
def rawFiberEquiv (c : Class) :
    {x : BitVec 129 // rawClass x = some c} ≃ {a : Alias // a.1 = c} :=
  (Equiv.ofBijective
    (fun a : {a : Alias // a.1 = c} =>
      (⟨aliasRaw a.val, by simp [rawClass, a.property]⟩ :
        {x : BitVec 129 // rawClass x = some c}))
    (by
      constructor
      · intro a b h
        apply Subtype.ext
        have he := congrArg (fun x : {x : BitVec 129 // rawClass x = some c} =>
          rawAlias x.val) h
        simpa using he
      · intro x
        have hx := x.property
        rw [rawClass, Option.map_eq_some_iff] at hx
        obtain ⟨a, ha, hc⟩ := hx
        exact ⟨⟨a, hc⟩, Subtype.ext (aliasRaw_of_rawAlias ha)⟩)).symm

/-- Exact raw129 per-class fiber. -/
theorem rawClass_fiber (c : Class) :
    (Finset.univ.filter fun x : BitVec 129 => rawClass x = some c).card = multiplicity c := by
  rw [← Fintype.card_subtype, Fintype.card_congr (rawFiberEquiv c),
    Fintype.card_congr (aliasFiberEquiv c), Fintype.card_fin]

end
end OptimalOTS.WeightedConstruction.WeightedSchedule

#print axioms OptimalOTS.WeightedConstruction.WeightedSchedule.card_class
#print axioms OptimalOTS.WeightedConstruction.WeightedSchedule.card_alias
#print axioms OptimalOTS.WeightedConstruction.WeightedSchedule.rawClass_fiber
