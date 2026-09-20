import OptimalOTS.Model

/-! Exact fibers of low-bit truncation, generic in both widths. These finite
bijections support different internal and public-key binding widths. -/

namespace OptimalOTS.WeightedConstruction.TruncFiber

noncomputable section
open scoped Classical

/-- Join fixed low bits with free high bits. -/
def join {n w : ℕ} (hw : w ≤ n) (a : BitVec w) (b : BitVec (n - w)) : BitVec n :=
  (b ++ a).cast (Nat.sub_add_cancel hw)

@[simp] theorem low_join {n w : ℕ} (hw : w ≤ n) (a : BitVec w)
    (b : BitVec (n - w)) : (join hw a b).setWidth w = a := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp [join, BitVec.getLsbD_append, hi]

@[simp] theorem high_join {n w : ℕ} (hw : w ≤ n) (a : BitVec w)
    (b : BitVec (n - w)) : ((join hw a b) >>> w).setWidth (n - w) = b := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hn : ¬ w + i < w := by omega
  simp [join, BitVec.getLsbD_ushiftRight,
    BitVec.getLsbD_append, hi, hn]

theorem join_high {n w : ℕ} (hw : w ≤ n) {a : BitVec w} (x : BitVec n)
    (hx : x.setWidth w = a) : join hw a ((x >>> w).setWidth (n - w)) = x := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  by_cases hl : i < w
  · have h := congrArg (fun t : BitVec w => t.getLsbD i) hx
    simpa [join, BitVec.getLsbD_append, BitVec.getLsbD_setWidth, hl] using h.symm
  · have hh : i - w < n - w := by omega
    have he : w + (i - w) = i := by omega
    simp [join, BitVec.getLsbD_append, BitVec.getLsbD_ushiftRight, hl, hh, he]

/-- Truncation leaves exactly the high `n-w` bits free. -/
def fiberEquiv {n w : ℕ} (hw : w ≤ n) (a : BitVec w) :
    {x : BitVec n // x.setWidth w = a} ≃ BitVec (n - w) where
  toFun x := (x.val >>> w).setWidth (n - w)
  invFun b := ⟨join hw a b, low_join hw a b⟩
  left_inv x := Subtype.ext (join_high hw x.val x.property)
  right_inv b := high_join hw a b

theorem card_filter_setWidth {n w : ℕ} (hw : w ≤ n) (a : BitVec w) :
    (Finset.univ.filter fun x : BitVec n => x.setWidth w = a).card = 2 ^ (n - w) := by
  rw [← Fintype.card_subtype, Fintype.card_congr (fiberEquiv hw a), Fintype.card_bitVec]

theorem card_filter_setWidth_le {n w : ℕ} (hw : w ≤ n) (a : BitVec w) :
    (Finset.univ.filter fun x : BitVec n => x.setWidth w = a).card ≤ 2 ^ (n - w) :=
  le_of_eq (card_filter_setWidth hw a)

theorem card_256_128 (a : BitVec 128) :
    (Finset.univ.filter fun x : BitVec 256 => x.setWidth 128 = a).card = 2 ^ 128 :=
  card_filter_setWidth (by omega) a

theorem card_256_129 (a : BitVec 129) :
    (Finset.univ.filter fun x : BitVec 256 => x.setWidth 129 = a).card = 2 ^ 127 :=
  card_filter_setWidth (by omega) a

end
end OptimalOTS.WeightedConstruction.TruncFiber

#print axioms OptimalOTS.WeightedConstruction.TruncFiber.fiberEquiv
#print axioms OptimalOTS.WeightedConstruction.TruncFiber.card_filter_setWidth
#print axioms OptimalOTS.WeightedConstruction.TruncFiber.card_256_128
#print axioms OptimalOTS.WeightedConstruction.TruncFiber.card_256_129
