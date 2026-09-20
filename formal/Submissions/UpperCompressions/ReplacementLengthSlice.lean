import Submissions.UpperCompressions.ReplacementPreload

/-! Concrete eager preloading of exactly one hash-input length. Length 342 is the
256-bit message plus 86-bit nonce domain. Other lengths keep the original cache. -/

open OracleSpec OracleComp OracleComp.EvalDist ENNReal
open OptimalOTS

namespace WeightedReplacement

noncomputable section
open scoped Classical
local instance stagedLocal_ReplacementLengthSlice_1 {α : Type*} : DecidableEq α := Classical.decEq α

def queryAtLength (b : ℕ) (q : Query) : Option (BitVec b) :=
  if h : q.1 = b then some (h ▸ q.2) else none

theorem queryAtLength_mk (b : ℕ) (x : BitVec b) :
    queryAtLength b ⟨b,x⟩ = some x := by simp [queryAtLength]

theorem queryAtLength_eq_some_iff (b : ℕ) (q : Query) (x : BitVec b) :
    queryAtLength b q = some x ↔ q = ⟨b,x⟩ := by
  constructor
  · intro hq
    rcases q with ⟨n,y⟩
    by_cases hn : n = b
    · subst n
      have hy : y = x := by simpa [queryAtLength] using hq
      subst y
      rfl
    · simp [queryAtLength, hn] at hq
  · rintro rfl
    exact queryAtLength_mk b x

def lengthSlice (b : ℕ) : QuerySlice (BitVec b) where
  locate := queryAtLength b
  unique := by
    intro q q' x hq hq'
    exact ((queryAtLength_eq_some_iff b q x).mp hq).trans
      ((queryAtLength_eq_some_iff b q' x).mp hq').symm

theorem lengthSlice_outside (b : ℕ) (g : BitVec b → BitVec hashBits)
    (q : Query) (hq : q.1 ≠ b) : (lengthSlice b).tableCache g q = none := by
  simp [QuerySlice.tableCache, lengthSlice, queryAtLength, hq]

theorem lengthSlice_inside (b : ℕ) (g : BitVec b → BitVec hashBits) (x : BitVec b) :
    (lengthSlice b).tableCache g ⟨b,x⟩ = some (g x) := by
  simp [QuerySlice.tableCache, lengthSlice, queryAtLength]

theorem outE_length_preload {α : Type} (b : ℕ) (oa : OracleComp Spec α)
    (c : Cache) (f : α → ℝ≥0∞) :
    outE oa c f = E ($ᵗ (BitVec b → BitVec hashBits))
      (fun g => outE oa ((lengthSlice b).preload c g) f) :=
  outE_finite_preload (lengthSlice b) oa c f

/-- Exact full 342-bit index-table averaging in the original shared random oracle. -/
theorem outE_index342_preload {α : Type} (oa : OracleComp Spec α)
    (c : Cache) (f : α → ℝ≥0∞) :
    outE oa c f = E ($ᵗ (BitVec 342 → BitVec hashBits))
      (fun g => outE oa ((lengthSlice 342).preload c g) f) :=
  outE_length_preload 342 oa c f

/-- Even after eager preloading, all other input lengths keep their exact cache entries. -/
theorem preload_index342_outside (c : Cache) (g : BitVec 342 → BitVec hashBits)
    (q : Query) (hq : q.1 ≠ 342) : (lengthSlice 342).preload c g q = c q := by
  apply QuerySlice.preload_outside
  simp [lengthSlice, queryAtLength, hq]

#print axioms outE_length_preload
#print axioms outE_index342_preload
#print axioms preload_index342_outside

end
end WeightedReplacement
