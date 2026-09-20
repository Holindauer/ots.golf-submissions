import Submissions.UpperCompressions.WideIndexDomains

/-! Physical relations between row and global multiplicities in the actual cache. -/
noncomputable section
open scoped Classical

namespace WeightedCacheCounts
variable {D B ι : Type} [DecidableEq D] [Fintype ι] [DecidableEq ι]

theorem classCounts_mono {A G : Finset D} (hAG : A ⊆ G)
    (cache : D → Option B) (decode : B → Option ι) (i : ι) :
    classCounts A cache decode i ≤ classCounts G cache decode i := by
  apply Finset.card_le_card
  intro q hq
  obtain ⟨hqA, hi⟩ := Finset.mem_filter.mp hq
  obtain ⟨hqA, hc⟩ := Finset.mem_filter.mp hqA
  exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hAG hqA, hc⟩, hi⟩

theorem fresh_seen_succ_le (A : Finset D) (cache : D → Option B)
    (q : D) (u : B) (hq : q ∈ A) (hc : cache q = none) :
    (seen A cache).card + 1 ≤ A.card := by
  rw [← seen_card_update A cache q u hq hc]
  exact seen_card_le _ _

end WeightedCacheCounts

namespace OptimalOTS.WeightedConstruction.WideDomains
open WeightedCacheCounts

theorem row_class_le_global (m : Message) (c : hashSpec.QueryCache)
    (i : Fin WeightedSchedule.M) :
    classCounts (rowDomain m) c WeightedSchedule.decode i ≤
      classCounts indexDomain c WeightedSchedule.decode i :=
  classCounts_mono (row_subset m) c WeightedSchedule.decode i

theorem fresh_row_succ_bound (m : Message) (c : hashSpec.QueryCache)
    (q : Query) (hq : q ∈ rowDomain m) (hc : c q = none) :
    (seen (rowDomain m) c).card + 1 ≤ 2^86 :=
  (fresh_seen_succ_le (rowDomain m) c q (0 : BitVec hashBits) hq hc).trans_eq
    (row_card m)

#print axioms row_class_le_global
#print axioms fresh_row_succ_bound
end OptimalOTS.WeightedConstruction.WideDomains
