import Submissions.UpperCompressions.WeightedMoments
noncomputable section
open scoped Classical
namespace WeightedCacheCounts
open WeightedRow.Weights WeightedPublicCounts
variable {D B ι : Type} [DecidableEq D] [Fintype ι] [DecidableEq ι]

/-- Cached inputs inside an explicitly finite public index domain. -/
def seen (A : Finset D) (cache : D → Option B) : Finset D :=
  A.filter (fun q => (cache q).isSome)

def classCounts (A : Finset D) (cache : D → Option B) (decode : B → Option ι) : ι → ℕ :=
  counts (seen A cache) (fun q => (cache q).bind decode)

theorem not_seen_of_none (A : Finset D) (cache : D → Option B) (q : D)
    (hq : cache q = none) : q ∉ seen A cache := by simp [seen, hq]

theorem seen_update_of_mem (A : Finset D) (cache : D → Option B) (q : D) (u : B)
    (hq : q ∈ A) : seen A (Function.update cache q (some u)) = insert q (seen A cache) := by
  ext t
  by_cases ht : t = q
  · subst t; simp [seen, hq]
  · simp [seen, ht, Function.update_of_ne ht]

theorem seen_update_of_not_mem (A : Finset D) (cache : D → Option B) (q : D) (u : B)
    (hq : q ∉ A) : seen A (Function.update cache q (some u)) = seen A cache := by
  ext t
  by_cases ht : t = q
  · subst t; simp [seen, hq]
  · simp [seen, ht, Function.update_of_ne ht]

theorem decoded_update (cache : D → Option B) (decode : B → Option ι) (q : D) (u : B) :
    (fun t => (Function.update cache q (some u) t).bind decode) =
      Function.update (fun t => (cache t).bind decode) q (decode u) := by
  funext t
  by_cases ht : t = q
  · subst t; simp
  · simp [ht]

/-- A cache miss at a selected input is exactly a new decoded multiplicity. -/
theorem classCounts_update_of_mem (A : Finset D) (cache : D → Option B)
    (decode : B → Option ι) (q : D) (u : B) (hq : q ∈ A) (hfresh : cache q = none) :
    classCounts A (Function.update cache q (some u)) decode =
      advance (classCounts A cache decode) (decode u) := by
  unfold classCounts
  rw [seen_update_of_mem A cache q u hq, decoded_update]
  exact counts_insert_update _ _ q (not_seen_of_none A cache q hfresh) _

/-- Fresh queries outside the selected input domain preserve its multiplicities. -/
theorem classCounts_update_of_not_mem (A : Finset D) (cache : D → Option B)
    (decode : B → Option ι) (q : D) (u : B) (hq : q ∉ A) :
    classCounts A (Function.update cache q (some u)) decode = classCounts A cache decode := by
  unfold classCounts
  rw [seen_update_of_not_mem A cache q u hq, decoded_update]
  apply counts_update_absent
  intro h
  exact hq (Finset.mem_of_mem_filter q h)

theorem seen_card_update (A : Finset D) (cache : D → Option B) (q : D) (u : B)
    (hq : q ∈ A) (hfresh : cache q = none) :
    (seen A (Function.update cache q (some u))).card = (seen A cache).card+1 := by
  rw [seen_update_of_mem A cache q u hq,
    Finset.card_insert_of_notMem (not_seen_of_none A cache q hfresh)]

theorem seen_card_le (A : Finset D) (cache : D → Option B) : (seen A cache).card ≤ A.card :=
  Finset.card_le_card (Finset.filter_subset _ _)

#print axioms classCounts_update_of_mem
#print axioms classCounts_update_of_not_mem
#print axioms seen_card_update
#print axioms seen_card_le
end WeightedCacheCounts
