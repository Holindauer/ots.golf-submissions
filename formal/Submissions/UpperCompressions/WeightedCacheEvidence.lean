import Submissions.UpperCompressions.FiniteCacheCounts
noncomputable section
namespace WeightedCacheEvidence
open WeightedCacheCounts
open scoped Classical
variable {Q W I : Type} [DecidableEq Q] [Fintype I] [DecidableEq I]

def classSet (A : Finset Q) (c : Q → Option W) (decode : W → Option I) (i : I) : Finset Q :=
  (seen A c).filter (fun q => (c q).bind decode=some i)

theorem mem (A : Finset Q) (c : Q → Option W) (decode : W → Option I) (i : I)
    (q : Q) (hq : q∈A) (y : W) (hc : c q=some y) (hi : decode y=some i) :
    q∈classSet A c decode i := by
  apply Finset.mem_filter.mpr
  constructor
  · exact Finset.mem_filter.mpr ⟨hq,by simp only [hc,Option.isSome_some]⟩
  · simp only [hc,Option.bind_some,hi]

theorem one (A : Finset Q) (c : Q → Option W) (decode : W → Option I) (i : I)
    (q : Q) (hq : q∈A) (y : W) (hc : c q=some y) (hi : decode y=some i) :
    1≤classCounts A c decode i := by
  exact Finset.one_le_card.mpr ⟨q,mem A c decode i q hq y hc hi⟩

theorem two (A : Finset Q) (c : Q → Option W) (decode : W → Option I) (i : I)
    (q q' : Q) (hne : q≠q') (hq : q∈A) (hq' : q'∈A)
    (y y' : W) (hc : c q=some y) (hc' : c q'=some y')
    (hi : decode y=some i) (hi' : decode y'=some i) : 2≤classCounts A c decode i := by
  have hs : ({q,q'} : Finset Q) ⊆ classSet A c decode i := by
    intro z hz
    have hz' : z=q ∨ z=q' := by simpa only [Finset.mem_insert,Finset.mem_singleton] using hz
    rcases hz' with hz | hz
    · rw [hz]
      exact mem A c decode i q hq y hc hi
    · rw [hz]
      exact mem A c decode i q' hq' y' hc' hi'
  have h := Finset.card_le_card hs
  have hn : q ∉ ({q'} : Finset Q) := by simpa only [Finset.mem_singleton] using hne
  have hcard : ({q,q'} : Finset Q).card=2 := by
    rw [Finset.card_insert_of_notMem hn,Finset.card_singleton]
  rw [hcard] at h
  exact h
#print axioms one
#print axioms two
end WeightedCacheEvidence
