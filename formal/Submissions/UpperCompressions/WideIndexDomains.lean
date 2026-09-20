import Submissions.UpperCompressions.WideDecoderLaw
import Submissions.UpperCompressions.WeightedAvailability
import Submissions.UpperCompressions.WideQuery
import Submissions.UpperCompressions.FiniteCacheCounts

/-! The concrete finite public index domain and its nonce rows. Counts are
computed from the real cache, so each row has at most2^86 distinct inputs. -/
noncomputable section
namespace OptimalOTS.WeightedConstruction.WideDomains
open scoped Classical
open WeightedCacheCounts WideForest
attribute [local irreducible] Finset.univ Finset.filter

def indexDomain : Finset Query := Finset.univ.image (fun x : BitVec 342 => (⟨342,x⟩ : Query))
def rowDomain (m : Message) : Finset Query :=
  Finset.univ.image (fun η : BitVec 86 => encQuery (m,η))

theorem mem_indexDomain (q : Query) : q ∈ indexDomain ↔ q.1=342 := by
  constructor
  · intro h
    obtain ⟨x,hx,he⟩ := Finset.mem_image.mp h
    exact (congrArg Sigma.fst he).symm
  · rcases q with ⟨n,x⟩
    intro hn
    dsimp at hn
    subst n
    exact Finset.mem_image.mpr ⟨x,Finset.mem_univ _,rfl⟩

theorem mem_rowDomain (m : Message) (q : Query) :
    q ∈ rowDomain m ↔ ∃ η : BitVec 86,encQuery (m,η)=q := by
  simp only [rowDomain,Finset.mem_image,Finset.mem_univ,true_and]

theorem row_subset (m : Message) : rowDomain m ⊆ indexDomain := by
  intro q hq
  obtain ⟨η,rfl⟩ := (mem_rowDomain m q).mp hq
  exact (mem_indexDomain _).mpr rfl

theorem row_card (m : Message) : (rowDomain m).card=2^86 := by
  unfold rowDomain
  rw [Finset.card_image_of_injective]
  · rw [Finset.card_univ,Fintype.card_bitVec]
  · intro η ζ h
    exact WeightedSampling.Availability.nonce_query_inj m h

theorem seen_row_bound (m : Message) (c : hashSpec.QueryCache) :
    (seen (rowDomain m) c).card ≤ 2^86 :=
  (seen_card_le _ _).trans_eq (row_card m)

theorem seen_row_subset (m : Message) (c : hashSpec.QueryCache) :
    seen (rowDomain m) c ⊆ seen indexDomain c := by
  intro q hq
  exact Finset.mem_filter.mpr ⟨row_subset m (Finset.mem_filter.mp hq).1,
    (Finset.mem_filter.mp hq).2⟩

theorem fresh_seen_empty (c : hashSpec.QueryCache)
    (hf : ∀ q : Query,q.1=342 → c q=none) : seen indexDomain c=∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro q hq
  have h := Finset.mem_filter.mp hq
  have hc := hf q ((mem_indexDomain q).mp h.1)
  simpa only [hc,Option.isSome_none,Bool.false_eq_true] using h.2

theorem fresh_counts_zero (c : hashSpec.QueryCache)
    (hf : ∀ q : Query,q.1=342 → c q=none) :
    classCounts indexDomain c WeightedSchedule.decode = fun _ => 0 := by
  unfold classCounts
  rw [fresh_seen_empty c hf]
  funext i
  simp [WeightedPublicCounts.counts]

#print axioms row_card
#print axioms seen_row_bound
#print axioms fresh_counts_zero
end OptimalOTS.WeightedConstruction.WideDomains
