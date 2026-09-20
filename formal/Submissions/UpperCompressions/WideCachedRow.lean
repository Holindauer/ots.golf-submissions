import Submissions.UpperCompressions.WideEmpiricalBounds
import Submissions.UpperCompressions.WeightedProgramPayoff
import Submissions.UpperCompressions.ReplacementEagerPrefix

/-! The actual pre-sign cache, viewed as a partially exposed nonce row. -/
noncomputable section
namespace WeightedCacheCounts
open scoped Classical
variable {D Q W I : Type} [Fintype D] [DecidableEq D] [DecidableEq Q]
  [Fintype I] [DecidableEq I]

theorem seen_image (e : D → Q) (c : Q → Option W) :
    seen (Finset.univ.image e) c = (Finset.univ.filter (fun a => (c (e a)).isSome)).image e := by
  ext q
  simp only [seen,Finset.mem_filter,Finset.mem_image,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨⟨a,rfl⟩,ha⟩
    exact ⟨a,ha,rfl⟩
  · rintro ⟨a,ha,rfl⟩
    exact ⟨⟨a,rfl⟩,ha⟩

theorem seen_image_card (e : D → Q) (he : Function.Injective e) (c : Q → Option W) :
    (seen (Finset.univ.image e) c).card=(Finset.univ.filter (fun a => (c (e a)).isSome)).card := by
  rw [seen_image,Finset.card_image_of_injective _ he]

theorem counts_image (e : D → Q) (he : Function.Injective e) (c : Q → Option W)
    (decode : W → Option I) :
    classCounts (Finset.univ.image e) c decode =
      WeightedCompletion.rowCount (Finset.univ.filter (fun a => (c (e a)).isSome))
        (fun a => (c (e a)).bind decode) := by
  funext i
  unfold classCounts WeightedPublicCounts.counts WeightedCompletion.rowCount
  rw [seen_image,Finset.filter_image,Finset.card_image_of_injective _ he]
end WeightedCacheCounts

namespace OptimalOTS.WeightedConstruction.WideCachedRow
open OracleSpec OracleComp OracleComp.EvalDist
open WeightedSchedule WideDomains WideForest WeightedReference WeightedConstants
open WeightedReplacement WeightedCompletion WeightedCacheCounts
open scoped Classical
attribute [local irreducible] Finset.univ Finset.filter

def exposed (m : Message) (c : Cache) : Finset (BitVec 86) :=
  Finset.univ.filter (fun η => (c (encQuery (m,η))).isSome)
def fixed (m : Message) (c : Cache) (η : BitVec 86) : Option (Fin M) :=
  (c (encQuery (m,η))).bind decode

theorem row_injective (m : Message) : Function.Injective (fun η : BitVec 86 => encQuery (m,η)) :=
  fun _ _ h => WeightedSampling.Availability.nonce_query_inj m h

theorem exposed_card (m : Message) (c : Cache) :
    (exposed m c).card=(seen (rowDomain m) c).card :=
  (seen_image_card _ (row_injective m) c).symm

theorem fixed_counts (m : Message) (c : Cache) :
    rowCount (exposed m c) (fixed m c)=classCounts (rowDomain m) c decode :=
  (counts_image _ (row_injective m) c decode).symm

theorem cached_known (m : Message) (c : Cache) (g : BitVec 342 → BitVec 256)
    (η : BitVec 86) (hη : η ∈ exposed m c) :
    decode (cachedRow 86 m c g η)=fixed m c η := by
  have hc : (c (encQuery (m,η))).isSome := (Finset.mem_filter.mp hη).2
  cases hh : c (encQuery (m,η)) with
  | none => simp [hh] at hc
  | some y =>
    change decode ((c (encQuery (m,η))).getD _)=(c (encQuery (m,η))).bind decode
    rw [hh]
    rfl

theorem cached_fresh (m : Message) (c : Cache) (g : BitVec 342 → BitVec 256)
    (η : BitVec 86) (hη : η ∉ exposed m c) :
    decode (cachedRow 86 m c g η)=decode (g (m++η)) := by
  have hc : c (encQuery (m,η))=none := by
    cases hh : c (encQuery (m,η)) with
    | none => rfl
    | some y => exact False.elim (hη (Finset.mem_filter.mpr ⟨Finset.mem_univ _,by simp [hh]⟩))
  change decode ((c (encQuery (m,η))).getD _)=_
  rw [hc]
  rfl

theorem cached_fresh_probability (m : Message) (c : Cache) (η : BitVec 86)
    (hη : η ∉ exposed m c) (i : Fin M) :
    uniformMean (fun g : BitVec 342 → BitVec 256 =>
      if decode (cachedRow 86 m c g η)=some i then 1 else 0)=classProbability i := by
  simp only [cached_fresh m c _ η hη]
  exact (uniformMean_coordinate (W:=BitVec 256) (m++η)
    (fun x => if decode x=some i then 1 else 0)).trans (uniform_decode_probability i)

theorem tableKernel_nonneg {D I : Type} [Fintype D] [Nonempty D] [DecidableEq D]
    [Fintype I] [DecidableEq I] (k : ℕ) (table : D → Option I) (tier : I → ℕ)
    (f : D → I → ℝ) (hf : ∀ a i,0 ≤ f a i) : 0 ≤ tableKernel k table tier f := by
  rw [← iid_selected_score]
  apply iidMean_nonneg
  intro xs
  cases hs : selected table tier xs with
  | none => simp [score,hs]
  | some p => simpa [score,hs] using hf p.1 p.2

/-- Exact payoff of the actual all-L signing loop, from an arbitrary real cache.
Its conditional row completion is averaged; no Good conditioning is performed. -/
theorem actual_sign_payoff (m : Message) (c : Cache) (f : BitVec 86 → Fin M → ℝ)
    (hf : ∀ a i,0 ≤ f a i) :
    outE (WeightedSampling.loop 86 decode tier m L) c
      (fun s => ENNReal.ofReal (score s (fun r => f r.1 r.2))) =
      ENNReal.ofReal (uniformMean (fun g : BitVec 342 → BitVec 256 =>
        tableKernel L (decode ∘ cachedRow 86 m c g) tier f)) := by
  rw [outE_index342_preload]
  have he (g : BitVec 342 → BitVec 256) :
      outE (WeightedSampling.loop 86 decode tier m L) ((lengthSlice 342).preload c g)
        (fun s => ENNReal.ofReal (score s (fun r => f r.1 r.2))) =
        ENNReal.ofReal (tableKernel L (decode ∘ cachedRow 86 m c g) tier f) :=
    E_loop_fixed_row_score 86 M L decode tier m (cachedRow 86 m c g)
      ((lengthSlice 342).preload c g) (length_preload_row 86 m c g) f hf
  calc
    _ = E ($ᵗ (BitVec 342 → BitVec 256)) (fun g => ENNReal.ofReal
        (tableKernel L (decode ∘ cachedRow 86 m c g) tier f)) := by
      congr 1
      funext g
      exact he g
    _ = _ := E_uniform_ofReal _ (fun g => tableKernel_nonneg L _ tier f hf)

#print axioms exposed_card
#print axioms fixed_counts
#print axioms cached_fresh_probability
#print axioms actual_sign_payoff
end OptimalOTS.WeightedConstruction.WideCachedRow
