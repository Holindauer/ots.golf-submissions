import Submissions.UpperCompressions.WideAuthPotential

/-! Uniform record-fiber coupling for arbitrary actual paid continuations.
The continuation may depend on all public disclosure data; the index potential
and its actual-law charge remain explicit hypotheses. -/
open OracleSpec OracleComp OracleComp.EvalDist ENNReal
noncomputable section
open scoped Classical
set_option maxRecDepth 10000
attribute [local irreducible] Finset.univ Finset.filter
namespace OptimalOTS.WeightedConstruction.WideForest
open OptimalOTS.Dag Name

theorem E_const_mul {α : Type} (p : ProbComp α) (c : ℝ≥0∞) (g : α → ℝ≥0∞) :
    c * E p g = E p (fun x => c * g x) := by
  rw [E, E, expectedValue_def, expectedValue_def, ← ENNReal.tsum_mul_left]
  exact tsum_congr fun x => by ring

theorem E_finsetSum {α ι : Type} (p : ProbComp α) (s : Finset ι) (g : ι → α → ℝ≥0∞) :
    E p (fun x => ∑ i ∈ s, g i x) = ∑ i ∈ s, E p (g i) :=
  expectedValue_finsetSum p s g

theorem record_regroup (T : Finset Rec) (Ac : Finset Name) (f : Rec → ℝ≥0∞) :
    (∑ ξ ∈ T, f ξ) = ∑ dt ∈ T.image (dataOf Ac), ∑ ξ ∈ T with dataOf Ac ξ = dt, f ξ :=
  (Finset.sum_fiberwise_of_maps_to (fun ξ hξ => Finset.mem_image_of_mem _ hξ) f).symm

theorem pkOf_of_subset_fiberA {pk : BitVec 128} {T : Finset Rec} (hT : T ⊆ fiberA pk) :
    ∀ ξ ∈ T, pkOf ξ = pk := by
  intro ξ hξ
  exact (Finset.mem_filter.mp (hT hξ)).2

/-- Full public-data fibers partition the public-key record fiber. Subsets may
be selected by earlier bad-event filters without assuming conditional uniformity. -/
theorem fiber_weights_le (Ac : Finset Name) {T : Finset Rec} {pk : BitVec 128}
    (hT : T ⊆ fiberA pk) :
    (∑ dt ∈ T.image (dataOf Ac), sumW (fiberB Ac dt)) ≤ sumW (fiberA pk) := by
  have hTpk := pkOf_of_subset_fiberA hT
  have hsub : ∀ dt ∈ T.image (dataOf Ac), fiberB Ac dt ⊆
      ((fiberA pk).filter fun ξ => dataOf Ac ξ ∈ T.image (dataOf Ac)).filter
        fun ξ => dataOf Ac ξ = dt := by
    intro dt hdt
    obtain ⟨ξ₀, hξ₀T, hξ₀⟩ := Finset.mem_image.1 hdt
    have hpk₀ := hTpk ξ₀ hξ₀T
    intro ξ hξ
    simp only [fiberB, Finset.mem_filter, Finset.mem_univ, true_and] at hξ
    have hpk : pkOf ξ = pkOf ξ₀ := by
      have := hξ.trans hξ₀.symm
      simp only [dataOf, Prod.mk.injEq] at this
      exact this.1
    simp only [fiberA, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨⟨hpk.trans hpk₀, ?_⟩, hξ⟩
    rw [hξ]
    exact hdt
  calc
    _ ≤ ∑ dt ∈ T.image (dataOf Ac),
        ∑ ξ ∈ ((fiberA pk).filter fun ξ => dataOf Ac ξ ∈ T.image (dataOf Ac))
          with dataOf Ac ξ = dt, w :=
      Finset.sum_le_sum fun dt hdt => Finset.sum_le_sum_of_subset (hsub dt hdt)
    _ = ∑ ξ ∈ ((fiberA pk).filter fun ξ => dataOf Ac ξ ∈ T.image (dataOf Ac)), w :=
      Finset.sum_fiberwise_of_maps_to (fun ξ hξ => (Finset.mem_filter.1 hξ).2) _
    _ ≤ sumW (fiberA pk) := Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)

/-- On one record fiber the actual continuation and starting cache are identical.
Exchange expectation with the finite record sum, then invoke one common budget. -/
theorem fiber_continuation {α : Type} {Ac : Finset Name} (hAc : IsCut Ac) (dt : Data)
    {T : Finset Rec} (hT : T ⊆ fiberB Ac dt) (J : Cache → ℝ≥0∞) (rate : ℝ≥0∞)
    (I : Cache → ℕ → Prop)
    (hIf : ∀ c b q, I c b → c q = none → queryCost (.inr q) ≤ b →
      ∀ u, I (c.cacheQuery q u) (b-queryCost (.inr q)))
    (hIc : ∀ c b q, I c b → (c q).isSome → queryCost (.inr q) ≤ b → I c (b-queryCost (.inr q)))
    (hJ : IndexCharge J rate I) (K : Data → OracleComp Spec α)
    (d : Cache) (b : ℕ) (hI : I (Cache.extend d dt.2.2) b) (hB : CostAtMost (K dt) b) :
    (∑ ξ ∈ T, w * E (run (K (dataOf Ac ξ)) (Cache.extend d (fExp (some Ac) ξ)))
      (fun p => ind (Cache.Hits p.2 (fHid (some Ac) ξ)) + ind (Spr p.2 ξ) + J p.2)) ≤
      jointPotential T (some Ac) J (Cache.extend d dt.2.2) +
        max authRate rate * sumW (fiberB Ac dt) * b := by
  have hdata : ∀ ξ ∈ T, dataOf Ac ξ = dt := by
    intro ξ hξ
    exact (Finset.mem_filter.mp (hT hξ)).2
  have hrun : ∀ ξ ∈ T,
      run (K (dataOf Ac ξ)) (Cache.extend d (fExp (some Ac) ξ)) =
        run (K dt) (Cache.extend d dt.2.2) := by
    intro ξ hξ
    have hd := hdata ξ hξ
    have hf : fExp (some Ac) ξ = dt.2.2 := congrArg (fun a : Data => a.2.2) hd
    rw [hd, hf]
  have hsum : (∑ ξ ∈ T, w * E (run (K (dataOf Ac ξ)) (Cache.extend d (fExp (some Ac) ξ)))
      (fun p => ind (Cache.Hits p.2 (fHid (some Ac) ξ)) + ind (Spr p.2 ξ) + J p.2)) =
      E (run (K dt) (Cache.extend d dt.2.2))
        (fun p => jointPotential T (some Ac) J p.2) := by
    simp only [jointPotential, authPotential, sumW, Finset.sum_mul, ← Finset.sum_add_distrib,
      ← mul_add]
    rw [E_finsetSum]
    apply Finset.sum_congr rfl
    intro ξ hξ
    rw [hrun ξ hξ, E_const_mul]
  rw [hsum]
  exact joint_continuation hAc dt hT J rate I hIf hIc hJ (K dt)
    (fun _ c => jointPotential T (some Ac) J c) (fun _ _ => le_rfl)
    (Cache.extend d dt.2.2) b hI hB

end OptimalOTS.WeightedConstruction.WideForest
#print axioms OptimalOTS.WeightedConstruction.WideForest.fiber_weights_le
#print axioms OptimalOTS.WeightedConstruction.WideForest.fiber_continuation
