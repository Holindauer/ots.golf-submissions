import Submissions.UpperCompressions.AuthExpectedCost
import Submissions.UpperCompressions.WideAuthSigning

/-! Graph authentication after the actual all-L signer, retaining the expected
non-index paid clock of the reduced continuation on each disclosure fiber. -/
open OracleSpec OracleComp OracleComp.EvalDist ENNReal
noncomputable section
open scoped Classical
set_option maxRecDepth 10000
namespace OptimalOTS.WeightedConstruction.WideForest
open OptimalOTS.Dag Name WeightedReplacement
set_option maxHeartbeats 800000
attribute [local irreducible] hashBits blockBits msgBits Finset.univ Finset.filter

/-- Weighted full disclosure fibers lie inside the public-key record fiber.
The weight may be an expected cost of the actual fiber-dependent continuation. -/
theorem fiber_costs_le (Ac : Finset Name) {T : Finset Rec} {pk : BitVec 128}
    (hT : T ⊆ fiberA pk) (F : Data → ℝ≥0∞) :
    (∑ dt ∈ T.image (dataOf Ac), sumW (fiberB Ac dt)*F dt) ≤
      ∑ ξ ∈ fiberA pk, w*F (dataOf Ac ξ) := by
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
  have hcost (dt : Data) : sumW (fiberB Ac dt)*F dt =
      ∑ ξ ∈ fiberB Ac dt, w*F (dataOf Ac ξ) := by
    rw [sumW, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro ξ hξ
    rw [(Finset.mem_filter.mp hξ).2]
  calc
    _ = ∑ dt ∈ T.image (dataOf Ac), ∑ ξ ∈ fiberB Ac dt, w*F (dataOf Ac ξ) :=
      Finset.sum_congr rfl fun dt _ => hcost dt
    _ ≤ ∑ dt ∈ T.image (dataOf Ac),
        ∑ ξ ∈ ((fiberA pk).filter fun ξ => dataOf Ac ξ ∈ T.image (dataOf Ac))
          with dataOf Ac ξ = dt, w*F (dataOf Ac ξ) :=
      Finset.sum_le_sum fun dt hdt => Finset.sum_le_sum_of_subset (hsub dt hdt)
    _ = ∑ ξ ∈ ((fiberA pk).filter fun ξ => dataOf Ac ξ ∈ T.image (dataOf Ac)),
        w*F (dataOf Ac ξ) :=
      Finset.sum_fiberwise_of_maps_to (fun ξ hξ => (Finset.mem_filter.1 hξ).2) _
    _ ≤ _ := Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)

/-- The signer's private index-only extension creates no graph authentication
loss. The remaining charge is the actual expected non-index cost, averaged over
the full public-key record fiber; it is not a second copy of the paid budget. -/
theorem postsign_auth_expected {α : Type} {Ac : Finset Name} (hAc : IsCut Ac)
    (pk : BitVec 128) (T : Finset Rec) (hT : T ⊆ fiberA pk)
    (d d' : Cache) (hd' : IndexExtension d d')
    (hTd : ∀ ξ ∈ T, ¬ Cache.Hits d (kc ξ))
    (isIndex : Spec.Domain → Prop)
    (hindex : ∀ q, isIndex (.inr q) → ∃ u : EncInput, q = encQuery u)
    (K : Data → OracleComp Spec α) :
    (∑ ξ ∈ T, w*E (run (K (dataOf Ac ξ)) (Cache.extend d' (fExp (some Ac) ξ)))
      (fun p => ind (Cache.Hits p.2 (fHid (some Ac) ξ))+ind (Spr p.2 ξ))) ≤
      (∑ ξ ∈ T, w*ind (Spr d ξ)) +
        authRate * ∑ ξ ∈ fiberA pk, w *
          expectedCharge (otherPaid isIndex) (K (dataOf Ac ξ))
            (Cache.extend d' (fExp (some Ac) ξ)) := by
  have hfiber : ∀ dt ∈ T.image (dataOf Ac),
      (∑ ξ ∈ T with dataOf Ac ξ = dt,
        w*E (run (K (dataOf Ac ξ)) (Cache.extend d' (fExp (some Ac) ξ)))
          (fun p => ind (Cache.Hits p.2 (fHid (some Ac) ξ))+ind (Spr p.2 ξ))) ≤
      (∑ ξ ∈ T with dataOf Ac ξ = dt, w*ind (Spr d ξ)) +
        authRate * (sumW (fiberB Ac dt)*
          expectedCharge (otherPaid isIndex) (K dt) (Cache.extend d' dt.2.2)) := by
    intro dt hdt
    let Td := T.filter fun ξ => dataOf Ac ξ = dt
    have hdata : ∀ ξ ∈ Td, dataOf Ac ξ = dt := fun ξ hξ => (Finset.mem_filter.mp hξ).2
    have hsub : Td ⊆ fiberB Ac dt := by
      intro ξ hξ
      simp only [fiberB, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hdata ξ hξ
    have hfe : ∀ ξ ∈ Td, fExp (some Ac) ξ = dt.2.2 :=
      fun ξ hξ => congrArg (fun a : Data => a.2.2) (hdata ξ hξ)
    have hc := fiber_auth_expected hAc dt hsub isIndex hindex K d'
    rw [authPotential_after_sign hd' Td (some Ac)
      (fun ξ hξ => hTd ξ (Finset.mem_filter.mp hξ).1) dt.2.2 hfe] at hc
    simpa only [mul_assoc] using hc
  rw [record_regroup T Ac, record_regroup T Ac (fun ξ => w*ind (Spr d ξ))]
  refine (Finset.sum_le_sum hfiber).trans ?_
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  apply add_le_add_right
  apply mul_le_mul_right
  exact fiber_costs_le Ac hT (fun dt =>
    expectedCharge (otherPaid isIndex) (K dt) (Cache.extend d' dt.2.2))

/-- The graph refinement applies to every supported outcome of the actual
all-L signer, including its accepted nonwinning cached index entries. -/
theorem actual_sign_auth_expected {α : Type} {M : ℕ} (S : WeightedScheme.Scheme M)
    (x : S.graph.Assignment) (m : Message) (d : Cache)
    (p : Option WeightedScheme.Signature × Cache)
    (hp : p ∈ support (run (S.sign x m) d))
    {Ac : Finset Name} (hAc : IsCut Ac)
    (pk : BitVec 128) (T : Finset Rec) (hT : T ⊆ fiberA pk)
    (hTd : ∀ ξ ∈ T, ¬ Cache.Hits d (kc ξ))
    (isIndex : Spec.Domain → Prop)
    (hindex : ∀ q, isIndex (.inr q) → ∃ u : EncInput, q = encQuery u)
    (K : Data → OracleComp Spec α) :
    (∑ ξ ∈ T, w*E (run (K (dataOf Ac ξ)) (Cache.extend p.2 (fExp (some Ac) ξ)))
      (fun z => ind (Cache.Hits z.2 (fHid (some Ac) ξ))+ind (Spr z.2 ξ))) ≤
      (∑ ξ ∈ T, w*ind (Spr d ξ)) +
        authRate * ∑ ξ ∈ fiberA pk, w *
          expectedCharge (otherPaid isIndex) (K (dataOf Ac ξ))
            (Cache.extend p.2 (fExp (some Ac) ξ)) :=
  postsign_auth_expected hAc pk T hT d p.2 (sign_indexExtension S x m d p hp)
    hTd isIndex hindex K

/-- Index and graph loss share one actual expected paid-query clock on every
record, before averaging. Both costs use exactly the same program and cache. -/
theorem record_shared_paid_budget {α : Type} (Ac : Finset Name) (pk : BitVec 128)
    (d' : Cache) (isIndex : Spec.Domain → Prop) (a b : ℝ≥0∞)
    (K : Data → OracleComp Spec α) (B : ℕ)
    (hB : ∀ ξ ∈ fiberA pk, CostAtMost (K (dataOf Ac ξ)) B) :
    a * (∑ ξ ∈ fiberA pk, w * expectedCharge (indexPaid isIndex)
      (K (dataOf Ac ξ)) (Cache.extend d' (fExp (some Ac) ξ))) +
    b * (∑ ξ ∈ fiberA pk, w * expectedCharge (otherPaid isIndex)
      (K (dataOf Ac ξ)) (Cache.extend d' (fExp (some Ac) ξ))) ≤
      max a b * sumW (fiberA pk) * B := by
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  calc
    _ = ∑ ξ ∈ fiberA pk, w * (a * expectedCharge (indexPaid isIndex)
        (K (dataOf Ac ξ)) (Cache.extend d' (fExp (some Ac) ξ)) +
        b * expectedCharge (otherPaid isIndex)
        (K (dataOf Ac ξ)) (Cache.extend d' (fExp (some Ac) ξ))) := by
      apply Finset.sum_congr rfl
      intro ξ _
      ring
    _ ≤ ∑ ξ ∈ fiberA pk, w*(max a b*B) :=
      Finset.sum_le_sum fun ξ hξ => mul_le_mul_right
        (paid_shared_budget isIndex a b (K (dataOf Ac ξ))
          (Cache.extend d' (fExp (some Ac) ξ)) B (hB ξ hξ)) w
    _ = _ := by rw [← Finset.sum_mul, ← sumW]; ring

#print axioms fiber_costs_le
#print axioms postsign_auth_expected
#print axioms actual_sign_auth_expected
#print axioms record_shared_paid_budget
end OptimalOTS.WeightedConstruction.WideForest
