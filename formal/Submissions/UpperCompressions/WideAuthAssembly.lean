import Submissions.UpperCompressions.WideAuthCoupling
import Submissions.UpperCompressions.WideAuthLocality

/-! Regroup a real continuation over every disclosure fiber, preserving the
uniform keygen record law and one paid budget. The class-dependent index charge
is an explicit obligation; this theorem is not a strong-security export. -/
open OracleSpec OracleComp OracleComp.EvalDist ENNReal
noncomputable section
open scoped Classical
set_option maxRecDepth 10000
attribute [local irreducible] Finset.univ Finset.filter
namespace OptimalOTS.WeightedConstruction.WideForest
open OptimalOTS.Dag Name

theorem postsign_continuation {α : Type} {Ac : Finset Name} (hAc : IsCut Ac)
    (pk : BitVec 128) (T : Finset Rec) (hT : T ⊆ fiberA pk)
    (d d' : Cache) (hd' : IndexExtension d d') (hTd : ∀ ξ ∈ T, ¬ Cache.Hits d (kc ξ))
    (J : Data → Cache → ℝ≥0∞) (rate : ℝ≥0∞) (I : Data → Cache → ℕ → Prop)
    (hIf : ∀ dt c b q, I dt c b → c q = none → queryCost (.inr q) ≤ b →
      ∀ u, I dt (c.cacheQuery q u) (b-queryCost (.inr q)))
    (hIc : ∀ dt c b q, I dt c b → (c q).isSome → queryCost (.inr q) ≤ b →
      I dt c (b-queryCost (.inr q)))
    (hJ : ∀ dt ∈ T.image (dataOf Ac), IndexCharge (J dt) rate (I dt))
    (K : Data → OracleComp Spec α) (b : ℕ)
    (hI : ∀ dt ∈ T.image (dataOf Ac), I dt (Cache.extend d' dt.2.2) b)
    (hB : ∀ dt ∈ T.image (dataOf Ac), CostAtMost (K dt) b) :
    (∑ ξ ∈ T, w * E (run (K (dataOf Ac ξ)) (Cache.extend d' (fExp (some Ac) ξ)))
      (fun p => ind (Cache.Hits p.2 (fHid (some Ac) ξ)) + ind (Spr p.2 ξ) + J (dataOf Ac ξ) p.2)) ≤
      (∑ ξ ∈ T, w * (ind (Spr d ξ) + J (dataOf Ac ξ) (Cache.extend d' (fExp (some Ac) ξ)))) +
        max authRate rate * sumW (fiberA pk) * b := by
  have hfiber : ∀ dt ∈ T.image (dataOf Ac),
      (∑ ξ ∈ T with dataOf Ac ξ = dt,
        w * E (run (K (dataOf Ac ξ)) (Cache.extend d' (fExp (some Ac) ξ)))
          (fun p => ind (Cache.Hits p.2 (fHid (some Ac) ξ)) + ind (Spr p.2 ξ) + J (dataOf Ac ξ) p.2)) ≤
      (∑ ξ ∈ T with dataOf Ac ξ = dt,
        w * (ind (Spr d ξ) + J (dataOf Ac ξ) (Cache.extend d' (fExp (some Ac) ξ)))) +
        max authRate rate * sumW (fiberB Ac dt) * b := by
    intro dt hdt
    let Td := T.filter fun ξ => dataOf Ac ξ = dt
    have hdata : ∀ ξ ∈ Td, dataOf Ac ξ = dt := fun ξ hξ => (Finset.mem_filter.mp hξ).2
    have hsub : Td ⊆ fiberB Ac dt := by
      intro ξ hξ
      simp only [fiberB, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hdata ξ hξ
    have hfe : ∀ ξ ∈ Td, fExp (some Ac) ξ = dt.2.2 :=
      fun ξ hξ => congrArg (fun a : Data => a.2.2) (hdata ξ hξ)
    have hc := fiber_continuation hAc dt hsub (J dt) rate (I dt) (hIf dt) (hIc dt)
      (hJ dt hdt) K d' b (hI dt hdt) (hB dt hdt)
    have hinit : jointPotential Td (some Ac) (J dt) (Cache.extend d' dt.2.2) =
        ∑ ξ ∈ Td, w * (ind (Spr d ξ) + J (dataOf Ac ξ) (Cache.extend d' (fExp (some Ac) ξ))) := by
      rw [jointPotential, authPotential_after_sign hd' Td (some Ac)
        (fun ξ hξ => hTd ξ (Finset.mem_filter.mp hξ).1) dt.2.2 hfe]
      simp only [sumW, Finset.sum_mul, ← Finset.sum_add_distrib, ← mul_add]
      apply Finset.sum_congr rfl
      intro ξ hξ
      rw [hdata ξ hξ, hfe ξ hξ]
    rw [hinit] at hc
    have he : (∑ ξ ∈ Td,
        w * E (run (K (dataOf Ac ξ)) (Cache.extend d' (fExp (some Ac) ξ)))
          (fun p => ind (Cache.Hits p.2 (fHid (some Ac) ξ)) + ind (Spr p.2 ξ) + J (dataOf Ac ξ) p.2)) =
        ∑ ξ ∈ Td,
        w * E (run (K (dataOf Ac ξ)) (Cache.extend d' (fExp (some Ac) ξ)))
          (fun p => ind (Cache.Hits p.2 (fHid (some Ac) ξ)) + ind (Spr p.2 ξ) + J dt p.2) := by
      apply Finset.sum_congr rfl
      intro ξ hξ
      rw [hdata ξ hξ]
    exact he.le.trans hc
  rw [record_regroup T Ac, record_regroup T Ac (fun ξ =>
    w * (ind (Spr d ξ) + J (dataOf Ac ξ) (Cache.extend d' (fExp (some Ac) ξ))))]
  refine (Finset.sum_le_sum hfiber).trans ?_
  rw [Finset.sum_add_distrib]
  apply add_le_add_right
  rw [← Finset.sum_mul, ← Finset.mul_sum]
  exact mul_le_mul_left (mul_le_mul_right (fiber_weights_le Ac hT) (max authRate rate)) b

end OptimalOTS.WeightedConstruction.WideForest
#print axioms OptimalOTS.WeightedConstruction.WideForest.postsign_continuation
