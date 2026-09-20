import Submissions.UpperCompressions.WideAuthPotential

/-! Signing locality needed by graph authentication. Accepted nonwinning
signing trials are unrestricted. Only the domain of new cache entries matters. -/
open OracleSpec OracleComp OracleComp.EvalDist ENNReal
noncomputable section
open scoped Classical
namespace OptimalOTS.WeightedConstruction.WideForest
open OptimalOTS.Dag Name

def IndexExtension (d d' : Cache) : Prop := Cache.Sub d d' ∧
  ∀ q v, d q = none → d' q = some v → ∃ u : EncInput, q = encQuery u

theorem sub_extend_left (c f : Cache) : Cache.Sub c (Cache.extend c f) :=
  fun _ _ h => Cache.extend_apply_of_some h

/-- With no keygen point of `ξ` in `d`, none is in `d'` either: the new entries of `d'` are
encoding entries. -/
theorem indexExtension_kc_none {d d' : Cache} (hd' : IndexExtension d d')
    {ξ : Rec} (hξ : ¬ Cache.Hits d (kc ξ)) {q : Query} (hq : (kc ξ q).isSome) : d' q = none := by
  rcases hq' : d' q with _ | v
  · rfl
  · exfalso
    rcases hdq : d q with _ | u
    · obtain ⟨u₀, hqe⟩ := hd'.2 q v hdq hq'
      rw [hqe, kc_enc] at hq
      simp at hq
    · exact hξ ⟨q, hq, by rw [hdq]; rfl⟩

theorem not_hits_fHid_of_indexExtension {d d' : Cache} (hd' : IndexExtension d d')
    {ξ : Rec} (hξ : ¬ Cache.Hits d (kc ξ)) (A? : Option (Finset Name)) :
    ¬ Cache.Hits d' (fHid A? ξ) := by
  rintro ⟨q, hq, hq'⟩
  have hkq : (kc ξ q).isSome := by
    obtain ⟨h, p, hp, -, hqp⟩ := (fHid_isSome_iff A? ξ q).1 hq
    exact (kc_isSome_iff ξ q).2 ⟨h, p, hp, hqp⟩
  rw [indexExtension_kc_none hd' hξ hkq] at hq'
  simp at hq'

theorem not_hits_extend_fExp_fHid {d d' : Cache} (hd' : IndexExtension d d')
    {ξ : Rec} (hξ : ¬ Cache.Hits d (kc ξ)) (A? : Option (Finset Name)) :
    ¬ Cache.Hits (Cache.extend d' (fExp A? ξ)) (fHid A? ξ) := by
  rw [Cache.hits_extend]
  rintro (h | h)
  · exact not_hits_fHid_of_indexExtension hd' hξ A? h
  · exact (disjoint_fExp_fHid A? ξ).not_hits h

theorem spr_indexExtension_iff {d d' : Cache} (hd' : IndexExtension d d')
    (ξ : Rec) : Spr d' ξ ↔ Spr d ξ := by
  constructor
  · rintro ⟨h, p, hp, u, hu, htag, w, hw, htr⟩
    refine ⟨h, p, hp, u, hu, htag, w, ?_, htr⟩
    rcases hdq : d ⟨p.len, u⟩ with _ | v
    · exfalso
      obtain ⟨u₀, hqe⟩ := hd'.2 _ w hdq hw
      exact mk_ne_encQuery hp u _ hqe
    · rw [hd'.1 _ _ hdq] at hw
      exact hw
  · exact Spr.mono hd'.1

theorem spr_extend_fExp_iff {d d' : Cache} (hd' : IndexExtension d d')
    (ξ : Rec) (A? : Option (Finset Name)) :
    Spr (Cache.extend d' (fExp A? ξ)) ξ ↔ Spr d ξ := by
  constructor
  · intro hs
    rcases spr_of_extend hs with hs | hs
    · exact (spr_indexExtension_iff hd' ξ).1 hs
    · exact absurd hs (not_spr_fExp A? ξ)
  · intro hs
    exact Spr.mono (sub_extend_left d' _) ((spr_indexExtension_iff hd' ξ).2 hs)


theorem authPotential_after_sign {d d' : Cache} (hd' : IndexExtension d d')
    (T : Finset Rec) (A? : Option (Finset Name))
    (hT : ∀ ξ ∈ T, ¬ Cache.Hits d (kc ξ))
    (fe : Cache) (he : ∀ ξ ∈ T, fExp A? ξ = fe) :
    authPotential T A? (Cache.extend d' fe) = ∑ ξ ∈ T, w * ind (Spr d ξ) := by
  unfold authPotential
  apply Finset.sum_congr rfl
  intro ξ hξ
  rw [← he ξ hξ]
  have hh := not_hits_extend_fExp_fHid hd' (hT ξ hξ) A?
  have hs := spr_extend_fExp_iff hd' ξ A?
  simp only [ind, if_neg hh, hs, zero_add]

end OptimalOTS.WeightedConstruction.WideForest
#print axioms OptimalOTS.WeightedConstruction.WideForest.authPotential_after_sign
