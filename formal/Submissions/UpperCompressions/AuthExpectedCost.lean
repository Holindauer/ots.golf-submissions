import Submissions.UpperCompressions.ExpectedChargeMaster
import Submissions.UpperCompressions.WideAuthLocality

/-! Authentication charges only actual expected non-index paid queries. Index
entries may already be privately cached or fully preloaded; no posterior law is
assumed for them and no separate copy of the whole paid budget is used. -/
open OracleSpec OracleComp OracleComp.EvalDist ENNReal
noncomputable section
open scoped Classical
namespace OptimalOTS.WeightedConstruction.WideForest
open OptimalOTS.Dag Name WeightedReplacement
set_option maxHeartbeats 800000
attribute [local irreducible] hashBits blockBits msgBits Finset.univ Finset.filter

/-- A caller-selected index predicate may mark only encoding hash queries as
free of graph charge. Private uniform queries have zero cost in either category. -/
theorem auth_query_expected {Ac : Finset Name} (hAc : IsCut Ac) (dt : Data)
    {T : Finset Rec} (hT : T ⊆ fiberB Ac dt)
    (isIndex : Spec.Domain → Prop)
    (hindex : ∀ q, isIndex (.inr q) → ∃ u : EncInput, q = encQuery u)
    (t : Spec.Domain) (c : Cache) :
    E ((oracleImpl t).run c) (fun p => authPotential T (some Ac) p.2) ≤
      authPotential T (some Ac) c +
        (authRate*sumW (fiberB Ac dt))*otherPaid isIndex t := by
  cases t with
  | inl n =>
    rw [oracleImpl_run_inl, E_bind]
    simp only [E_pure, otherPaid, queryCost]
    split_ifs <;> simpa using E_const_le (liftM (unifSpec.query n) : ProbComp (unifSpec.Range n))
      (authPotential T (some Ac) c)
  | inr q =>
    cases hc : c q with
    | some u =>
      rw [oracleImpl_run_inr_some hc, E_pure]
      exact le_self_add
    | none =>
      rw [oracleImpl_run_inr_none hc, E_bind, E_uniform]
      simp only [E_pure]
      by_cases hi : isIndex (.inr q)
      · obtain ⟨u,rfl⟩ := hindex q hi
        rw [authPotential_index, otherPaid, if_pos hi, mul_zero, add_zero]
      · rw [otherPaid, if_neg hi]
        exact authPotential_charge hAc dt hT c q hc

/-- Graph-only master refinement, valid for the actual shared oracle from any
starting cache, including a fixed eagerly preloaded index table. -/
theorem auth_continuation_expected {α : Type} {Ac : Finset Name} (hAc : IsCut Ac) (dt : Data)
    {T : Finset Rec} (hT : T ⊆ fiberB Ac dt)
    (isIndex : Spec.Domain → Prop)
    (hindex : ∀ q, isIndex (.inr q) → ∃ u : EncInput, q = encQuery u)
    (oa : OracleComp Spec α) (c : Cache) :
    E (run oa c) (fun p => authPotential T (some Ac) p.2) ≤
      authPotential T (some Ac) c +
        (authRate*sumW (fiberB Ac dt))*expectedCharge (otherPaid isIndex) oa c :=
  WeightedExpectedCharge.master_expected (authPotential T (some Ac)) (otherPaid isIndex)
    (authRate*sumW (fiberB Ac dt)) (auth_query_expected hAc dt hT isIndex hindex) oa c

/-- On a disclosure fiber all records share the same reduced actual execution,
so their graph authentication loss uses one common expected paid-query clock. -/
theorem fiber_auth_expected {α : Type} {Ac : Finset Name} (hAc : IsCut Ac) (dt : Data)
    {T : Finset Rec} (hT : T ⊆ fiberB Ac dt)
    (isIndex : Spec.Domain → Prop)
    (hindex : ∀ q, isIndex (.inr q) → ∃ u : EncInput, q = encQuery u)
    (K : Data → OracleComp Spec α) (d : Cache) :
    (∑ ξ ∈ T, w*E (run (K (dataOf Ac ξ)) (Cache.extend d (fExp (some Ac) ξ)))
      (fun p => ind (Cache.Hits p.2 (fHid (some Ac) ξ))+ind (Spr p.2 ξ))) ≤
      authPotential T (some Ac) (Cache.extend d dt.2.2) +
        (authRate*sumW (fiberB Ac dt))*
          expectedCharge (otherPaid isIndex) (K dt) (Cache.extend d dt.2.2) := by
  have hdata : ∀ ξ ∈ T, dataOf Ac ξ = dt := fun ξ hξ => (Finset.mem_filter.mp (hT hξ)).2
  have hrun : ∀ ξ ∈ T,
      run (K (dataOf Ac ξ)) (Cache.extend d (fExp (some Ac) ξ)) =
        run (K dt) (Cache.extend d dt.2.2) := by
    intro ξ hξ
    have hd := hdata ξ hξ
    have hf : fExp (some Ac) ξ = dt.2.2 := congrArg (fun a : Data => a.2.2) hd
    rw [hd,hf]
  have hsum : (∑ ξ ∈ T, w*E (run (K (dataOf Ac ξ)) (Cache.extend d (fExp (some Ac) ξ)))
      (fun p => ind (Cache.Hits p.2 (fHid (some Ac) ξ))+ind (Spr p.2 ξ))) =
      E (run (K dt) (Cache.extend d dt.2.2)) (fun p => authPotential T (some Ac) p.2) := by
    unfold authPotential
    rw [E_finsetSum]
    apply Finset.sum_congr rfl
    intro ξ hξ
    rw [hrun ξ hξ, E_const_mul]
  rw [hsum]
  exact auth_continuation_expected hAc dt hT isIndex hindex (K dt) (Cache.extend d dt.2.2)

#print axioms auth_query_expected
#print axioms auth_continuation_expected
#print axioms fiber_auth_expected
end OptimalOTS.WeightedConstruction.WideForest
