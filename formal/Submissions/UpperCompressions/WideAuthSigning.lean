import Submissions.UpperCompressions.WideAuthLocality
import Submissions.UpperCompressions.ReplacementLocality

/-! The actual all-L signer satisfies precisely the graph locality interface.
No restriction is placed on its accepted nonwinning cache entries. -/
open OracleSpec OracleComp OracleComp.EvalDist ENNReal
noncomputable section
open scoped Classical
namespace OptimalOTS.WeightedConstruction.WideForest
open OptimalOTS.Dag Name

theorem sign_indexExtension {M : ℕ} (S : WeightedScheme.Scheme M)
    (x : S.graph.Assignment) (m : Message) (c : Cache)
    (p : Option WeightedScheme.Signature × Cache)
    (hp : p ∈ support (run (S.sign x m) c)) : IndexExtension c p.2 := by
  refine ⟨sub_of_mem_support_run _ c p hp, ?_⟩
  intro q v hc he
  obtain ⟨η, hη⟩ := ReplacementLocality.sign_new_cache_row S x m c p hp q v hc he
  exact ⟨(m, η), hη⟩

/-- After an actual supported signing run, graph hidden hits remain absent and
spurious graph images agree with their pre-sign values on every public-data fiber. -/
theorem authPotential_after_actual_sign {M : ℕ} (S : WeightedScheme.Scheme M)
    (x : S.graph.Assignment) (m : Message) (c : Cache)
    (p : Option WeightedScheme.Signature × Cache)
    (hp : p ∈ support (run (S.sign x m) c))
    (T : Finset Rec) (A? : Option (Finset Name))
    (hT : ∀ ξ ∈ T, ¬ Cache.Hits c (kc ξ))
    (fe : Cache) (he : ∀ ξ ∈ T, fExp A? ξ = fe) :
    authPotential T A? (Cache.extend p.2 fe) = ∑ ξ ∈ T, w * ind (Spr c ξ) :=
  authPotential_after_sign (sign_indexExtension S x m c p hp) T A? hT fe he

end OptimalOTS.WeightedConstruction.WideForest
#print axioms OptimalOTS.WeightedConstruction.WideForest.authPotential_after_actual_sign
