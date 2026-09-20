import Submissions.UpperCompressions.ActualSmallSecurity
import Submissions.UpperCompressions.ActualLargeSecurity
import Submissions.UpperCompressions.WideSecurityClosure

/-! Full strong security of the weighted, wide-word forest construction. -/
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
namespace OptimalOTS.WeightedConstruction.WideSecure
open WideForest

theorem typed_secure : forestScheme.toAlgorithm.Secure := by
  apply WideSecurityClosure.typed_secure_of_bounds
  · intro A B hB hsmall hcap
    exact WideSmallSecurity.actual_small_security A hB hsmall (by exact_mod_cast hcap)
  · intro A B hB hlarge hcap
    exact actual_large_security A hB hlarge (by exact_mod_cast hcap)

theorem raw_secure : WideWire.scheme.Secure :=
  WideBudgetEndpoints.raw_secure_of_typed typed_secure

#print axioms typed_secure
#print axioms raw_secure
end OptimalOTS.WeightedConstruction.WideSecure
