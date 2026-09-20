import Submissions.UpperCompressions.WideAvailability
import Submissions.UpperCompressions.WideSecure

namespace OptimalOTS.Challenge.UpperCompressions

noncomputable def scheme : OracleAlgorithm.Scheme :=
  WeightedConstruction.WideWire.scheme

theorem admissible : scheme.Admissible :=
  WeightedConstruction.WideHonest.admissible

theorem secure : scheme.Secure :=
  WeightedConstruction.WideSecure.raw_secure

theorem cost : scheme.VerifyCostAtMost 92 :=
  WeightedConstruction.WideWire.cost

end OptimalOTS.Challenge.UpperCompressions
