import Submissions.UpperCompressions.WideIndexDomains
import Submissions.UpperCompressions.ProtectedCacheStatistics

/-! The exact primitive-query law for the concrete weighted92 decoder under
the contract's actual shared random oracle. This applies before signing. -/
noncomputable section
namespace OptimalOTS.WeightedConstruction.WidePreSign
open OracleSpec OracleComp
open WeightedSchedule WideDomains WeightedCacheCounts WeightedRow.Weights
open WeightedRealExecution WeightedDirectCache
open scoped Classical

theorem primitive_law (A : Finset Query) (t : Spec.Domain) (c : hashSpec.QueryCache)
    (f : ℕ → (Fin M → ℕ) → ℝ) :
    realEval ((oracleImpl t).run c)
      (fun out => f (seen A out.2).card (classCounts A out.2 decode)) =
    securityWeights.expect (fun x => f
      (step (protectedFresh A t c) (seen A c).card (classCounts A c decode) x).1
      (step (protectedFresh A t c) (seen A c).card (classCounts A c decode) x).2) := by
  exact WeightedProtectedCache.query_law securityWeights A decode decoder_law t c f

theorem index_initial (c : hashSpec.QueryCache)
    (hf : ∀ q : Query,q.1=342 → c q=none) :
    (seen indexDomain c).card=0 ∧ classCounts indexDomain c decode=(fun _ => 0) := by
  constructor
  · rw [fresh_seen_empty c hf,Finset.card_empty]
  · exact fresh_counts_zero c hf

theorem row_count_bound (m : Message) (c : hashSpec.QueryCache) :
    (seen (rowDomain m) c).card ≤ 2^86 := seen_row_bound m c

#print axioms primitive_law
#print axioms index_initial
end OptimalOTS.WeightedConstruction.WidePreSign
