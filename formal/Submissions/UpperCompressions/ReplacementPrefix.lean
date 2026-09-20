import Submissions.UpperCompressions.ReplacementProgram

/-! Adaptive public-prefix invariance for actual `OracleComp Spec` programs.
The interpreter records uniform draws and answered hash queries, and stops before
answering the distinguished query. Its whole distribution is invariant under any
change to that table coordinate. This uses a complete-table view; hidden signer
queries never become independent fresh public answers. -/

open OracleSpec OracleComp OracleComp.EvalDist ENNReal
open OptimalOTS

namespace WeightedReplacement

noncomputable section
open scoped Classical
local instance stagedLocal_ReplacementPrefix_1 {α : Type*} : DecidableEq α := Classical.decEq α

abbrev PublicStep := Σ t : Spec.Domain, Spec.Range t
abbrev PublicTrace := List PublicStep
abbrev PrefixM := OptionT (StateT PublicTrace ProbComp)

/-- Trace is stored in reverse chronological order. `none` means the program
requested the distinguished hash input; that request is not answered. All free
uniform choices are preserved and recorded, so their revelation is allowed. -/
def prefixImpl (u : Query) (table : Query → BitVec hashBits) : QueryImpl Spec PrefixM
  | .inl n => OptionT.mk fun trace => do
      let a ← HasQuery.query (spec := unifSpec) (m := ProbComp) n
      pure (some a, ⟨.inl n, a⟩ :: trace)
  | .inr q => OptionT.mk fun trace =>
      if q = u then pure (none, trace)
      else pure (some (table q), ⟨.inr q, table q⟩ :: trace)

def prefixRun {α : Type} (u : Query) (table : Query → BitVec hashBits)
    (oa : OracleComp Spec α) : ProbComp (Option α × PublicTrace) :=
  (OptionT.run (simulateQ (prefixImpl u table) oa)).run []

theorem prefixImpl_target (u : Query) (table : Query → BitVec hashBits) (trace : PublicTrace) :
    (OptionT.run (prefixImpl u table (.inr u))).run trace = pure (none, trace) := by
  simp [prefixImpl, OptionT.run, OptionT.mk, StateT.run]

theorem prefixImpl_hash_of_ne (u q : Query) (table : Query → BitVec hashBits)
    (hqu : q ≠ u) (trace : PublicTrace) :
    (OptionT.run (prefixImpl u table (.inr q))).run trace =
      pure (some (table q), ⟨.inr q, table q⟩ :: trace) := by
  simp [prefixImpl, OptionT.run, OptionT.mk, StateT.run, hqu]

theorem prefixImpl_eq_of_eq_off (u : Query) (table table' : Query → BitVec hashBits)
    (h : ∀ q, q ≠ u → table q = table' q) : prefixImpl u table = prefixImpl u table' := by
  funext t
  cases t with
  | inl n => rfl
  | inr q =>
    by_cases hqu : q = u
    · simp [prefixImpl, hqu]
    · simp [prefixImpl, hqu, h q hqu]

/-- An arbitrary adaptive oracle program, including all its random choices and
every observed response before querying u, has identical prefix distribution
under tables that differ only at u. No nonadaptive-query hypothesis is used. -/
theorem prefixRun_eq_of_eq_off {α : Type} (u : Query)
    (table table' : Query → BitVec hashBits) (oa : OracleComp Spec α)
    (h : ∀ q, q ≠ u → table q = table' q) :
    prefixRun u table oa = prefixRun u table' oa := by
  unfold prefixRun
  rw [prefixImpl_eq_of_eq_off u table table' h]

theorem prefixRun_update {α : Type} (u : Query) (table : Query → BitVec hashBits)
    (oa : OracleComp Spec α) (y : BitVec hashBits) :
    prefixRun u (Function.update table u y) oa = prefixRun u table oa := by
  apply prefixRun_eq_of_eq_off
  intro q hqu
  exact Function.update_of_ne hqu _ _

/-- Any event about the full public prefix, including a chosen adaptive stopping
trace, supplies evidence whose likelihood is independent of the hidden answer. -/
theorem prefix_event_update {α : Type} (u : Query) (table : Query → BitVec hashBits)
    (oa : OracleComp Spec α) (event : Option α × PublicTrace → Prop)
    (y : BitVec hashBits) :
    E (prefixRun u (Function.update table u y) oa)
        (fun t => if event t then 1 else 0) =
      E (prefixRun u table oa) (fun t => if event t then 1 else 0) := by
  rw [prefixRun_update]

#print axioms prefixRun_eq_of_eq_off
#print axioms prefixRun_update
#print axioms prefix_event_update

end
end WeightedReplacement
