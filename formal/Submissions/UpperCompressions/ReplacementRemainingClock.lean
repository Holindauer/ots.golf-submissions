import Submissions.UpperCompressions.ReplacementPublicCost
import Submissions.UpperCompressions.Master

/-! Retain the actual pathwise remaining budget alongside the original shared
cache interpreter, without requiring a finite adversary state space. -/
open OracleSpec OracleComp OracleComp.EvalDist ENNReal
open OptimalOTS
namespace WeightedReplacement
noncomputable section
open scoped Classical

def runRemaining {α : Type} (oa : OracleComp Spec α) : Cache → ℕ → ProbComp (α × Cache × ℕ) :=
  OracleComp.construct (fun a c b => pure (a,c,b))
    (fun t _ rec c b => do
      let r ← (oracleImpl t).run c
      rec r.1 r.2 (b-queryCost t)) oa

@[simp] theorem runRemaining_pure {α : Type} (a : α) (c : Cache) (b : ℕ) :
    runRemaining (pure a) c b = pure (a,c,b) := by simp [runRemaining]

theorem runRemaining_query {α : Type} (t : Spec.Domain)
    (k : Spec.Range t → OracleComp Spec α) (c : Cache) (b : ℕ) :
    runRemaining (liftM (Spec.query t) >>= k) c b =
      (oracleImpl t).run c >>= fun r => runRemaining (k r.1) r.2 (b-queryCost t) := by
  simp [runRemaining]

theorem runRemaining_project {α : Type} (oa : OracleComp Spec α) (c : Cache) (b : ℕ) :
    (fun r : α × Cache × ℕ => (r.1,r.2.1)) <$> runRemaining oa c b = run oa c := by
  induction oa using OracleComp.inductionOn generalizing c b with
  | pure a => simp [run_pure]
  | query_bind t k ih =>
    rw [runRemaining_query,run_query_bind,map_bind]
    exact bind_congr fun r => ih r.1 r.2 _

/-- All members of the continuation family inherit the same pathwise remaining
budget after every supported actual first-stage execution. -/
theorem runRemaining_family_support {α β J : Type} [Nonempty J]
    (oa : OracleComp Spec α) (k : J → α → OracleComp Spec β) :
    ∀ c b, (∀ j, CostAtMost (oa >>= k j) b) →
      ∀ r ∈ support (runRemaining oa c b),
        r.2.2 ≤ b ∧ ∀ j, CostAtMost (k j r.1) r.2.2 := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro c b hB r hr
    rw [runRemaining_pure,support_pure,Set.mem_singleton_iff] at hr
    subst r
    exact ⟨le_rfl,fun j => by simpa only [pure_bind] using hB j⟩
  | query_bind t f ih =>
    intro c b hB r hr
    have hB' : ∀ a j, CostAtMost (f a >>= k j) (b-queryCost t) := by
      intro a j
      have h := hB j
      rw [bind_assoc,costAtMost_query_bind_iff] at h
      exact h.2 a
    rw [runRemaining_query,support_bind] at hr
    simp only [Set.mem_iUnion] at hr
    obtain ⟨p,_,hr⟩ := hr
    obtain ⟨hle,hk⟩ := ih p.1 p.2 _ (hB' p.1) r hr
    exact ⟨hle.trans (Nat.sub_le _ _),hk⟩

/-- The expected spent query cost and expected remaining budget share the
original budget. This is useful when averaging a continuation-rate bound. -/
theorem expected_spent_remaining_le {α β J : Type} [Nonempty J]
    (oa : OracleComp Spec α) (k : J → α → OracleComp Spec β) :
    ∀ c b, (∀ j, CostAtMost (oa >>= k j) b) →
      expectedCharge (fun t => queryCost t) oa c +
        E (runRemaining oa c b) (fun r => (r.2.2:ℝ≥0∞)) ≤ b := by
  induction oa using OracleComp.inductionOn with
  | pure a => intro c b hB; simp [E_pure]
  | query_bind t f ih =>
    intro c b hB
    have hh := hB (Classical.arbitrary J)
    rw [bind_assoc,costAtMost_query_bind_iff] at hh
    have hB' : ∀ a j, CostAtMost (f a >>= k j) (b-queryCost t) := by
      intro a j
      have h := hB j
      rw [bind_assoc,costAtMost_query_bind_iff] at h
      exact h.2 a
    rw [expectedCharge_query,runRemaining_query,E_bind]
    calc
      _ = (queryCost t:ℝ≥0∞) + E ((oracleImpl t).run c) (fun p =>
          expectedCharge (fun t => queryCost t) (f p.1) p.2 +
            E (runRemaining (f p.1) p.2 (b-queryCost t)) (fun r => (r.2.2:ℝ≥0∞))) := by
        rw [add_assoc]
        exact congrArg ((queryCost t:ℝ≥0∞) + ·) (expectedValue_add _ _ _).symm
      _ ≤ (queryCost t:ℝ≥0∞) + E ((oracleImpl t).run c)
          (fun _ => ((b-queryCost t:ℕ):ℝ≥0∞)) :=
        add_le_add le_rfl (E_mono _ (fun p => ih p.1 p.2 _ (hB' p.1)))
      _ ≤ (queryCost t:ℝ≥0∞) + ((b-queryCost t:ℕ):ℝ≥0∞) :=
        add_le_add le_rfl (E_const_le _ _)
      _ = _ := by rw [← Nat.cast_add,Nat.add_sub_of_le hh.1]

#print axioms runRemaining_project
#print axioms runRemaining_family_support
#print axioms expected_spent_remaining_le
end
end WeightedReplacement
