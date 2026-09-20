import Submissions.UpperCompressions.ReplacementPrefixReserve

/-! Expected spent public-prefix cost plus its actual post-reserve remaining
budget fits in one initial public budget, without ENNReal subtraction. -/
open OracleSpec OracleComp OracleComp.EvalDist ENNReal
open OptimalOTS
namespace WeightedReplacement
noncomputable section
open scoped Classical

theorem expected_spent_reserved_remaining_le {α β : Type} (oa : OracleComp Spec α)
    (k : α → OracleComp Spec β) (R : ℕ)
    (hR : ∀ a b, CostAtMost (k a) b → R ≤ b) :
    ∀ c b, CostAtMost (oa >>= k) b →
      expectedCharge (fun t => queryCost t) oa c +
        E (runRemaining oa c b) (fun r => ((r.2.2-R:ℕ):ℝ≥0∞)) ≤ (b-R:ℕ) := by
  induction oa using OracleComp.inductionOn with
  | pure a => intro c b hB; simp
  | query_bind t f ih =>
    intro c b hB
    have hprefix := (costAtMost_prefix_reserved (liftM (Spec.query t) >>= f) k R hR b hB).2
    rw [costAtMost_query_bind_iff] at hprefix
    rw [bind_assoc,costAtMost_query_bind_iff] at hB
    rw [expectedCharge_query,runRemaining_query,E_bind]
    calc
      _ = (queryCost t:ℝ≥0∞) + E ((oracleImpl t).run c) (fun p =>
          expectedCharge (fun t => queryCost t) (f p.1) p.2 +
            E (runRemaining (f p.1) p.2 (b-queryCost t)) (fun r => ((r.2.2-R:ℕ):ℝ≥0∞))) := by
        rw [add_assoc]
        exact congrArg ((queryCost t:ℝ≥0∞) + ·) (expectedValue_add _ _ _).symm
      _ ≤ (queryCost t:ℝ≥0∞) + E ((oracleImpl t).run c)
          (fun _ => ((b-queryCost t-R:ℕ):ℝ≥0∞)) :=
        add_le_add le_rfl (E_mono _ (fun p => ih p.1 p.2 _ (hB.2 p.1)))
      _ ≤ (queryCost t:ℝ≥0∞) + ((b-queryCost t-R:ℕ):ℝ≥0∞) :=
        add_le_add le_rfl (E_const_le _ _)
      _ = _ := by
        rw [← Nat.cast_add]
        congr 1
        omega

#print axioms expected_spent_reserved_remaining_le
end
end WeightedReplacement
