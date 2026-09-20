import Submissions.UpperCompressions.WeightedMoments

/-! Deterministic domination of the cached-replay hazard by the global first
and collision-pair scores. No random-oracle or stopping hypotheses are used. -/
noncomputable section
namespace WeightedRow.Weights
variable {ι : Type*} [Fintype ι] [DecidableEq ι] (w : Weights ι)

theorem nat_le_twice_choose_two (n : ℕ) (hn : 2 ≤ n) : n ≤ 2*n.choose 2 := by
  induction n with
  | zero => omega
  | succ n ih =>
    have he : (n+1).choose 2=n.choose 2+n := by
      simpa [Nat.choose_one_right,add_comm] using Nat.choose_succ_succ n 1
    rw [he]
    by_cases h : 2 ≤ n
    · have := ih h
      omega
    · have : n=1 := by omega
      subst n
      decide

theorem seen_nonneg (k : ι → ℕ) : 0 ≤ w.seen k := by
  unfold seen
  exact Finset.sum_nonneg fun i _ => by split_ifs <;> first | exact le_rfl | exact w.g_nonneg i

theorem seen_le_score (k : ι → ℕ) : w.seen k ≤ w.score k := by
  unfold seen score
  apply Finset.sum_le_sum
  intro i hi
  by_cases h : k i=0
  · simp [h]
  · rw [if_neg h]
    have hk : (1:ℝ) ≤ k i := by exact_mod_cast (show 1 ≤ k i by omega)
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hk (w.g_nonneg i)

theorem bad_le_twice_pairScore (k row : ι → ℕ) (hr : ∀ i,row i ≤ k i) :
    w.bad k row ≤ 2*w.pairScore k := by
  unfold bad pairScore
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  by_cases hk : 2 ≤ k i
  · rw [if_pos hk]
    have hkn : row i ≤ 2*(k i).choose 2 := (hr i).trans (nat_le_twice_choose_two _ hk)
    have hkr : (row i:ℝ) ≤ 2*((k i).choose 2:ℝ) := by exact_mod_cast hkn
    have hx := mul_le_mul_of_nonneg_right hkr
      (div_nonneg (w.g_nonneg i) (w.p_pos i).le)
    convert hx using 1 <;> ring
  · rw [if_neg hk]
    exact mul_nonneg (by norm_num)
      (div_nonneg (mul_nonneg (Nat.cast_nonneg _) (w.g_nonneg i)) (w.p_pos i).le)

theorem hazard_le_score_pair (N : ℝ) (hN : 0 < N) (r : ℕ)
    (k row : ι → ℕ) (hr : ∀ i,row i ≤ k i) :
    w.hazard N r k row ≤ w.score k+2*w.pairScore k/N := by
  have hc : 1-(r:ℝ)/N ≤ 1 := sub_le_self _ (div_nonneg (Nat.cast_nonneg _) hN.le)
  have hseen := mul_le_mul_of_nonneg_right hc (w.seen_nonneg k)
  have hbad := div_le_div_of_nonneg_right (w.bad_le_twice_pairScore k row hr) hN.le
  unfold hazard
  have hs := w.seen_le_score k
  nlinarith

#print axioms hazard_le_score_pair
end WeightedRow.Weights
