import Submissions.UpperCompressions.WeightedCompletion
import Submissions.UpperCompressions.ReplacementProgram

/-! Exact weighted-payoff law for the actual first-minimum selector.
The whole nonce list is processed, ties retain the first occurrence. -/
noncomputable section
open scoped BigOperators Classical
namespace WeightedCompletion
open WeightedReplacement OptimalOTS.WeightedSampling
variable {D I : Type} [Fintype D] [Nonempty D] [DecidableEq D] [DecidableEq I]

def selected (table : D → Option I) (tier : I → ℕ) (xs : List D) : Option (D × I) :=
  select (fun p => tier p.2) (xs.map fun a => (fun i => (a,i)) <$> table a)

theorem selected_consistent (table : D → Option I) (tier : I → ℕ) (xs : List D)
    (a : D) (i : I) (h : selected table tier xs = some (a,i)) : table a = some i := by
  have hm := select_source (fun p : D × I => tier p.2) _ (a,i) h
  obtain ⟨b, _, hb⟩ := List.mem_map.mp hm
  change (table b).map (fun i => (b,i)) = some (a,i) at hb
  rw [Option.map_eq_some_iff] at hb
  obtain ⟨j, hj, hji⟩ := hb
  obtain ⟨hab, hij⟩ := Prod.mk.inj hji
  cases hab
  cases hij
  exact hj

theorem selected_score_expand (table : D → Option I) (tier : I → ℕ)
    (f : D → I → ℝ) (xs : List D) :
    score (selected table tier xs) (fun p => f p.1 p.2) =
      ∑ a : D, score (table a) (fun i => if selected table tier xs = some (a,i) then f a i else 0) := by
  cases hs : selected table tier xs with
  | none =>
    simp only [score, Option.map_none, Option.getD_none]
    apply Eq.symm
    apply Finset.sum_eq_zero
    intro a _
    cases table a <;> simp [score, hs]
  | some r =>
    obtain ⟨a,i⟩ := r
    have ht := selected_consistent table tier xs a i hs
    rw [Finset.sum_eq_single a]
    · simp [score, ht, hs]
    · intro b _ hba
      cases table b with
      | none => simp [score]
      | some j =>
        have hn : (a,i) ≠ (b,j) := fun he => hba (congrArg Prod.fst he).symm
        simp [score, hs, hn, Ne.symm hba]
    · simp

theorem iidMean_sum {ι : Type} (s : Finset ι) (f : ι → List D → ℝ) (n : ℕ) :
    iidMean n (fun xs => ∑ i ∈ s, f i xs) = ∑ i ∈ s, iidMean n (f i) := by
  induction n generalizing f with
  | zero => rfl
  | succ n ih =>
    change uniformMean (fun a => iidMean n (fun xs => ∑ i ∈ s, f i (a::xs))) = _
    simp only [ih]
    rw [mean_sum]
    rfl

theorem iidMean_mul_const (f : List D → ℝ) (c : ℝ) (n : ℕ) :
    iidMean n (fun xs => f xs*c) = iidMean n f*c := by
  induction n generalizing f with
  | zero => rfl
  | succ n ih =>
    change uniformMean (fun a => iidMean n (fun xs => f (a::xs)*c)) = _
    simp only [ih]
    rw [uniformMean_mul_const]
    rfl

theorem iidMean_const (c : ℝ) (n : ℕ) : iidMean n (fun _ : List D => c) = c := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change uniformMean (fun _ : D => iidMean n (fun _ : List D => c)) = c
    rw [ih, uniformMean_const]

theorem iidMean_mono (f g : List D → ℝ) (h : ∀ xs, f xs ≤ g xs) (n : ℕ) :
    iidMean n f ≤ iidMean n g := by
  induction n generalizing f g with
  | zero => exact h []
  | succ n ih =>
    apply uniformMean_mono
    intro a
    exact ih _ _ (fun xs => h (a::xs))

def tableKernel (n : ℕ) (table : D → Option I) (tier : I → ℕ) (f : D → I → ℝ) : ℝ :=
  (∑ a : D, score (table a) (fun i => kernel n
    (fraction (weakRank tier i ∘ table)) (fraction (strictRank tier i ∘ table)) * f a i)) /
      Fintype.card D

/-- Exact expectation, for arbitrary real scores, under iid nonce draws. -/
theorem iid_selected_score (n : ℕ) (table : D → Option I) (tier : I → ℕ)
    (f : D → I → ℝ) :
    iidMean n (fun xs => score (selected table tier xs) (fun p => f p.1 p.2)) =
      tableKernel n table tier f := by
  simp only [selected_score_expand]
  rw [iidMean_sum]
  unfold tableKernel
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro a _
  cases ht : table a with
  | none => simp [score, ht, iidMean_const]
  | some i =>
    simp only [score, ht, Option.map_some, Option.getD_some]
    have he : (fun xs => if selected table tier xs = some (a,i) then f a i else 0) =
        fun xs => (if selected table tier xs = some (a,i) then 1 else 0)*f a i := by
      funext xs
      split_ifs <;> simp
    rw [he, iidMean_mul_const]
    have hp := iid_tagged_table_probability table tier a i ht n
    have hp' : iidMean n (fun xs => if selected table tier xs = some (a,i) then 1 else 0) =
        kernel n (fraction (weakRank tier i ∘ table))
          (fraction (strictRank tier i ∘ table)) / Fintype.card D := by
      convert hp using 1
      congr 1
      funext xs
      unfold selected
      split_ifs <;> rfl
    rw [hp']
    ring

theorem tableKernel_le (n : ℕ) (table : D → Option I) (tier : I → ℕ)
    (f : D → I → ℝ) (C : ℝ) (hC : 0 ≤ C) (hf : ∀ a i, f a i ≤ C) :
    tableKernel n table tier f ≤ C := by
  rw [← iid_selected_score]
  apply le_trans (iidMean_mono _ (fun _ => C) ?_ n) (iidMean_const C n).le
  intro xs
  cases selected table tier xs with
  | none => exact hC
  | some r => exact hf r.1 r.2

end WeightedCompletion
#print axioms WeightedCompletion.iid_selected_score
#print axioms WeightedCompletion.tableKernel_le
