import Submissions.UpperCompressions.ClippedDrift

/-! Exact class-count moments. A fresh rejected index query advances q while
leaving class counts unchanged. Cached/non-index queries leave both unchanged.
No actual random-oracle distribution is assumed from these finite identities. -/

noncomputable section
open scoped BigOperators
namespace WeightedRow.Weights

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (w : WeightedRow.Weights ι)

/-- Weighted unordered collision-pair count. -/
def pairScore (k : ι → ℕ) : ℝ := ∑ i, (Nat.choose (k i) 2 : ℝ)*w.g i/w.p i

def advance (k : ι → ℕ) : Option ι → (ι → ℕ)
  | none => k
  | some i => bump k i

def scoreJump : Option ι → ℝ
  | none => 0
  | some i => w.g i

def pairJump (k : ι → ℕ) : Option ι → ℝ
  | none => 0
  | some i => (k i : ℝ)*w.g i/w.p i

private theorem sum_update_delta (f f' : ι → ℝ) (i : ι)
    (h : ∀ j, j ≠ i → f' j = f j) :
    (∑ j, f' j) = (∑ j, f j)+(f' i-f i) := by
  have he : f' = fun j => f j + if j=i then f' i-f i else 0 := by
    funext j
    by_cases hj : j=i
    · subst j; simp
    · simp [hj, h j hj]
  rw [he, Finset.sum_add_distrib]
  simp

theorem score_bump (k : ι → ℕ) (i : ι) : w.score (bump k i) = w.score k+w.g i := by
  unfold score
  rw [sum_update_delta (fun j => (k j:ℝ)*w.g j)
    (fun j => (bump k i j:ℝ)*w.g j) i
    (by intro j hj; simp [bump, Function.update_of_ne hj])]
  simp only [bump, Function.update_self, Nat.cast_add, Nat.cast_one]
  ring

theorem pairScore_bump (k : ι → ℕ) (i : ι) :
    w.pairScore (bump k i) = w.pairScore k+(k i:ℝ)*w.g i/w.p i := by
  unfold pairScore
  rw [sum_update_delta (fun j => (Nat.choose (k j) 2:ℝ)*w.g j/w.p j)
    (fun j => (Nat.choose (bump k i j) 2:ℝ)*w.g j/w.p j) i
    (by intro j hj; simp [bump, Function.update_of_ne hj])]
  have hc : Nat.choose (k i+1) 2 = Nat.choose (k i) 2+k i := by
    simpa [Nat.choose_one_right, add_comm] using Nat.choose_succ_succ (k i) 1
  simp only [bump, Function.update_self, hc, Nat.cast_add]
  ring

@[simp] theorem score_advance (k : ι → ℕ) (x : Option ι) :
    w.score (advance k x) = w.score k+w.scoreJump x := by
  cases x <;> simp [advance, scoreJump, score_bump]

@[simp] theorem pairScore_advance (k : ι → ℕ) (x : Option ι) :
    w.pairScore (advance k x) = w.pairScore k+w.pairJump k x := by
  cases x <;> simp [advance, pairJump, pairScore_bump]

@[simp] theorem mean_scoreJump : w.expect w.scoreJump = w.mean := by
  simp [expect, scoreJump, mean]

@[simp] theorem mean_pairJump (k : ι → ℕ) : w.expect (w.pairJump k) = w.score k := by
  simp only [expect, pairJump, mul_zero, zero_add, score]
  apply Finset.sum_congr rfl
  intro i _
  field_simp [(w.p_pos i).ne']

/-- Direct fresh-query expected score increment. -/
theorem score_drift (k : ι → ℕ) :
    w.expect (fun x => w.score (advance k x)-w.score k) = w.mean := by
  simp only [score_advance, add_sub_cancel_left]
  exact w.mean_scoreJump

/-- Direct fresh-query expected pair-energy increment. -/
theorem pair_drift (k : ι → ℕ) :
    w.expect (fun x => w.pairScore (advance k x)-w.pairScore k) = w.score k := by
  simp only [pairScore_advance, add_sub_cancel_left]
  exact w.mean_pairJump k

theorem scoreJump_bounds (G : ℝ) (hG : 0 ≤ G) (hg : ∀ i, w.g i ≤ G)
    (x : Option ι) : 0 ≤ w.scoreJump x ∧ w.scoreJump x ≤ G := by
  cases x with
  | none => exact ⟨le_rfl, hG⟩
  | some i => exact ⟨w.g_nonneg i, hg i⟩

/-- Variance-sensitive one-query bound, retaining the rejection atom. -/
theorem score_variance_le (G : ℝ) (hG : 0 ≤ G) (hg : ∀ i, w.g i ≤ G) :
    w.expect (fun x => (w.scoreJump x-w.mean)^2) ≤ G*w.mean := by
  simpa only [mean_scoreJump] using
    w.centered_variance_le w.scoreJump G (w.scoreJump_bounds G hG hg)

/-- Centered weighted score after q distinct fresh index queries. -/
def M1 (q : ℕ) (k : ι → ℕ) : ℝ := w.score k-w.mean*(q:ℝ)

/-- Pair-energy martingale; q counts fresh rejected index queries too. -/
def M2 (q : ℕ) (k : ι → ℕ) : ℝ :=
  w.pairScore k-(q:ℝ)*w.score k+w.mean*(q:ℝ)*((q:ℝ)+1)/2

theorem M1_increment (q : ℕ) (k : ι → ℕ) (x : Option ι) :
    w.M1 (q+1) (advance k x) = w.M1 q k+(w.scoreJump x-w.mean) := by
  simp only [M1, score_advance, Nat.cast_add, Nat.cast_one]
  ring

theorem M2_increment (q : ℕ) (k : ι → ℕ) (x : Option ι) :
    w.M2 (q+1) (advance k x) = w.M2 q k+
      (w.pairJump k x-w.score k)-((q:ℝ)+1)*(w.scoreJump x-w.mean) := by
  simp only [M2, score_advance, pairScore_advance, Nat.cast_add, Nat.cast_one]
  ring

/-- Exact conditional martingale equality for the weighted score. -/
theorem M1_mean_next (q : ℕ) (k : ι → ℕ) :
    w.expect (fun x => w.M1 (q+1) (advance k x)) = w.M1 q k := by
  simp_rw [M1_increment]
  rw [expect_add, expect_const, expect_sub, mean_scoreJump, expect_const]
  ring

/-- Exact conditional martingale equality for pair energy. -/
theorem M2_mean_next (q : ℕ) (k : ι → ℕ) :
    w.expect (fun x => w.M2 (q+1) (advance k x)) = w.M2 q k := by
  simp_rw [M2_increment]
  rw [expect_sub, expect_add, expect_const, expect_sub, mean_pairJump,
    expect_const, expect_smul, expect_sub, mean_scoreJump, expect_const]
  ring

/-- Predictable quadratic-variation bound, with no independence assumption
between the current score and the history that determined q or k. -/
theorem M1_square_next_le (G : ℝ) (hG : 0 ≤ G) (hg : ∀ i, w.g i ≤ G)
    (q : ℕ) (k : ι → ℕ) :
    w.expect (fun x => (w.M1 (q+1) (advance k x))^2) ≤ (w.M1 q k)^2+G*w.mean := by
  have hz : w.expect (fun x => w.scoreJump x-w.mean) = 0 := by
    rw [expect_sub, mean_scoreJump, expect_const, sub_self]
  have heq : (fun x => (w.M1 (q+1) (advance k x))^2) =
      (fun x => (w.M1 q k)^2+(2*w.M1 q k)*(w.scoreJump x-w.mean)+(w.scoreJump x-w.mean)^2) := by
    funext x
    rw [M1_increment]
    ring
  rw [heq, expect_add, expect_add, expect_const, expect_smul, hz, mul_zero, add_zero]
  exact add_le_add le_rfl (w.score_variance_le G hG hg)

/-- The square minus G*h times the fresh-query counter has nonpositive drift. -/
theorem M1_compensated_square_next_le (G : ℝ) (hG : 0 ≤ G) (hg : ∀ i, w.g i ≤ G)
    (q : ℕ) (k : ι → ℕ) :
    w.expect (fun x => (w.M1 (q+1) (advance k x))^2-G*w.mean*((q+1:ℕ):ℝ)) ≤
      (w.M1 q k)^2-G*w.mean*(q:ℝ) := by
  rw [expect_sub, expect_const]
  have hx := w.M1_square_next_le G hG hg q k
  push_cast
  linarith

/-- The rejected class carries the remaining probability mass. -/
def classMass : Option ι → ℝ
  | none => 1-∑ i, w.p i
  | some i => w.p i

/-- Exact decoder law from finite answer-fiber probabilities. This applies to
uniform 256-bit oracle answers once the concrete decoder fibers are supplied. -/
theorem uniform_decoder_expect {β : Type*} [Fintype β] [Nonempty β]
    (decode : β → Option ι)
    (hfiber : ∀ x : Option ι,
      ((Finset.univ.filter (fun b => decode b=x)).card:ℝ)/(Fintype.card β:ℝ) = w.classMass x)
    (f : Option ι → ℝ) :
    (∑ b : β, f (decode b))/(Fintype.card β:ℝ) = w.expect f := by
  have hp := Finset.sum_fiberwise' (Finset.univ : Finset β) decode f
  simp only [Finset.sum_const, nsmul_eq_mul] at hp
  calc
    (∑ b : β, f (decode b))/(Fintype.card β:ℝ) =
        (∑ x : Option ι, ((Finset.univ.filter (fun b => decode b=x)).card:ℝ)*f x)/
          (Fintype.card β:ℝ) := by rw [hp]
    _ = ∑ x : Option ι,
        (((Finset.univ.filter (fun b => decode b=x)).card:ℝ)/(Fintype.card β:ℝ))*f x := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro x _
      ring
    _ = ∑ x : Option ι, w.classMass x*f x := by simp_rw [hfiber]
    _ = w.expect f := by rw [Fintype.sum_option]; rfl

/-- A fresh-query flag separates index observations from cached or unrelated
queries. The latter preserve all weighted statistics and the fresh counter. -/
def step (fresh : Bool) (q : ℕ) (k : ι → ℕ) (x : Option ι) : ℕ × (ι → ℕ) :=
  if fresh then (q+1, advance k x) else (q,k)

@[simp] theorem step_not_fresh (q : ℕ) (k : ι → ℕ) (x : Option ι) :
    step false q k x = (q,k) := rfl

theorem M1_step_mean (fresh : Bool) (q : ℕ) (k : ι → ℕ) :
    w.expect (fun x => w.M1 (step fresh q k x).1 (step fresh q k x).2) = w.M1 q k := by
  cases fresh
  · simp only [step_not_fresh, expect_const]
  · exact w.M1_mean_next q k

theorem M2_step_mean (fresh : Bool) (q : ℕ) (k : ι → ℕ) :
    w.expect (fun x => w.M2 (step fresh q k x).1 (step fresh q k x).2) = w.M2 q k := by
  cases fresh
  · simp only [step_not_fresh, expect_const]
  · exact w.M2_mean_next q k

theorem M1_step_square_compensated (fresh : Bool) (G : ℝ)
    (hG : 0 ≤ G) (hg : ∀ i, w.g i ≤ G) (q : ℕ) (k : ι → ℕ) :
    w.expect (fun x =>
      (w.M1 (step fresh q k x).1 (step fresh q k x).2)^2-G*w.mean*((step fresh q k x).1:ℝ)) ≤
        (w.M1 q k)^2-G*w.mean*(q:ℝ) := by
  cases fresh
  · simp only [step_not_fresh, expect_const, le_refl]
  · exact w.M1_compensated_square_next_le G hG hg q k

#print axioms score_bump
#print axioms pairScore_bump
#print axioms score_drift
#print axioms pair_drift
#print axioms score_variance_le
#print axioms M1_mean_next
#print axioms M2_mean_next
#print axioms M1_square_next_le
#print axioms M1_compensated_square_next_le
#print axioms uniform_decoder_expect
#print axioms M1_step_mean
#print axioms M2_step_mean
#print axioms M1_step_square_compensated

end WeightedRow.Weights

namespace WeightedPublicCounts
open WeightedRow.Weights
open scoped BigOperators
variable {Q ι : Type*} [DecidableEq Q] [Fintype ι] [DecidableEq ι]

/-- Multiplicities count distinct public index inputs, not repeated queries. -/
def counts (A : Finset Q) (answers : Q → Option ι) (i : ι) : ℕ :=
  (A.filter (fun q => answers q=some i)).card

theorem counts_insert_apply (A : Finset Q) (answers : Q → Option ι)
    (q : Q) (hq : q ∉ A) (i : ι) :
    counts (insert q A) answers i = counts A answers i + if answers q=some i then 1 else 0 := by
  by_cases hi : answers q=some i
  · simp [counts, Finset.filter_insert, hi, hq, add_comm]
  · simp [counts, Finset.filter_insert, hi]

theorem counts_insert (A : Finset Q) (answers : Q → Option ι)
    (q : Q) (hq : q ∉ A) :
    counts (insert q A) answers = advance (counts A answers) (answers q) := by
  cases he : answers q with
  | none =>
    funext i
    simp [counts_insert_apply, hq, he, advance]
  | some j =>
    funext i
    by_cases hij : i=j
    · subst i
      simp [counts_insert_apply, hq, he, advance, bump]
    · simp [counts_insert_apply, hq, he, advance, bump, Function.update_of_ne hij, hij, Ne.symm hij]

theorem counts_update_absent (A : Finset Q) (answers : Q → Option ι)
    (q : Q) (hq : q ∉ A) (x : Option ι) :
    counts A (Function.update answers q x) = counts A answers := by
  funext i
  unfold counts
  congr 1
  apply Finset.filter_congr
  intro r hr
  have hrq : r ≠ q := by intro he; subst r; exact hq hr
  simp [Function.update_of_ne hrq]

/-- The exact count update after exposing one previously absent index input. -/
theorem counts_insert_update (A : Finset Q) (answers : Q → Option ι)
    (q : Q) (hq : q ∉ A) (x : Option ι) :
    counts (insert q A) (Function.update answers q x) = advance (counts A answers) x := by
  rw [counts_insert _ _ _ hq, Function.update_self, counts_update_absent _ _ _ hq]

/-- Repeating a public query with the same cached answer changes no count. -/
theorem counts_cached (A : Finset Q) (answers : Q → Option ι) (q : Q) (hq : q ∈ A) :
    counts (insert q A) answers = counts A answers := by rw [Finset.insert_eq_of_mem hq]

#print axioms counts_insert_update
#print axioms counts_cached
end WeightedPublicCounts
