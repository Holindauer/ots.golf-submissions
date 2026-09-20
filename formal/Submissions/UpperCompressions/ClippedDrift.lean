import Mathlib

/-! One-query algebra for the clipped row hazard of weighted index sampling.
This is a finite-distribution theorem. It does not formalize signing, the
random-oracle experiment, concentration, or any signature-security claim. -/

noncomputable section

open scoped BigOperators
namespace WeightedRow

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

structure Weights (ι : Type*) [Fintype ι] where
  p : ι → ℝ
  g : ι → ℝ
  p_pos : ∀ i, 0 < p i
  g_nonneg : ∀ i, 0 ≤ g i
  mass_le_one : ∑ i, p i ≤ 1

namespace Weights

variable (w : Weights ι)

/-- Add one observed accepted class. Rejection changes no class count. -/
def bump (k : ι → ℕ) (i : ι) : ι → ℕ := Function.update k i (k i + 1)

def seen (k : ι → ℕ) : ℝ := ∑ i, if k i = 0 then 0 else w.g i

def bad (k row : ι → ℕ) : ℝ :=
  ∑ i, if 2 ≤ k i then (row i : ℝ) * w.g i / w.p i else 0

def score (row : ι → ℕ) : ℝ := ∑ i, (row i : ℝ) * w.g i

def singleton (k row : ι → ℕ) : ℝ :=
  ∑ i, if k i = 1 then (row i : ℝ) * w.g i else 0

def mean : ℝ := ∑ i, w.p i * w.g i

def unseenMean (k : ι → ℕ) : ℝ := ∑ i, if k i = 0 then w.p i * w.g i else 0

/-- `r` includes rejected positions in the distinguished row. -/
def hazard (N : ℝ) (r : ℕ) (k row : ι → ℕ) : ℝ :=
  (1 - (r : ℝ) / N) * w.seen k + w.bad k row / N

/-- Expectation over one oracle output, including the rejected-output atom. -/
def expect (f : Option ι → ℝ) : ℝ :=
  (1 - ∑ i, w.p i) * f none + ∑ i, w.p i * f (some i)

private theorem sum_change (f f' : ι → ℝ) (i : ι)
    (h : ∀ j, j ≠ i → f' j = f j) :
    (∑ j, f' j) = (∑ j, f j) + (f' i - f i) := by
  have he : f' = fun j => f j + if j = i then f' i - f i else 0 := by
    funext j
    by_cases hj : j = i
    · subst j; simp
    · simp [hj, h j hj]
  rw [he, Finset.sum_add_distrib]
  simp

@[simp] theorem seen_bump (k : ι → ℕ) (i : ι) :
    w.seen (bump k i) = w.seen k + if k i = 0 then w.g i else 0 := by
  unfold seen
  rw [sum_change (fun j => if k j = 0 then 0 else w.g j)
    (fun j => if bump k i j = 0 then 0 else w.g j) i
    (by intro j hj; simp [bump, Function.update_of_ne hj])]
  simp [bump]
  split_ifs <;> ring

theorem bad_bump_outside (k row : ι → ℕ) (i : ι) :
    w.bad (bump k i) row = w.bad k row +
      if k i = 1 then (row i : ℝ) * w.g i / w.p i else 0 := by
  unfold bad
  rw [sum_change (fun j => if 2 ≤ k j then (row j : ℝ) * w.g j / w.p j else 0)
    (fun j => if 2 ≤ bump k i j then (row j : ℝ) * w.g j / w.p j else 0) i
    (by intro j hj; simp [bump, Function.update_of_ne hj])]
  simp only [bump, Function.update_self]
  by_cases h0 : k i = 0
  · simp [h0]
  · by_cases h1 : k i = 1
    · simp [h1]
    · have h2 : 2 ≤ k i := by omega
      have h3 : 2 ≤ k i + 1 := by omega
      simp [h1, h2, h3]

theorem bad_bump_inside (k row : ι → ℕ) (i : ι) :
    w.bad (bump k i) (bump row i) = w.bad k row +
      (if k i = 0 then 0 else w.g i / w.p i) +
      (if k i = 1 then (row i : ℝ) * w.g i / w.p i else 0) := by
  unfold bad
  rw [sum_change (fun j => if 2 ≤ k j then (row j : ℝ) * w.g j / w.p j else 0)
    (fun j => if 2 ≤ bump k i j then (bump row i j : ℝ) * w.g j / w.p j else 0) i
    (by intro j hj; simp [bump, Function.update_of_ne hj])]
  simp only [bump, Function.update_self, Nat.cast_add, Nat.cast_one]
  by_cases h0 : k i = 0
  · simp [h0]
  · by_cases h1 : k i = 1
    · simp [h1]
      ring
    · have h2 : 2 ≤ k i := by omega
      have h3 : 2 ≤ k i + 1 := by omega
      simp [h0, h1, h2, h3]
      ring

private theorem avg_new (k : ι → ℕ) :
    (∑ i, w.p i * (if k i = 0 then w.g i else 0)) = w.unseenMean k := by
  unfold unseenMean
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> simp

private theorem avg_old (k : ι → ℕ) :
    (∑ i, w.p i * (if k i = 0 then 0 else w.g i / w.p i)) = w.seen k := by
  unfold seen
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : k i = 0
  · simp [h]
  · simp only [if_neg h]
    field_simp [(w.p_pos i).ne']

private theorem avg_singleton (k row : ι → ℕ) :
    (∑ i, w.p i * (if k i = 1 then (row i : ℝ) * w.g i / w.p i else 0)) =
      w.singleton k row := by
  unfold singleton
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : k i = 1
  · simp only [if_pos h]
    field_simp [(w.p_pos i).ne']
  · simp [h]

/-- Exact change if the accepted query is outside the distinguished row. -/
theorem hazard_change_outside (N : ℝ) (r : ℕ) (k row : ι → ℕ) (i : ι) :
    w.hazard N r (bump k i) row - w.hazard N r k row =
      (1 - (r : ℝ) / N) * (if k i = 0 then w.g i else 0) +
      (if k i = 1 then (row i : ℝ) * w.g i / w.p i else 0) / N := by
  simp only [hazard, seen_bump, bad_bump_outside]
  ring

/-- Exact change if the accepted query is inside the distinguished row. -/
theorem hazard_change_inside (N : ℝ) (r : ℕ) (k row : ι → ℕ) (i : ι) :
    w.hazard N (r + 1) (bump k i) (bump row i) - w.hazard N r k row =
      (1 - ((r : ℝ) + 1) / N) * (if k i = 0 then w.g i else 0) +
      ((if k i = 0 then 0 else w.g i / w.p i) +
       (if k i = 1 then (row i : ℝ) * w.g i / w.p i else 0)) / N -
      w.seen k / N := by
  simp only [hazard, seen_bump, bad_bump_inside, Nat.cast_add, Nat.cast_one]
  ring

/-- A rejected inside-row query only removes one unknown candidate position. -/
theorem hazard_change_rejected (N : ℝ) (r : ℕ) (k row : ι → ℕ) :
    w.hazard N (r + 1) k row - w.hazard N r k row = -w.seen k / N := by
  simp only [hazard, Nat.cast_add, Nat.cast_one]
  ring

/-- Query outside the row; `none` denotes rejection. -/
def afterOutside (N : ℝ) (r : ℕ) (k row : ι → ℕ) : Option ι → ℝ
  | none => w.hazard N r k row
  | some i => w.hazard N r (bump k i) row

/-- Query inside the row; the row position count grows even on rejection. -/
def afterInside (N : ℝ) (r : ℕ) (k row : ι → ℕ) : Option ι → ℝ
  | none => w.hazard N (r + 1) k row
  | some i => w.hazard N (r + 1) (bump k i) (bump row i)

/-- Exact conditional drift for a query outside the row. -/
theorem drift_outside (N : ℝ) (r : ℕ) (k row : ι → ℕ) :
    w.expect (fun x => w.afterOutside N r k row x - w.hazard N r k row) =
      (1 - (r : ℝ) / N) * w.unseenMean k + w.singleton k row / N := by
  simp only [expect, afterOutside, sub_self, mul_zero, zero_add, hazard_change_outside]
  simp only [mul_add, Finset.sum_add_distrib]
  rw [show (∑ i, w.p i * ((1 - (r : ℝ) / N) *
      (if k i = 0 then w.g i else 0))) =
      (1 - (r : ℝ) / N) * ∑ i, w.p i * (if k i = 0 then w.g i else 0) by
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intros; ring]
  rw [avg_new]
  rw [show (∑ i, w.p i * ((if k i = 1 then (row i : ℝ) * w.g i / w.p i else 0) / N)) =
      (∑ i, w.p i * (if k i = 1 then (row i : ℝ) * w.g i / w.p i else 0)) / N by
        rw [Finset.sum_div]; apply Finset.sum_congr rfl; intros; ring]
  rw [avg_singleton]

/-- Exact conditional drift for a query inside the row. The rejection atom
cancels the apparent extra `seen/N` term after averaging. -/
theorem drift_inside (N : ℝ) (r : ℕ) (k row : ι → ℕ) :
    w.expect (fun x => w.afterInside N r k row x - w.hazard N r k row) =
      (1 - ((r : ℝ) + 1) / N) * w.unseenMean k + w.singleton k row / N := by
  simp only [expect, afterInside, hazard_change_rejected, hazard_change_inside]
  simp only [mul_sub, mul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [show (∑ i, w.p i * ((1 - ((r : ℝ) + 1) / N) *
      (if k i = 0 then w.g i else 0))) =
      (1 - ((r : ℝ) + 1) / N) * ∑ i, w.p i * (if k i = 0 then w.g i else 0) by
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intros; ring]
  rw [avg_new]
  have hsum : (∑ i, w.p i *
      ((if k i = 0 then 0 else w.g i / w.p i) +
       (if k i = 1 then (row i : ℝ) * w.g i / w.p i else 0)) / N) =
      (w.seen k + w.singleton k row) / N := by
    rw [← Finset.sum_div]
    simp only [mul_add, Finset.sum_add_distrib]
    rw [avg_old, avg_singleton]
  simp_rw [← mul_div_assoc]
  rw [hsum, ← Finset.sum_div, ← Finset.sum_mul]
  ring


/-- The rejected-output atom is a nonnegative probability. -/
theorem rejection_nonneg : 0 ≤ 1 - ∑ i, w.p i := sub_nonneg.mpr w.mass_le_one

theorem expect_one : w.expect (fun _ => 1) = 1 := by
  simp only [expect, mul_one]
  ring

theorem unseenMean_nonneg (k : ι → ℕ) : 0 ≤ w.unseenMean k := by
  unfold unseenMean
  apply Finset.sum_nonneg
  intro i _
  split_ifs
  · exact mul_nonneg (w.p_pos i).le (w.g_nonneg i)
  · exact le_rfl

theorem unseenMean_le_mean (k : ι → ℕ) : w.unseenMean k ≤ w.mean := by
  unfold unseenMean mean
  apply Finset.sum_le_sum
  intro i _
  split_ifs
  · exact le_rfl
  · exact mul_nonneg (w.p_pos i).le (w.g_nonneg i)

theorem singleton_le_score (k row : ι → ℕ) : w.singleton k row ≤ w.score row := by
  unfold singleton score
  apply Finset.sum_le_sum
  intro i _
  split_ifs
  · exact le_rfl
  · exact mul_nonneg (Nat.cast_nonneg _) (w.g_nonneg i)

/-- A row-score concentration hypothesis controls either drift formula.
The exact drift identities above hold even without count-consistency hypotheses;
in an actual count matrix one also has row_i≤global_i and sum row_i≤r. -/
theorem drift_expression_le (N : ℝ) (hN : 0 < N) (r : ℕ)
    (hr : (r : ℝ) ≤ N) (k row : ι → ℕ) (η κ extra : ℝ)
    (hextra : 0 ≤ extra)
    (hscore : w.score row ≤ (r : ℝ) * w.mean + η * κ * N) :
    (1 - ((r : ℝ) + extra) / N) * w.unseenMean k + w.singleton k row / N ≤
      w.mean + η * κ := by
  have hc : 0 ≤ 1 - (r : ℝ) / N :=
    sub_nonneg.mpr ((div_le_one hN).2 hr)
  have hc' : 1 - ((r : ℝ) + extra) / N ≤ 1 - (r : ℝ) / N := by
    apply sub_le_sub_left
    exact div_le_div_of_nonneg_right (by linarith) hN.le
  calc
    (1 - ((r : ℝ) + extra) / N) * w.unseenMean k + w.singleton k row / N
      ≤ (1 - (r : ℝ) / N) * w.unseenMean k + w.singleton k row / N :=
        add_le_add (mul_le_mul_of_nonneg_right hc' (w.unseenMean_nonneg k)) le_rfl
    _ ≤ (1 - (r : ℝ) / N) * w.mean + w.score row / N :=
        add_le_add (mul_le_mul_of_nonneg_left (w.unseenMean_le_mean k) hc)
          (div_le_div_of_nonneg_right (w.singleton_le_score k row) hN.le)
    _ ≤ (1 - (r : ℝ) / N) * w.mean +
          ((r : ℝ) * w.mean + η * κ * N) / N :=
        add_le_add le_rfl (div_le_div_of_nonneg_right hscore hN.le)
    _ = w.mean + η * κ := by field_simp [hN.ne']; ring

theorem drift_outside_le (N : ℝ) (hN : 0 < N) (r : ℕ)
    (hr : (r : ℝ) ≤ N) (k row : ι → ℕ) (η κ : ℝ)
    (hscore : w.score row ≤ (r : ℝ) * w.mean + η * κ * N) :
    w.expect (fun x => w.afterOutside N r k row x - w.hazard N r k row) ≤
      w.mean + η * κ := by
  rw [drift_outside]
  simpa only [add_zero] using w.drift_expression_le N hN r hr k row η κ 0 le_rfl hscore

theorem drift_inside_le (N : ℝ) (hN : 0 < N) (r : ℕ)
    (hr : (r : ℝ) ≤ N) (k row : ι → ℕ) (η κ : ℝ)
    (hscore : w.score row ≤ (r : ℝ) * w.mean + η * κ * N) :
    w.expect (fun x => w.afterInside N r k row x - w.hazard N r k row) ≤
      w.mean + η * κ := by
  rw [drift_inside]
  exact w.drift_expression_le N hN r hr k row η κ 1 zero_le_one hscore


/-- Nonnegative part of an outside-row increment. -/
def positiveOutside (N : ℝ) (r : ℕ) (k row : ι → ℕ) : Option ι → ℝ
  | none => 0
  | some i =>
      (1 - (r : ℝ) / N) * (if k i = 0 then w.g i else 0) +
      (if k i = 1 then (row i : ℝ) * w.g i / w.p i else 0) / N

/-- Nonnegative part of an inside-row increment; `seen/N` is predictable. -/
def positiveInside (N : ℝ) (r : ℕ) (k row : ι → ℕ) : Option ι → ℝ
  | none => 0
  | some i =>
      (1 - ((r : ℝ) + 1) / N) * (if k i = 0 then w.g i else 0) +
      ((if k i = 0 then 0 else w.g i / w.p i) +
       (if k i = 1 then (row i : ℝ) * w.g i / w.p i else 0)) / N

theorem increment_outside (N : ℝ) (r : ℕ) (k row : ι → ℕ) (x : Option ι) :
    w.afterOutside N r k row x - w.hazard N r k row =
      w.positiveOutside N r k row x := by
  cases x <;> simp [afterOutside, positiveOutside, hazard_change_outside]

theorem increment_inside (N : ℝ) (r : ℕ) (k row : ι → ℕ) (x : Option ι) :
    w.afterInside N r k row x - w.hazard N r k row =
      w.positiveInside N r k row x - w.seen k / N := by
  cases x <;> simp [afterInside, positiveInside, hazard_change_inside,
    hazard_change_rejected, neg_div]

private theorem coeff_bounds (N : ℝ) (hN : 0 < N) (t : ℝ)
    (ht : 0 ≤ t) (htN : t ≤ N) : 0 ≤ 1 - t / N ∧ 1 - t / N ≤ 1 := by
  constructor
  · exact sub_nonneg.mpr ((div_le_one hN).2 htN)
  · exact sub_le_self _ (div_nonneg ht hN.le)

private theorem row_ratio_bounds (k row : ι → ℕ) (hrow : ∀ i, row i ≤ k i)
    (L : ℝ) (hL : 0 ≤ L) (hratio : ∀ i, w.g i / w.p i ≤ L)
    (i : ι) (h1 : k i = 1) :
    0 ≤ (row i : ℝ) * w.g i / w.p i ∧ (row i : ℝ) * w.g i / w.p i ≤ L := by
  have hr : (row i : ℝ) ≤ 1 := by exact_mod_cast (h1 ▸ hrow i)
  have hg := div_nonneg (w.g_nonneg i) (w.p_pos i).le
  constructor
  · exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) (w.g_nonneg i)) (w.p_pos i).le
  · calc
      (row i : ℝ) * w.g i / w.p i = (row i : ℝ) * (w.g i / w.p i) := by ring
      _ ≤ 1 * L := mul_le_mul hr (hratio i) hg (by norm_num)
      _ = L := one_mul L

/-- The physical count consistency is used only here, to bound the singleton jump. -/
theorem positiveOutside_bounds (N : ℝ) (hN : 0 < N) (r : ℕ)
    (hr : (r : ℝ) ≤ N) (k row : ι → ℕ) (hrow : ∀ i, row i ≤ k i)
    (G L : ℝ) (hG : 0 ≤ G) (hL : 0 ≤ L)
    (hg : ∀ i, w.g i ≤ G) (hratio : ∀ i, w.g i / w.p i ≤ L)
    (x : Option ι) :
    0 ≤ w.positiveOutside N r k row x ∧
      w.positiveOutside N r k row x ≤ G + 2 * L / N := by
  have hLN : 0 ≤ L / N := div_nonneg hL hN.le
  have htwo : 2 * L / N = 2 * (L / N) := by ring
  have hc := coeff_bounds N hN r (Nat.cast_nonneg _) hr
  cases x with
  | none => simp only [positiveOutside]; constructor <;> nlinarith
  | some i =>
    by_cases h0 : k i = 0
    · have h1 : k i ≠ 1 := by omega
      simp only [positiveOutside, if_pos h0, if_neg h1, zero_div, add_zero]
      have hu : (1 - (r : ℝ) / N) * w.g i ≤ G :=
        (mul_le_mul_of_nonneg_right hc.2 (w.g_nonneg i)).trans (by simpa using hg i)
      constructor
      · exact mul_nonneg hc.1 (w.g_nonneg i)
      · nlinarith
    · by_cases h1 : k i = 1
      · simp only [positiveOutside, if_neg h0, if_pos h1, mul_zero, zero_add]
        have hb := w.row_ratio_bounds k row hrow L hL hratio i h1
        have hd := div_le_div_of_nonneg_right hb.2 hN.le
        constructor
        · exact div_nonneg hb.1 hN.le
        · nlinarith
      · simp only [positiveOutside, if_neg h0, if_neg h1, mul_zero, zero_div, add_zero]
        constructor <;> nlinarith

theorem positiveInside_bounds (N : ℝ) (hN : 0 < N) (r : ℕ)
    (hr : (r : ℝ) + 1 ≤ N) (k row : ι → ℕ) (hrow : ∀ i, row i ≤ k i)
    (G L : ℝ) (hG : 0 ≤ G) (hL : 0 ≤ L)
    (hg : ∀ i, w.g i ≤ G) (hratio : ∀ i, w.g i / w.p i ≤ L)
    (x : Option ι) :
    0 ≤ w.positiveInside N r k row x ∧
      w.positiveInside N r k row x ≤ G + 2 * L / N := by
  have hLN : 0 ≤ L / N := div_nonneg hL hN.le
  have htwo : 2 * L / N = 2 * (L / N) := by ring
  have hc := coeff_bounds N hN ((r : ℝ) + 1) (by positivity) hr
  cases x with
  | none => simp only [positiveInside]; constructor <;> nlinarith
  | some i =>
    by_cases h0 : k i = 0
    · have h1 : k i ≠ 1 := by omega
      simp only [positiveInside, if_pos h0, if_neg h1, add_zero, zero_div]
      have hu : (1 - ((r : ℝ) + 1) / N) * w.g i ≤ G :=
        (mul_le_mul_of_nonneg_right hc.2 (w.g_nonneg i)).trans (by simpa using hg i)
      constructor
      · exact mul_nonneg hc.1 (w.g_nonneg i)
      · nlinarith
    · have hgi : 0 ≤ w.g i / w.p i := div_nonneg (w.g_nonneg i) (w.p_pos i).le
      by_cases h1 : k i = 1
      · simp only [positiveInside, if_neg h0, if_pos h1, mul_zero, zero_add]
        have hb := w.row_ratio_bounds k row hrow L hL hratio i h1
        have hd : (w.g i / w.p i + (row i : ℝ) * w.g i / w.p i) / N ≤ 2 * L / N :=
          div_le_div_of_nonneg_right (by linarith [hratio i]) hN.le
        constructor
        · exact div_nonneg (add_nonneg hgi hb.1) hN.le
        · linarith
      · simp only [positiveInside, if_neg h0, if_neg h1, mul_zero, add_zero, zero_add]
        have hd := div_le_div_of_nonneg_right (hratio i) hN.le
        constructor
        · exact div_nonneg hgi hN.le
        · nlinarith


/-- Elementary finite-distribution expectation rules, retaining rejection. -/
theorem expect_const (a : ℝ) : w.expect (fun _ => a) = a := by
  simp only [expect, ← Finset.sum_mul]
  ring

theorem expect_add (f f' : Option ι → ℝ) :
    w.expect (fun x => f x + f' x) = w.expect f + w.expect f' := by
  simp only [expect, mul_add, Finset.sum_add_distrib]
  ring

theorem expect_sub (f f' : Option ι → ℝ) :
    w.expect (fun x => f x - f' x) = w.expect f - w.expect f' := by
  simp only [expect, mul_sub, Finset.sum_sub_distrib]
  ring

theorem expect_smul (a : ℝ) (f : Option ι → ℝ) :
    w.expect (fun x => a * f x) = a * w.expect f := by
  unfold expect
  rw [show (∑ i, w.p i * (a * f (some i))) = a * ∑ i, w.p i * f (some i) by
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intros; ring]
  ring

theorem expect_mono (f f' : Option ι → ℝ) (h : ∀ x, f x ≤ f' x) :
    w.expect f ≤ w.expect f' := by
  unfold expect
  apply add_le_add
  · exact mul_le_mul_of_nonneg_left (h none) w.rejection_nonneg
  · exact Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (h (some i)) (w.p_pos i).le)

theorem expect_nonneg (f : Option ι → ℝ) (hf : ∀ x, 0 ≤ f x) : 0 ≤ w.expect f := by
  simpa only [expect_const] using w.expect_mono (fun _ => 0) f hf

theorem expect_le_const (f : Option ι → ℝ) (d : ℝ) (hf : ∀ x, f x ≤ d) :
    w.expect f ≤ d := by
  simpa only [expect_const] using w.expect_mono f (fun _ => d) hf

/-- Subtracting a predictable scalar does not change the centered increment. -/
theorem center_predictable_shift (u : Option ι → ℝ) (c : ℝ) (x : Option ι) :
    (u x - c) - w.expect (fun y => u y - c) = u x - w.expect u := by
  rw [expect_sub, expect_const]
  ring

/-- Exact second centered moment for this finite distribution. -/
theorem centered_square (u : Option ι → ℝ) :
    w.expect (fun x => (u x - w.expect u)^2) =
      w.expect (fun x => (u x)^2) - (w.expect u)^2 := by
  calc
    w.expect (fun x => (u x - w.expect u)^2) =
        w.expect (fun x => (u x)^2 - (2 * w.expect u) * u x + (w.expect u)^2) := by
          congr 1; funext x; ring
    _ = w.expect (fun x => (u x)^2) - (w.expect u)^2 := by
      rw [expect_add, expect_sub, expect_smul, expect_const]
      ring

/-- A nonnegative jump in [0,d] has variance at most d times its mean. -/
theorem centered_variance_le (u : Option ι → ℝ) (d : ℝ)
    (hu : ∀ x, 0 ≤ u x ∧ u x ≤ d) :
    w.expect (fun x => (u x - w.expect u)^2) ≤ d * w.expect u := by
  have hsq : w.expect (fun x => (u x)^2) ≤ w.expect (fun x => d * u x) := by
    apply w.expect_mono
    intro x
    nlinarith [(hu x).1, (hu x).2]
  rw [expect_smul] at hsq
  rw [centered_square]
  nlinarith [sq_nonneg (w.expect u)]

/-- Its centered increment is also bounded in absolute value by d. -/
theorem centered_abs_le (u : Option ι → ℝ) (d : ℝ)
    (hu : ∀ x, 0 ≤ u x ∧ u x ≤ d) (x : Option ι) :
    |u x - w.expect u| ≤ d := by
  have hm0 := w.expect_nonneg u (fun y => (hu y).1)
  have hmd := w.expect_le_const u d (fun y => (hu y).2)
  apply abs_le.mpr
  constructor <;> linarith [(hu x).1, (hu x).2]

#print axioms drift_outside
#print axioms drift_inside
#print axioms drift_outside_le
#print axioms drift_inside_le
#print axioms expect_one
#print axioms positiveOutside_bounds
#print axioms positiveInside_bounds
#print axioms centered_variance_le
#print axioms centered_abs_le
#print axioms center_predictable_shift

end Weights
end WeightedRow
