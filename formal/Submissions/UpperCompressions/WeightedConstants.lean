import Mathlib

/-! Symbolic constants for the mixed72 schedule, avoiding million-degree
rational evaluation. These lemmas concern the reference tier distribution. -/

noncomputable section
namespace WeightedConstants
attribute [local irreducible] Nat.choose
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

def L : ℕ := 2^20
def q : ℝ := 19/(16*L)

theorem truncated_binomial (x : ℝ) (hx : 0 ≤ x) (n d : ℕ) (hd : d ≤ n+1) :
    (∑ i ∈ Finset.range d, x^i*(n.choose i : ℝ)) ≤ (1+x)^n := by
  have h := Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hd)
    (f := fun i => x^i*(1:ℝ)^(n-i)*(n.choose i : ℝ))
    (by intro i hi hni; positivity)
  rw [← add_pow] at h
  simpa only [one_pow,mul_one,add_comm] using h

theorem reciprocal_lower : (200:ℝ)/61 ≤ (1+(19:ℝ)/16777197)^L := by
  have h := truncated_binomial ((19:ℝ)/16777197) (by norm_num) L 8 (by norm_num [L])
  have hb : (200:ℝ)/61 ≤ ∑ i ∈ Finset.range 8, ((19:ℝ)/16777197)^i*(L.choose i : ℝ) := by
    norm_num [L,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,
      Nat.descFactorial_succ,Nat.factorial_succ]
  exact hb.trans h

theorem first_survival : (1-q)^L ≤ (61:ℝ)/200 := by
  have hnonneg : 0 ≤ (1-q)^L := by apply pow_nonneg; norm_num [q,L]
  have hid : (1-q)^L*(1+(19:ℝ)/16777197)^L = 1 := by
    rw [← mul_pow]
    have hb : (1-q)*(1+(19:ℝ)/16777197) = 1 := by norm_num [q,L]
    rw [hb,one_pow]
  have h := mul_le_mul_of_nonneg_left reciprocal_lower hnonneg
  rw [hid] at h
  linarith

theorem penultimate_reciprocal_lower : (3:ℝ) ≤ (1+(19:ℝ)/16777197)^(L-1) := by
  have h := truncated_binomial ((19:ℝ)/16777197) (by norm_num) (L-1) 4 (by norm_num [L])
  have hb : (3:ℝ) ≤ ∑ i ∈ Finset.range 4,
      ((19:ℝ)/16777197)^i*((L-1).choose i : ℝ) := by
    norm_num [L,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,
      Nat.descFactorial_succ,Nat.factorial_succ]
  exact hb.trans h

theorem penultimate_survival : (1-q)^(L-1) ≤ (1:ℝ)/3 := by
  have hnonneg : 0 ≤ (1-q)^(L-1) := by apply pow_nonneg; norm_num [q,L]
  have hid : (1-q)^(L-1)*(1+(19:ℝ)/16777197)^(L-1) = 1 := by
    rw [← mul_pow]
    have hb : (1-q)*(1+(19:ℝ)/16777197) = 1 := by norm_num [q,L]
    rw [hb,one_pow]
  have h := mul_le_mul_of_nonneg_left penultimate_reciprocal_lower hnonneg
  rw [hid] at h
  linarith

theorem prefix_power (t : ℕ) (r : ℝ) (hb : (1-q)^t ≤ r)
    (j : ℕ) (hj : j ≤ 71) : (1-(j:ℝ)*q)^t ≤ r^j := by
  have hjr : (j:ℝ) ≤ 71 := by exact_mod_cast hj
  have hq0 : 0 ≤ q := by norm_num [q,L]
  have hq1 : q ≤ 1 := by norm_num [q,L]
  have hbase : 0 ≤ 1-(j:ℝ)*q := by
    have hp := mul_le_mul_of_nonneg_right hjr hq0
    have hh : (71:ℝ)*q ≤ 1 := by norm_num [q,L]
    linarith
  have hbern : 1-(j:ℝ)*q ≤ (1-q)^j := by
    have h := one_add_mul_le_pow (show (-2:ℝ) ≤ -q by linarith) j
    simpa only [sub_eq_add_neg,mul_neg] using h
  calc
    _ ≤ ((1-q)^j)^t := pow_le_pow_left₀ hbase hbern t
    _ = ((1-q)^t)^j := by rw [← pow_mul,← pow_mul,Nat.mul_comm j t]
    _ ≤ r^j := pow_le_pow_left₀ (pow_nonneg (by linarith) _) hb j

theorem weighted_telescope (u : ℕ → ℝ) (k : ℕ) :
    (∑ j ∈ Finset.range k, (2:ℝ)^j*(u j-u (j+1))) =
      u 0+(∑ j ∈ Finset.range k, (2:ℝ)^j*u (j+1))-(2:ℝ)^k*u k := by
  induction k with
  | zero => simp
  | succ k ih =>
    simp only [Finset.sum_range_succ,ih,pow_succ]
    ring

theorem geometric_identity (x : ℝ) (k : ℕ) :
    (1-x)*(∑ j ∈ Finset.range k, x^j) = 1-x^k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ,mul_add,ih,pow_succ]
    ring

theorem geometric_upper (x : ℝ) (hx : 0 ≤ x) (hx1 : x < 1) (k : ℕ) :
    (∑ j ∈ Finset.range k, x^j) ≤ 1/(1-x) := by
  apply (le_div_iff₀ (by linarith)).2
  rw [mul_comm,geometric_identity]
  exact sub_le_self _ (pow_nonneg hx k)

/-- The last tier may contain more aliases; only its failure tail is dropped.
No equal-mass assumption is imposed on that last tier. -/
theorem weighted_mean_bound (u : ℕ → ℝ) (tail : ℝ) (ht : 0 ≤ tail)
    (h0 : u 0 ≤ 1) (hu : ∀ j, j ≤ 71 → u j ≤ ((61:ℝ)/200)^j) :
    (1:ℝ)/2*((∑ j ∈ Finset.range 71, (2:ℝ)^j*(u j-u (j+1)))+
      (2:ℝ)^71*(u 71-tail)) ≤ 139/156 := by
  rw [weighted_telescope]
  have hs : (∑ j ∈ Finset.range 71, (2:ℝ)^j*u (j+1)) ≤
      (61:ℝ)/200*(∑ j ∈ Finset.range 71, ((61:ℝ)/100)^j) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j hj
    have hp := mul_le_mul_of_nonneg_left (hu (j+1) (by have := Finset.mem_range.mp hj; omega))
      (show (0:ℝ) ≤ 2^j by positivity)
    calc
      _ ≤ 2^j*((61:ℝ)/200)^(j+1) := hp
      _ = (61:ℝ)/200*((61:ℝ)/100)^j := by
        rw [pow_succ]
        have hh : (2:ℝ)*((61:ℝ)/200) = (61:ℝ)/100 := by norm_num
        rw [← hh,mul_pow]
        ring
  have hg := geometric_upper ((61:ℝ)/100) (by norm_num) (by norm_num) 71
  have htail : (0:ℝ) ≤ 2^71*tail := by positivity
  nlinarith

def referenceMean (failure : ℝ) : ℝ :=
  (1:ℝ)/2*((∑ j ∈ Finset.range 71,
    (2:ℝ)^j*((1-(j:ℝ)*q)^L-(1-((j+1:ℕ):ℝ)*q)^L))+
      (2:ℝ)^71*((1-(71:ℝ)*q)^L-failure))

theorem referenceMean_le (failure : ℝ) (hf : 0 ≤ failure) :
    referenceMean failure ≤ (223:ℝ)/250 := by
  have h := weighted_mean_bound (fun j => (1-(j:ℝ)*q)^L) failure hf (by simp)
    (fun j hj => prefix_power L ((61:ℝ)/200) first_survival j hj)
  exact h.trans (by norm_num)

theorem relative_peak_bound (j : ℕ) (hj : j ≤ 71) :
    (2:ℝ)^j*(1-(j:ℝ)*q)^(L-1) ≤ 1 := by
  have h := mul_le_mul_of_nonneg_left
    (prefix_power (L-1) ((1:ℝ)/3) penultimate_survival j hj)
    (show (0:ℝ) ≤ 2^j by positivity)
  calc
    _ ≤ (2:ℝ)^j*((1:ℝ)/3)^j := h
    _ = ((2:ℝ)/3)^j := by rw [← mul_pow]; congr 1; norm_num
    _ ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)

theorem small_total_margin :
    (99:ℝ)/98*(223/250)*(11/10)+2/1000 = 243337/245000 ∧
      (243337:ℝ)/245000 < 1 := by norm_num

#print axioms first_survival
#print axioms penultimate_survival
#print axioms referenceMean_le
#print axioms relative_peak_bound
end WeightedConstants
