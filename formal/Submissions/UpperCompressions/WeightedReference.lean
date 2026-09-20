import Submissions.UpperCompressions.WeightedConstants
import Submissions.UpperCompressions.ReplacementKernel

/-! Reference probabilities and symbolic security constants for mixed72.
These are arithmetic lemmas, not a forgery-game theorem. -/
noncomputable section
namespace WeightedReference
open WeightedConstants WeightedReplacement
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

def kappa : ℝ := 1/2^127
def acceptance : ℝ := 45/524288
def survival (j : ℕ) : ℝ := 1-(j:ℝ)*q
def lower (j : ℕ) : ℝ := if j < 71 then survival (j+1) else 1-acceptance
def mass (j : ℕ) : ℝ := survival j-lower j
def probability (j : ℕ) : ℝ := kappa/2*2^j
def weight (j : ℕ) : ℝ := probability j*kernel L (survival j) (lower j)
def failure : ℝ := (1-acceptance)^L

theorem survival_nonneg (j : ℕ) (hj : j ≤ 71) : 0 ≤ survival j := by
  have hjr : (j:ℝ) ≤ 71 := by exact_mod_cast hj
  have hh := mul_le_mul_of_nonneg_right hjr (show 0 ≤ q by norm_num [q,L])
  have hn : (71:ℝ)*q ≤ 1 := by norm_num [q,L]
  unfold survival
  linarith

theorem lower_nonneg (j : ℕ) (hj : j ≤ 71) : 0 ≤ lower j := by
  unfold lower
  split_ifs with h
  · exact survival_nonneg _ (by omega)
  · norm_num [acceptance]

theorem lower_le_survival (j : ℕ) (hj : j ≤ 71) : lower j ≤ survival j := by
  unfold lower
  split_ifs with h
  · have hq : 0 ≤ q := by norm_num [q,L]
    simp only [survival,Nat.cast_add,Nat.cast_one]
    nlinarith
  · have he : j=71 := by omega
    subst j
    norm_num [survival,acceptance,q,L]

theorem kernel_diagonal (n : ℕ) (A : ℝ) : kernel n A A = (n:ℝ)*A^(n-1) := by
  unfold kernel
  have hterm : ∀ k ∈ Finset.range n, A^k*A^(n-1-k) = A^(n-1) := by
    intro k hk
    rw [← pow_add]
    congr 1
    have := Finset.mem_range.mp hk
    omega
  simp only [Finset.sum_congr rfl hterm,Finset.sum_const,Finset.card_range,nsmul_eq_mul]

theorem weight_nonneg (j : ℕ) (hj : j ≤ 71) : 0 ≤ weight j := by
  exact mul_nonneg (by unfold probability kappa; positivity)
    (kernel_nonneg L (survival_nonneg j hj) (lower_nonneg j hj))

theorem weight_le (j : ℕ) (hj : j ≤ 71) : weight j ≤ (L:ℝ)*kappa/2 := by
  have hm := kernel_mono L (survival_nonneg j hj) (lower_nonneg j hj)
    (le_refl (survival j)) (lower_le_survival j hj)
  rw [kernel_diagonal] at hm
  have hp : 0 ≤ probability j := by unfold probability kappa; positivity
  have h := mul_le_mul_of_nonneg_left hm hp
  have ht := relative_peak_bound j hj
  have hk : 0 ≤ (L:ℝ)*kappa/2 := by unfold kappa; positivity
  have ht' := mul_le_mul_of_nonneg_left ht hk
  unfold weight
  calc
    _ ≤ probability j*((L:ℝ)*survival j^(L-1)) := h
    _ = ((L:ℝ)*kappa/2)*(2^j*(1-(j:ℝ)*q)^(L-1)) := by unfold probability survival; ring
    _ ≤ (L:ℝ)*kappa/2 := by simpa only [mul_one] using ht'

theorem failure_nonneg : 0 ≤ failure := by unfold failure acceptance; positivity

theorem failure_le : failure ≤ (1:ℝ)/1000 := by
  have hm : 1-acceptance ≤ survival 71 := by norm_num [acceptance,survival,q,L]
  have h := pow_le_pow_left₀ (show 0 ≤ 1-acceptance by norm_num [acceptance]) hm L
  have hp := prefix_power L ((61:ℝ)/200) first_survival 71 (by omega)
  exact (h.trans hp).trans (by norm_num)

theorem mass_weight (j : ℕ) :
    mass j*weight j = kappa/2*(2^j*(survival j^L-lower j^L)) := by
  have h := sub_mul_kernel L (survival j) (lower j)
  unfold mass weight probability
  calc
    _ = kappa/2*2^j*((survival j-lower j)*kernel L (survival j) (lower j)) := by ring
    _ = _ := by rw [h]; ring

theorem reference_mean_identity :
    (∑ j ∈ Finset.range 72, mass j*weight j) = kappa*referenceMean failure := by
  rw [show 72=71+1 by omega,Finset.sum_range_succ]
  have hs : (∑ j ∈ Finset.range 71, mass j*weight j) =
      kappa/2*(∑ j ∈ Finset.range 71,2^j*(survival j^L-survival (j+1)^L)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [mass_weight,lower,if_pos (Finset.mem_range.mp hj)]
  rw [hs,mass_weight]
  simp only [lower,show ¬71<71 by omega,if_false]
  unfold referenceMean failure survival
  ring

theorem reference_mean_le :
    (∑ j ∈ Finset.range 72,mass j*weight j) ≤ kappa*(223/250) := by
  rw [reference_mean_identity]
  exact mul_le_mul_of_nonneg_left (referenceMean_le failure failure_nonneg)
    (by unfold kappa; positivity)

theorem telescope (u : ℕ → ℝ) (n : ℕ) :
    (∑ j ∈ Finset.range n,(u j-u (j+1))) = u 0-u n := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ,ih]; ring

theorem total_mass : (∑ j ∈ Finset.range 72,mass j) = acceptance := by
  rw [show 72=71+1 by omega,Finset.sum_range_succ]
  have hs : (∑ j ∈ Finset.range 71,mass j) = survival 0-survival 71 := by
    rw [← telescope survival 71]
    apply Finset.sum_congr rfl
    intro j hj
    simp only [mass,lower,if_pos (Finset.mem_range.mp hj)]
  rw [hs]
  norm_num [mass,lower,survival]

theorem total_winner_mass :
    (∑ j ∈ Finset.range 72,mass j*kernel L (survival j) (lower j)) = 1-failure := by
  rw [show 72=71+1 by omega,Finset.sum_range_succ]
  have hs : (∑ j ∈ Finset.range 71,mass j*kernel L (survival j) (lower j)) =
      survival 0^L-survival 71^L := by
    rw [← telescope (fun j => survival j^L) 71]
    apply Finset.sum_congr rfl
    intro j hj
    unfold mass
    rw [sub_mul_kernel,lower,if_pos (Finset.mem_range.mp hj)]
  rw [hs]
  unfold mass
  rw [sub_mul_kernel]
  simp only [lower,show ¬71<71 by omega,if_false]
  unfold failure
  have h0 : survival 0=1 := by simp [survival]
  rw [h0,one_pow]
  ring

theorem post_excess_le {h f : ℝ} (hh : h ≤ kappa*(223/250))
    (hf : f ≤ 1/1000) : h/(1-acceptance)-kappa/2*(1-f) ≤ kappa*(2/5) := by
  have hd : 0 < 1-acceptance := by norm_num [acceptance]
  have h1 := div_le_div_of_nonneg_right hh hd.le
  have hk : 0 ≤ kappa := by unfold kappa; positivity
  have h2 := mul_le_mul_of_nonneg_left hf (div_nonneg hk (by norm_num : (0:ℝ) ≤ 2))
  have hn : (kappa*(223/250))/(1-acceptance)-kappa/2*(1-1/1000) ≤ kappa*(2/5) := by
    norm_num [kappa,acceptance]
  linarith

/-- A binomial upper bound that avoids expanding a large natural exponent. -/
theorem pow_times_linear_le_one (x : ℝ) (hx : 0 ≤ x) (n : ℕ) :
    (1+x)^n*(1-(n:ℝ)*x) ≤ 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hp : 0 ≤ (1+x)^n := by positivity
    have hs : 0 ≤ (1+x)^n*((n:ℝ)+1)*x^2 := by positivity
    push_cast
    rw [pow_succ]
    nlinarith

theorem common_envelope :
    (1+(1/(100*(L:ℝ)))/(1-acceptance))^(L-1) ≤ (99:ℝ)/98 := by
  let x : ℝ := (1/(100*(L:ℝ)))/(1-acceptance)
  have hx : 0 ≤ x := by norm_num [x,L,acceptance]
  have h := pow_times_linear_le_one x hx (L-1)
  have hd : 0 < 1-((L-1:ℕ):ℝ)*x := by norm_num [x,L,acceptance]
  have hb : 1/(1-((L-1:ℕ):ℝ)*x) ≤ (99:ℝ)/98 := by norm_num [x,L,acceptance]
  exact ((le_div_iff₀ hd).2 h).trans hb

#print axioms weight_le
#print axioms reference_mean_le
#print axioms post_excess_le
#print axioms common_envelope
end WeightedReference
