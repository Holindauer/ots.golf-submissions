import Submissions.UpperCompressions.ReplacementKernel

/-! Exact finite-table iid sampling law. `iidMean` is the expectation obtained by
independently drawing one uniform element at every recursive step. A fixed target
is returned precisely when earlier draws are strictly worse and later draws are
weakly worse. Repeated nonce values are included without any distinctness premise. -/

namespace WeightedReplacement

attribute [local instance] Classical.propDecidable

noncomputable def uniformMean {α : Type*} [Fintype α] (f : α → ℝ) : ℝ :=
  (∑ a, f a) / Fintype.card α

noncomputable def iidMean {α : Type*} [Fintype α] : ℕ → (List α → ℝ) → ℝ
  | 0, f => f []
  | n+1, f => uniformMean fun a => iidMean n (fun xs => f (a :: xs))

noncomputable def allPass {α : Type*} (weak : α → Prop) (xs : List α) : ℝ :=
  if ∀ a ∈ xs, weak a then 1 else 0

noncomputable def targetWins {α : Type*} (v : α) (weak strict : α → Prop) : List α → ℝ
  | [] => 0
  | a :: xs => if a = v then allPass weak xs else
      if strict a then targetWins v weak strict xs else 0

noncomputable def fraction {α : Type*} [Fintype α] (p : α → Prop) : ℝ :=
  uniformMean fun a => if p a then 1 else 0

/-- A target occurrence with only strictly worse draws before it and only weakly
worse draws after it is exactly a first occurrence at the minimum accepted tier. -/
def FirstMinimumEvent {α : Type*} (v : α) (weak strict : α → Prop) (xs : List α) : Prop :=
  ∃ pre post, xs = pre ++ v :: post ∧ (∀ a ∈ pre, strict a) ∧ (∀ a ∈ post, weak a)

theorem firstMinimumEvent_nil {α : Type*} (v : α) (weak strict : α → Prop) :
    ¬ FirstMinimumEvent v weak strict [] := by
  rintro ⟨pre, post, he, _, _⟩
  have hh := congrArg List.length he
  simp at hh

theorem firstMinimumEvent_cons {α : Type*} (v a : α) (weak strict : α → Prop)
    (xs : List α) :
    FirstMinimumEvent v weak strict (a :: xs) ↔
      (a = v ∧ ∀ b ∈ xs, weak b) ∨ (strict a ∧ FirstMinimumEvent v weak strict xs) := by
  constructor
  · rintro ⟨pre, post, he, hpre, hpost⟩
    cases pre with
    | nil =>
      simp only [List.nil_append, List.cons.injEq] at he
      exact Or.inl ⟨he.1, he.2 ▸ hpost⟩
    | cons b pre =>
      simp only [List.cons_append, List.cons.injEq] at he
      obtain ⟨rfl, he⟩ := he
      exact Or.inr ⟨hpre a (by simp), pre, post, he,
        fun c hc => hpre c (by simp [hc]), hpost⟩
  · rintro (⟨rfl, hx⟩ | ⟨ha, pre, post, he, hpre, hpost⟩)
    · exact ⟨[], xs, rfl, by simp, hx⟩
    · refine ⟨a :: pre, post, ?_, ?_, hpost⟩
      · simp [he]
      · simpa using And.intro ha hpre

theorem targetWins_indicator {α : Type*} (v : α) (weak strict : α → Prop)
    (hv : ¬ strict v) (xs : List α) :
    targetWins v weak strict xs = if FirstMinimumEvent v weak strict xs then 1 else 0 := by
  classical
  induction xs with
  | nil => simp [targetWins, firstMinimumEvent_nil]
  | cons a xs ih =>
    rw [firstMinimumEvent_cons]
    by_cases ha : a = v
    · subst a
      simp [targetWins, hv, allPass]
    · by_cases hs : strict a
      · simp [targetWins, ha, hs, ih]
      · simp [targetWins, ha, hs]

theorem uniformMean_add {α : Type*} [Fintype α] (f g : α → ℝ) :
    uniformMean (fun a => f a + g a) = uniformMean f + uniformMean g := by
  simp [uniformMean, Finset.sum_add_distrib, add_div]

theorem uniformMean_mul_const {α : Type*} [Fintype α] (f : α → ℝ) (c : ℝ) :
    uniformMean (fun a => f a * c) = uniformMean f * c := by
  simp [uniformMean, ← Finset.sum_mul, div_mul_eq_mul_div]

theorem uniformMean_gate {α : Type*} [Fintype α] (p : α → Prop) (c : ℝ) :
    uniformMean (fun a => if p a then c else 0) = fraction p * c := by
  classical
  unfold fraction
  rw [← uniformMean_mul_const]
  congr 1
  funext a
  split_ifs <;> simp

theorem uniformMean_point {α : Type*} [Fintype α] (v : α) (c : ℝ) :
    uniformMean (fun a => if a = v then c else 0) = c / Fintype.card α := by
  classical
  simp [uniformMean]

theorem iidMean_zero {α : Type*} [Fintype α] (n : ℕ) :
    iidMean n (fun _ : List α => 0) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [iidMean, ih, uniformMean]

theorem iidMean_allPass {α : Type*} [Fintype α] (weak : α → Prop) (n : ℕ) :
    iidMean n (allPass weak) = fraction weak ^ n := by
  classical
  induction n with
  | zero => simp [iidMean, allPass]
  | succ n ih =>
    have hh (a : α) :
        iidMean n (fun xs => allPass weak (a :: xs)) =
          if weak a then fraction weak ^ n else 0 := by
      by_cases ha : weak a
      · have hf : (fun xs => allPass weak (a :: xs)) = allPass weak := by
          funext xs
          simp [allPass, ha]
        simpa only [hf, if_pos ha] using ih
      · simp [allPass, ha, iidMean_zero]
    simp only [iidMean, hh]
    rw [uniformMean_gate, pow_succ']

theorem iidMean_targetWins_succ {α : Type*} [Fintype α]
    (v : α) (weak strict : α → Prop) (hv : ¬ strict v) (n : ℕ) :
    iidMean (n+1) (targetWins v weak strict) =
      fraction weak ^ n / Fintype.card α +
        fraction strict * iidMean n (targetWins v weak strict) := by
  classical
  have hh (a : α) :
      iidMean n (fun xs => targetWins v weak strict (a :: xs)) =
        (if a = v then fraction weak ^ n else 0) +
        (if strict a then iidMean n (targetWins v weak strict) else 0) := by
    by_cases ha : a = v
    · subst a
      simp [targetWins, hv, iidMean_allPass]
    · by_cases hs : strict a
      · simp [targetWins, ha, hs]
      · simp [targetWins, ha, hs, iidMean_zero]
  simp only [iidMean, hh]
  rw [uniformMean_add, uniformMean_point, uniformMean_gate]

theorem kernel_succ (n : ℕ) (A B : ℝ) :
    kernel (n+1) A B = A^n + B * kernel n A B := by
  unfold kernel
  rw [Finset.sum_range_succ]
  simp only [Nat.add_sub_cancel, Nat.sub_self, pow_zero, mul_one]
  rw [Finset.mul_sum]
  have hh : (∑ k ∈ Finset.range n, A^k * B^(n-k)) =
      ∑ k ∈ Finset.range n, B * (A^k * B^(n-1-k)) := by
    apply Finset.sum_congr rfl
    intro k hk
    have hk' := Finset.mem_range.mp hk
    have he : n-k = (n-1-k)+1 := by omega
    rw [he, pow_succ]
    ring
  rw [hh]
  ring

/-- The exact probability that iid uniform draws return a fixed nonce under the
first-minimum rule. `weak` means no better than the target; `strict` means strictly
worse, including rejected draws. The only algebraic premise is that the target
is not strictly worse than itself. -/
theorem iid_first_minimum_probability {α : Type*} [Fintype α]
    (v : α) (weak strict : α → Prop) (hv : ¬ strict v) (n : ℕ) :
    iidMean n (targetWins v weak strict) =
      kernel n (fraction weak) (fraction strict) / Fintype.card α := by
  induction n with
  | zero => simp [iidMean, targetWins]
  | succ n ih =>
    rw [iidMean_targetWins_succ v weak strict hv, ih, kernel_succ]
    ring

theorem iid_first_minimum_event_probability {α : Type*} [Fintype α]
    (v : α) (weak strict : α → Prop) (hv : ¬ strict v) (n : ℕ) :
    iidMean n (fun xs => if FirstMinimumEvent v weak strict xs then 1 else 0) =
      kernel n (fraction weak) (fraction strict) / Fintype.card α := by
  classical
  simp_rw [← targetWins_indicator v weak strict hv]
  exact iid_first_minimum_probability v weak strict hv n

set_option maxHeartbeats 1000000 in
/-- Independent finite uniform sampling is exactly the uniform distribution on
all length-n vectors, with denominator N^n. The recursive definition does not hide
any random-sampling or independence premise. -/
theorem iidMean_eq_uniform_vectors {α : Type*} [Fintype α] (n : ℕ) (f : List α → ℝ) :
    iidMean n f = (∑ draws : Fin n → α, f (List.ofFn draws)) / (Fintype.card α : ℝ)^n := by
  classical
  induction n generalizing f with
  | zero => simp [iidMean]
  | succ n ih =>
    simp only [iidMean]
    simp_rw [ih]
    unfold uniformMean
    rw [← Finset.sum_div, div_div, ← pow_succ]
    congr 1
    calc
      (∑ a, ∑ draws : Fin n → α, f (a :: List.ofFn draws)) =
          ∑ p : α × (Fin n → α), f (p.1 :: List.ofFn p.2) :=
        (Fintype.sum_prod_type (fun p : α × (Fin n → α) => f (p.1 :: List.ofFn p.2))).symm
      _ = ∑ draws : Fin (n+1) → α, f (List.ofFn draws) := by
        have he := (Fin.consEquiv (fun _ : Fin (n+1) => α)).sum_comp
          (fun draws : Fin (n+1) → α => f (List.ofFn draws))
        change (∑ p : α × (Fin n → α), f (List.ofFn (Fin.cons p.1 p.2))) =
          ∑ draws : Fin (n+1) → α, f (List.ofFn draws) at he
        simpa only [List.ofFn_cons] using he

/-- Finite sample-space formulation of the exact first-minimum law. -/
theorem uniform_vectors_first_minimum_probability {α : Type*} [Fintype α]
    (v : α) (weak strict : α → Prop) (hv : ¬ strict v) (n : ℕ) :
    (∑ draws : Fin n → α,
      if FirstMinimumEvent v weak strict (List.ofFn draws) then (1 : ℝ) else 0) /
        (Fintype.card α : ℝ)^n =
      kernel n (fraction weak) (fraction strict) / Fintype.card α := by
  classical
  rw [← iidMean_eq_uniform_vectors n
    (fun xs => if FirstMinimumEvent v weak strict xs then (1 : ℝ) else 0)]
  exact iid_first_minimum_event_probability v weak strict hv n

#print axioms iidMean_allPass
#print axioms iid_first_minimum_probability
#print axioms iid_first_minimum_event_probability
#print axioms iidMean_eq_uniform_vectors
#print axioms uniform_vectors_first_minimum_probability

end WeightedReplacement
