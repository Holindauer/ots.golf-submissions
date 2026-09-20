import Submissions.UpperCompressions.WideAuthCharges
import Submissions.UpperCompressions.Master

/-! Authentication record potentials and a joint query-type interface.
The index potential is explicit and must be discharged by the weighted posterior proof. -/
open OracleSpec OracleComp OracleComp.EvalDist ENNReal
noncomputable section
open scoped Classical
namespace OptimalOTS.WeightedConstruction.WideForest
open OptimalOTS.Dag Name

def sumW (T : Finset Rec) : ℝ≥0∞ := ∑ ξ ∈ T, w

def ind (p : Prop) : ℝ≥0∞ := if p then 1 else 0

def authRate : ℝ≥0∞ := (((2:ℝ≥0∞)^127)⁻¹) / 2

def authPotential (T : Finset Rec) (A? : Option (Finset Name)) (c : Cache) : ℝ≥0∞ :=
  ∑ ξ ∈ T, w * (ind (Cache.Hits c (fHid A? ξ)) + ind (Spr c ξ))

theorem sumW_mono {T T' : Finset Rec} (h : T ⊆ T') : sumW T ≤ sumW T' :=
  Finset.sum_le_sum_of_subset h

theorem ind_congr {p r : Prop} (h : p ↔ r) : ind p = ind r := by
  unfold ind; simp only [h]

theorem ind_or_le (p r : Prop) : ind (p ∨ r) ≤ ind p + ind r := by
  unfold ind
  by_cases hp : p <;> by_cases hr : r <;> simp [hp, hr]

theorem ind_exists_some (i : ℕ) (P : ℕ → Prop) :
    ind (∃ i', some i = some i' ∧ P i') = ind (P i) := by
  apply ind_congr; simp

theorem ind_exists_none (P : ℕ → Prop) :
    ind (∃ i', (none : Option ℕ) = some i' ∧ P i') = 0 := by
  simp [ind]

theorem w_mul_ind_le (p : Prop) [Decidable p] : w * ind p ≤ if p then w else 0 := by
  unfold ind; split_ifs <;> simp

/-- Averaging over a fresh answer commutes with a weighted sum over records. -/
theorem avg_sum_comm (T : Finset Rec) (f : Rec → BitVec hashBits → ℝ≥0∞) :
    ∑ u, (Fintype.card (BitVec hashBits) : ℝ≥0∞)⁻¹ * ∑ ξ ∈ T, w * f ξ u =
      ∑ ξ ∈ T, w * ∑ u, (Fintype.card (BitVec hashBits) : ℝ≥0∞)⁻¹ * f ξ u := by
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun ξ _ => Finset.sum_congr rfl fun u _ => ?_
  ring

theorem avg_const (X : ℝ≥0∞) :
    ∑ _u : BitVec hashBits, (Fintype.card (BitVec hashBits) : ℝ≥0∞)⁻¹ * X = X :=
  sum_inv_card_mul X

/-- Summing a per-record charge of `ε` with the weights `w`. -/
theorem sum_w_mul_le_add (T : Finset Rec) (a b : Rec → ℝ≥0∞) (h : ∀ ξ ∈ T, a ξ ≤ b ξ + ε) :
    ∑ ξ ∈ T, w * a ξ ≤ ∑ ξ ∈ T, w * b ξ + ε * sumW T := by
  unfold sumW
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun ξ hξ => ?_
  rw [mul_comm ε w, ← mul_add]
  exact mul_le_mul_right (h ξ hξ) w

/-- Summing a general per-record charge with the weights. -/
theorem sum_w_mul_le_add_charge (δ : ℝ≥0∞) (T : Finset Rec)
    (a b : Rec → ℝ≥0∞) (h : ∀ ξ ∈ T, a ξ ≤ b ξ + δ) :
    ∑ ξ ∈ T, w * a ξ ≤ ∑ ξ ∈ T, w * b ξ + δ * sumW T := by
  unfold sumW
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun ξ hξ => ?_
  rw [mul_comm δ w, ← mul_add]
  exact mul_le_mul_right (h ξ hξ) w

/-- A fresh answer can only create a hit at the queried point. -/
theorem hits_avg_le (T : Finset Rec) (f : Rec → Cache) (c : Cache) (q : Query) :
    ∑ u, (Fintype.card (BitVec hashBits) : ℝ≥0∞)⁻¹ *
        ∑ ξ ∈ T, w * ind (Cache.Hits (c.cacheQuery q u) (f ξ)) ≤
      ∑ ξ ∈ T, w * ind (Cache.Hits c (f ξ)) + ∑ ξ ∈ T, w * ind ((f ξ q).isSome) := by
  rw [avg_sum_comm, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun ξ _ => ?_
  rw [← mul_add]
  refine mul_le_mul_right ?_ w
  calc ∑ u, (Fintype.card (BitVec hashBits) : ℝ≥0∞)⁻¹ *
        ind (Cache.Hits (c.cacheQuery q u) (f ξ))
      ≤ ∑ _u : BitVec hashBits, (Fintype.card (BitVec hashBits) : ℝ≥0∞)⁻¹ *
          (ind (Cache.Hits c (f ξ)) + ind ((f ξ q).isSome)) := by
        refine Finset.sum_le_sum fun u _ => mul_le_mul_right ?_ _
        rw [ind_congr (Cache.hits_cacheQuery c (f ξ) q u)]
        exact ind_or_le _ _
    _ = _ := sum_inv_card_mul _

/-- No hit at a point absent from every `f ξ`. -/
theorem hits_avg_eq (T : Finset Rec) (f : Rec → Cache) (c : Cache) (q : Query)
    (hf : ∀ ξ, f ξ q = none) :
    ∑ u, (Fintype.card (BitVec hashBits) : ℝ≥0∞)⁻¹ *
        ∑ ξ ∈ T, w * ind (Cache.Hits (c.cacheQuery q u) (f ξ)) =
      ∑ ξ ∈ T, w * ind (Cache.Hits c (f ξ)) := by
  rw [← avg_const (∑ ξ ∈ T, w * ind (Cache.Hits c (f ξ)))]
  refine Finset.sum_congr rfl fun u _ =>
    congrArg ((Fintype.card (BitVec hashBits) : ℝ≥0∞)⁻¹ * ·)
      (Finset.sum_congr rfl fun ξ _ => congrArg (w * ·) (ind_congr ?_))
  simp only [Cache.hits_cacheQuery, hf, Option.isSome_none, Bool.false_eq_true, or_false]

theorem spr_avg_le (T : Finset Rec) (c : Cache) (q : Query) (hq : c q = none) :
    ∑ u, (Fintype.card (BitVec hashBits) : ℝ≥0∞)⁻¹ *
        ∑ ξ ∈ T, w * ind (Spr (c.cacheQuery q u) ξ) ≤
      ∑ ξ ∈ T, w * ind (Spr c ξ) + (ε * blockCost q.1) * sumW T := by
  rw [avg_sum_comm]
  exact sum_w_mul_le_add_charge (ε * blockCost q.1) T _ _ fun ξ _ => spr_charge c ξ q hq

theorem spr_avg_eq (T : Finset Rec) (c : Cache) (u₀ : EncInput) :
    ∑ u, (Fintype.card (BitVec hashBits) : ℝ≥0∞)⁻¹ *
        ∑ ξ ∈ T, w * ind (Spr (c.cacheQuery (encQuery u₀) u) ξ) =
      ∑ ξ ∈ T, w * ind (Spr c ξ) := by
  rw [← avg_const (∑ ξ ∈ T, w * ind (Spr c ξ))]
  refine Finset.sum_congr rfl fun u _ =>
    congrArg ((Fintype.card (BitVec hashBits) : ℝ≥0∞)⁻¹ * ·)
      (Finset.sum_congr rfl fun ξ _ => congrArg (w * ·) (ind_congr ?_))
  exact spr_cacheQuery_enc c ξ u₀ u

theorem hits_charge_A' (pk : BitVec 128) {T : Finset Rec} (hT : T ⊆ fiberA pk) (q : Query) :
    ∑ ξ ∈ T, w * ind ((kc ξ q).isSome) ≤ ε * sumW (fiberA pk) :=
  calc ∑ ξ ∈ T, w * ind ((kc ξ q).isSome)
      ≤ ∑ ξ ∈ T, (if (kc ξ q).isSome then w else 0) :=
        Finset.sum_le_sum fun _ _ => w_mul_ind_le _
    _ ≤ ∑ ξ ∈ fiberA pk, (if (kc ξ q).isSome then w else 0) := Finset.sum_le_sum_of_subset hT
    _ ≤ ε * sumW (fiberA pk) := hits_charge_A pk q

theorem hits_charge_B' {Ac : Finset Name} (hAc : IsCut Ac) (dt : Data) {T : Finset Rec}
    (hT : T ⊆ fiberB Ac dt) (q : Query) :
    ∑ ξ ∈ T, w * ind ((fHid (some Ac) ξ q).isSome) ≤ ε * sumW (fiberB Ac dt) :=
  calc ∑ ξ ∈ T, w * ind ((fHid (some Ac) ξ q).isSome)
      ≤ ∑ ξ ∈ T, (if (fHid (some Ac) ξ q).isSome then w else 0) :=
        Finset.sum_le_sum fun _ _ => w_mul_ind_le _
    _ ≤ ∑ ξ ∈ fiberB Ac dt, (if (fHid (some Ac) ξ q).isSome then w else 0) :=
        Finset.sum_le_sum_of_subset hT
    _ ≤ ε * sumW (fiberB Ac dt) := hits_charge_B hAc dt q


theorem authPotential_eq (T : Finset Rec) (A? : Option (Finset Name)) (c : Cache) :
    authPotential T A? c = (∑ ξ ∈ T, w * ind (Cache.Hits c (fHid A? ξ))) +
      ∑ ξ ∈ T, w * ind (Spr c ξ) := by
  simp only [authPotential, mul_add, Finset.sum_add_distrib]

theorem authPotential_index (T : Finset Rec) (A? : Option (Finset Name))
    (c : Cache) (u₀ : EncInput) :
    (∑ u, (Fintype.card (BitVec hashBits) : ℝ≥0∞)⁻¹ *
      authPotential T A? (c.cacheQuery (encQuery u₀) u)) = authPotential T A? c := by
  simp only [authPotential_eq, mul_add, Finset.sum_add_distrib]
  rw [hits_avg_eq _ _ _ _ (fun ξ => fHid_enc A? ξ u₀), spr_avg_eq]

theorem authPotential_charge {Ac : Finset Name} (hAc : IsCut Ac) (dt : Data)
    {T : Finset Rec} (hT : T ⊆ fiberB Ac dt) (c : Cache) (q : Query) (hq : c q = none) :
    (∑ u, (Fintype.card (BitVec hashBits) : ℝ≥0∞)⁻¹ *
      authPotential T (some Ac) (c.cacheQuery q u)) ≤
      authPotential T (some Ac) c + authRate * sumW (fiberB Ac dt) * queryCost (.inr q) := by
  simp only [authPotential_eq, mul_add, Finset.sum_add_distrib]
  have hh := (hits_avg_le T (fHid (some Ac)) c q).trans
    (add_le_add_right (hits_charge_B' hAc dt hT q) _)
  have hs := (spr_avg_le T c q hq).trans
    (add_le_add_right (mul_le_mul_right (sumW_mono hT) (ε * blockCost q.1)) _)
  have hc := mul_le_mul_right (authentication_charge_budget q) (sumW (fiberB Ac dt))
  calc
    _ ≤ ((∑ ξ ∈ T, w * ind (Cache.Hits c (fHid (some Ac) ξ))) + ε * sumW (fiberB Ac dt)) +
        ((∑ ξ ∈ T, w * ind (Spr c ξ)) + (ε * blockCost q.1) * sumW (fiberB Ac dt)) := add_le_add hh hs
    _ = ((∑ ξ ∈ T, w * ind (Cache.Hits c (fHid (some Ac) ξ))) +
        (∑ ξ ∈ T, w * ind (Spr c ξ))) + (ε + ε * blockCost q.1) * sumW (fiberB Ac dt) := by ring
    _ ≤ _ := by
      apply add_le_add_right
      simpa only [authRate, queryCost, mul_assoc, mul_comm, mul_left_comm] using hc

/-- Only the weighted index analysis may supply these hypotheses. Non-index
queries leave this potential unchanged, so authentication and index share a budget. -/
structure IndexCharge (J : Cache → ℝ≥0∞) (rate : ℝ≥0∞) (I : Cache → ℕ → Prop) : Prop where
  fresh : ∀ c b u₀, I c b → c (encQuery u₀) = none → queryCost (.inr (encQuery u₀)) ≤ b →
    (∑ u, (Fintype.card (BitVec hashBits) : ℝ≥0∞)⁻¹ * J (c.cacheQuery (encQuery u₀) u)) ≤
      J c + rate * queryCost (.inr (encQuery u₀))
  other : ∀ c q, (∀ u₀ : EncInput, q ≠ encQuery u₀) → ∀ u, J (c.cacheQuery q u) = J c

def jointPotential (T : Finset Rec) (A? : Option (Finset Name)) (J : Cache → ℝ≥0∞)
    (c : Cache) : ℝ≥0∞ := authPotential T A? c + sumW T * J c

theorem avg_mul (a : ℝ≥0∞) (f : BitVec hashBits → ℝ≥0∞) :
    (∑ u, (Fintype.card (BitVec hashBits) : ℝ≥0∞)⁻¹ * (a * f u)) =
      a * ∑ u, (Fintype.card (BitVec hashBits) : ℝ≥0∞)⁻¹ * f u := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u _
  ring

theorem jointPotential_charge {Ac : Finset Name} (hAc : IsCut Ac) (dt : Data)
    {T : Finset Rec} (hT : T ⊆ fiberB Ac dt) (J : Cache → ℝ≥0∞) (rate : ℝ≥0∞)
    (I : Cache → ℕ → Prop) (hJ : IndexCharge J rate I) :
    ∀ c b q, I c b → c q = none → queryCost (.inr q) ≤ b →
    (∑ u, (Fintype.card (BitVec hashBits) : ℝ≥0∞)⁻¹ * jointPotential T (some Ac) J (c.cacheQuery q u)) ≤
      jointPotential T (some Ac) J c +
        max authRate rate * sumW (fiberB Ac dt) * queryCost (.inr q) := by
  intro c b q hI hq hcost
  simp only [jointPotential, mul_add, Finset.sum_add_distrib]
  by_cases he : ∃ u₀ : EncInput, q = encQuery u₀
  · obtain ⟨u₀, rfl⟩ := he
    rw [authPotential_index, avg_mul]
    have h := mul_le_mul_right (hJ.fresh c b u₀ hI hq hcost) (sumW T)
    refine (add_le_add_right h _).trans ?_
    rw [mul_add]
    calc
      _ = authPotential T (some Ac) c + sumW T * J c + rate * sumW T * queryCost (.inr (encQuery u₀)) := by ring
      _ ≤ _ := by gcongr; exact le_max_right _ _; exact sumW_mono hT
  · have hne : ∀ u₀ : EncInput, q ≠ encQuery u₀ := by simpa only [not_exists] using he
    simp only [hJ.other c q hne, avg_const]
    have h := authPotential_charge hAc dt hT c q hq
    refine (add_le_add_left h _).trans ?_
    calc
      _ = authPotential T (some Ac) c + sumW T * J c + authRate * sumW (fiberB Ac dt) * queryCost (.inr q) := by ring
      _ ≤ _ := by gcongr; exact le_max_left _ _

/-- A single paid OracleComp continuation pays the maximum query-type rate,
not the sum of two separate full-budget estimates. -/
theorem joint_continuation {α : Type} {Ac : Finset Name} (hAc : IsCut Ac) (dt : Data)
    {T : Finset Rec} (hT : T ⊆ fiberB Ac dt) (J : Cache → ℝ≥0∞) (rate : ℝ≥0∞)
    (I : Cache → ℕ → Prop)
    (hIf : ∀ c b q, I c b → c q = none → queryCost (.inr q) ≤ b →
      ∀ u, I (c.cacheQuery q u) (b-queryCost (.inr q)))
    (hIc : ∀ c b q, I c b → (c q).isSome → queryCost (.inr q) ≤ b → I c (b-queryCost (.inr q)))
    (hJ : IndexCharge J rate I) (oa : OracleComp Spec α)
    (F : α → Cache → ℝ≥0∞) (hF : ∀ x c, F x c ≤ jointPotential T (some Ac) J c)
    (c : Cache) (b : ℕ) (hI : I c b) (hB : CostAtMost oa b) :
    E (run oa c) (fun p => F p.1 p.2) ≤ jointPotential T (some Ac) J c +
      max authRate rate * sumW (fiberB Ac dt) * b :=
  master_single (max authRate rate * sumW (fiberB Ac dt)) (jointPotential T (some Ac) J)
    I hIf hIc (jointPotential_charge hAc dt hT J rate I hJ) oa F hF c b hI hB

end OptimalOTS.WeightedConstruction.WideForest
#print axioms OptimalOTS.WeightedConstruction.WideForest.authPotential_charge
#print axioms OptimalOTS.WeightedConstruction.WideForest.joint_continuation
