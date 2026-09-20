import Submissions.UpperCompressions.WideResample

/-! Per-compression authentication charges for129-bit internals and a128-bit
public root. These are event/fiber bounds; security-game integration remains separate. -/

open OracleSpec OracleComp ENNReal
noncomputable section
open scoped Classical

namespace OptimalOTS.WeightedConstruction.WideForest
open OptimalOTS.Dag Name

/-- The root has twice the spurious-match probability of an internal node. -/
def sprRate (h : Name) : ℝ≥0∞ := if h = rh then ε + ε else ε

theorem bindingWidth_le (h : Name) : bindingWidth h ≤ 256 := by
  simp only [bindingWidth]
  split_ifs <;> omega

theorem binding_fiber (h : Name) (a : BitVec (bindingWidth h)) :
    (Finset.univ.filter fun b : BitVec 256 => bindingValue h b = a).card =
      2 ^ (256 - bindingWidth h) :=
  TruncFiber.card_filter_setWidth (bindingWidth_le h) a

theorem inv_card_binding (h : Name) :
    (Fintype.card (BitVec 256) : ℝ≥0∞)⁻¹ *
      ((2 ^ (256 - bindingWidth h) : ℕ) : ℝ≥0∞) = sprRate h := by
  by_cases hh : h = rh
  · simp only [bindingWidth, sprRate, if_pos hh]
    change (Fintype.card (BitVec 256) : ℝ≥0∞)⁻¹ * ((2 ^ 128 : ℕ) : ℝ≥0∞) = ε + ε
    have he : (2 : ℕ)^128 = 2^127 + 2^127 := by
      rw [show (128 : ℕ) = 127+1 from rfl, pow_succ, mul_two]
    rw [he, Nat.cast_add, mul_add, inv_card_bitVec_mul_two_pow]
  · simp only [bindingWidth, sprRate, if_neg hh]
    exact inv_card_bitVec_mul_two_pow

theorem epsilon_le_query_cost (q : Query) : ε ≤ ε * (blockCost q.1 : ℝ≥0∞) := by
  have hc : (1 : ℝ≥0∞) ≤ (blockCost q.1 : ℝ≥0∞) := by
    exact_mod_cast (Nat.le_max_left 1 ((q.1 + blockBits - 1) / blockBits))
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hc (show (0 : ℝ≥0∞) ≤ ε from zero_le)

/-- The root's128-bit match charge is covered by its actual five-compression input. -/
theorem sprRate_le_query_cost {h p : Name} (hp : hashParent h = some p)
    (q : Query) (hlen : q.1 = p.len) : sprRate h ≤ ε * (blockCost q.1 : ℝ≥0∞) := by
  by_cases hh : h = rh
  · subst h
    simp only [hashParent, Option.some.injEq] at hp
    subst p
    rw [sprRate, if_pos rfl, hlen]
    change ε + ε ≤ ε * (blockCost 2338 : ℝ≥0∞)
    have hc : blockCost 2338 = 5 := by norm_num [blockCost, blockBits]
    rw [hc, ← mul_two]
    exact mul_le_mul_of_nonneg_left (by norm_num : (2 : ℝ≥0∞) ≤ 5) zero_le
  · rw [sprRate, if_neg hh]
    exact epsilon_le_query_cost q

/-- A fresh answer increases the spurious-image event by at most2^-129 per
paid compression, including the root's distinct128-bit endpoint. -/
theorem spr_charge (c : Cache) (ξ : Rec) (q : Query) (_hq : c q = none) :
    ∑ b : BitVec 256, (Fintype.card (BitVec 256) : ℝ≥0∞)⁻¹ *
      (if Spr (c.cacheQuery q b) ξ then 1 else 0) ≤
        (if Spr c ξ then 1 else 0) + ε * (blockCost q.1 : ℝ≥0∞) := by
  by_cases hs : Spr c ξ
  · rw [if_pos hs]
    calc ∑ b : BitVec 256, (Fintype.card (BitVec 256) : ℝ≥0∞)⁻¹ *
          (if Spr (c.cacheQuery q b) ξ then 1 else 0)
        ≤ ∑ _b : BitVec 256, (Fintype.card (BitVec 256) : ℝ≥0∞)⁻¹ * 1 := by
          refine Finset.sum_le_sum fun b _ => mul_le_mul_of_nonneg_left ?_ zero_le
          split_ifs <;> simp
      _ = 1 := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
            ENNReal.mul_inv_cancel (by exact_mod_cast Fintype.card_ne_zero)
              (ENNReal.natCast_ne_top _)]
      _ ≤ _ := le_self_add
  · rw [if_neg hs, zero_add]
    have key : ∀ b, Spr (c.cacheQuery q b) ξ →
        ∃ h p, hashParent h = some p ∧ q.1 = p.len ∧ tagNat q = h.idx ∧
          bindingValue h b = bindingValue h (ξ.2 h.fin) := by
      rintro b ⟨h, p, hp, u, hu, htag, b', hb', ht⟩
      by_cases hqq : (⟨p.len, u⟩ : Query) = q
      · subst hqq
        rw [QueryCache.cacheQuery_self] at hb'
        obtain rfl := Option.some.inj hb'
        exact ⟨h, p, hp, rfl, htag, ht⟩
      · rw [QueryCache.cacheQuery_of_ne _ _ hqq] at hb'
        exact (hs ⟨h, p, hp, u, hu, htag, b', hb', ht⟩).elim
    by_cases hex : ∃ h₀ p₀, hashParent h₀ = some p₀ ∧ q.1 = p₀.len ∧ tagNat q = h₀.idx
    · obtain ⟨h₀, p₀, hp₀, hlen₀, hq₀⟩ := hex
      have key' : ∀ b, Spr (c.cacheQuery q b) ξ →
          bindingValue h₀ b = bindingValue h₀ (ξ.2 h₀.fin) := by
        intro b hb
        obtain ⟨h, p, hp, hlen, hq', ht⟩ := key b hb
        have he : h₀ = h := Name.idx_injective (hq₀.symm.trans hq')
        subst he
        exact ht
      calc ∑ b : BitVec 256, (Fintype.card (BitVec 256) : ℝ≥0∞)⁻¹ *
            (if Spr (c.cacheQuery q b) ξ then 1 else 0)
          ≤ ∑ b : BitVec 256, (Fintype.card (BitVec 256) : ℝ≥0∞)⁻¹ *
            (if bindingValue h₀ b = bindingValue h₀ (ξ.2 h₀.fin) then 1 else 0) := by
            refine Finset.sum_le_sum fun b _ => mul_le_mul_of_nonneg_left ?_ zero_le
            split_ifs with h1 h2
            · exact le_rfl
            · exact absurd (key' b h1) h2
            · exact zero_le_one
            · exact le_rfl
        _ = (Fintype.card (BitVec 256) : ℝ≥0∞)⁻¹ *
            ((Finset.univ.filter fun b : BitVec 256 =>
              bindingValue h₀ b = bindingValue h₀ (ξ.2 h₀.fin)).card : ℝ≥0∞) := by
            rw [← Finset.mul_sum, Finset.sum_boole]
        _ = sprRate h₀ := by rw [binding_fiber, inv_card_binding]
        _ ≤ _ := sprRate_le_query_cost hp₀ q hlen₀
    · have hno : ∀ b, ¬ Spr (c.cacheQuery q b) ξ := fun b hb => by
        obtain ⟨h, p, hp, hlen, htag, _⟩ := key b hb
        exact hex ⟨h, p, hp, hlen, htag⟩
      rw [Finset.sum_eq_zero fun b _ => by rw [if_neg (hno b), mul_zero]]
      exact zero_le

theorem two_epsilon_eq_half_kappa : ε + ε = (((2 : ℝ≥0∞)^127)⁻¹) / 2 := by
  have hstep (n : ℕ) : ((2 : ℝ≥0∞)^(n+1))⁻¹ = ((2 : ℝ≥0∞)^n)⁻¹ / 2 := by
    rw [pow_succ, ENNReal.mul_inv (Or.inr (by norm_num : (2 : ℝ≥0∞) ≠ ⊤))
      (Or.inr two_ne_zero), div_eq_mul_inv]
  calc ε + ε = ((2 : ℝ≥0∞)^128)⁻¹ / 2 + ((2 : ℝ≥0∞)^128)⁻¹ / 2 := by
        rw [ε, show (129 : ℕ) = 128+1 from rfl, hstep]
    _ = ((2 : ℝ≥0∞)^128)⁻¹ := ENNReal.add_halves _
    _ = _ := hstep 127

/-- Combining the hidden-input and spurious-image charges costs κ/2 per compression. -/
theorem authentication_charge_budget (q : Query) :
    ε + ε * (blockCost q.1 : ℝ≥0∞) ≤
      ((((2 : ℝ≥0∞)^127)⁻¹) / 2) * (blockCost q.1 : ℝ≥0∞) := by
  calc ε + ε * (blockCost q.1 : ℝ≥0∞)
      ≤ ε * (blockCost q.1 : ℝ≥0∞) + ε * (blockCost q.1 : ℝ≥0∞) :=
        add_le_add (epsilon_le_query_cost q) le_rfl
    _ = (ε+ε) * (blockCost q.1 : ℝ≥0∞) := (add_mul ..).symm
    _ = _ := by rw [two_epsilon_eq_half_kappa]

end OptimalOTS.WeightedConstruction.WideForest

#print axioms OptimalOTS.WeightedConstruction.WideForest.spr_charge
#print axioms OptimalOTS.WeightedConstruction.WideForest.authentication_charge_budget
