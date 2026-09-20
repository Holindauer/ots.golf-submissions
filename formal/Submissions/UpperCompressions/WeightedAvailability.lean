import Submissions.UpperCompressions.WeightedSampling
import Submissions.UpperCompressions.Master

/-! Availability of the actual with-replacement loop, retaining shared-oracle
memoization. Cached nonce probability is paid inside the per-trial failure
factor; no additive nonce-collision error is used. -/

open OracleSpec OracleComp OracleComp.EvalDist ENNReal
noncomputable section
open scoped Classical

namespace OptimalOTS.WeightedSampling.Availability

variable {M : ℕ}

theorem nonce_suffix (m : Message) (η : Nonce n) : (m++η).setWidth n = η := by
  ext j hj
  simp [BitVec.getElem_setWidth,BitVec.getLsbD_append,hj]

theorem nonce_query_inj (m : Message) {η ζ : Nonce n}
    (h : (⟨msgBits+n,m++η⟩ : Query) = ⟨msgBits+n,m++ζ⟩) : η = ζ := by
  have hh := congrArg (fun q : Query => q.2.setWidth n) h
  simpa only [nonce_suffix] using hh

theorem fresh_insert (m : Message) (c : Cache) (tried : Finset (Nonce n))
    (hf : ∀ η ∉ tried, c ⟨msgBits+n,m++η⟩ = none) (η : Nonce n) (w : BitVec hashBits) :
    ∀ ζ ∉ insert η tried, (c.cacheQuery ⟨msgBits+n,m++η⟩ w) ⟨msgBits+n,m++ζ⟩ = none := by
  intro ζ hζ
  have hne : (⟨msgBits+n,m++ζ⟩ : Query) ≠ ⟨msgBits+n,m++η⟩ := by
    intro h
    have he := nonce_query_inj m h
    exact hζ (he ▸ Finset.mem_insert_self η tried)
  rw [QueryCache.cacheQuery_of_ne _ _ hne]
  exact hf ζ (fun h => hζ (Finset.mem_insert_of_mem h))

theorem run_hash_fresh {b : ℕ} (u : BitVec b) (c : Cache)
    (h : c ⟨b,u⟩ = none) : run (hash u) c =
      ($ᵗ BitVec hashBits) >>= fun w => pure (w,c.cacheQuery ⟨b,u⟩ w) := by
  unfold hash run
  rw [simulateQ_spec_query]
  exact oracleImpl_run_inr_none h

theorem uniform_tried (n : ℕ) (tried : Finset (Nonce n)) (a : ℝ≥0∞) :
    E ($ᵗ BitVec n) (fun η => if η ∈ tried then a else 0) =
      (tried.card : ℝ≥0∞) / 2^n * a := by
  rw [E_uniform]
  simp only [mul_ite,mul_zero]
  rw [← Finset.sum_filter]
  simp only [Finset.filter_mem_eq_inter,Finset.univ_inter,Finset.sum_const,
    nsmul_eq_mul,Fintype.card_bitVec,Nat.cast_pow,Nat.cast_ofNat]
  rw [div_eq_mul_inv,mul_assoc]

theorem uniform_miss_plus (n : ℕ) (tried : Finset (Nonce n)) (miss a : ℝ≥0∞) :
    E ($ᵗ BitVec n) (fun η => miss*a + (if η ∈ tried then a else 0)) =
      (miss + (tried.card : ℝ≥0∞)/2^n)*a := by
  rw [E_uniform]
  simp only [mul_add,Finset.sum_add_distrib]
  rw [sum_inv_card_mul]
  have hh := uniform_tried n tried a
  rw [E_uniform] at hh
  rw [hh,add_mul]

theorem none_best (rank : α → ℕ) (a b : Option α) :
    (if (best rank a b).isNone then (1 : ℝ≥0∞) else 0) =
      if a.isNone then (if b.isNone then 1 else 0) else 0 := by
  cases a <;> cases b <;> simp [best]
  split_ifs <;> simp

theorem after_bound (n : ℕ) (decode : BitVec hashBits → Option (Fin M))
    (tier : Fin M → ℕ) (m : Message) (k : ℕ) (c : Cache) (η : Nonce n)
    (w : BitVec hashBits) (a : ℝ≥0∞)
    (h : E (run (loop n decode tier m k) c) (fun p => if p.1.isNone then 1 else 0) ≤ a) :
    E (run (loop n decode tier m k) c)
      (fun p => if (best (fun s => tier s.2) (candidate decode η w) p.1).isNone
        then 1 else 0) ≤ if (decode w).isNone then a else 0 := by
  simp_rw [none_best]
  cases hd : decode w with
  | none => simpa [candidate,hd] using h
  | some i => simpa [candidate,hd] using E_const_le (run (loop n decode tier m k) c) 0

/-- A cache with at mosttried.card possibly occupied row slots. -/
theorem loop_failure (n : ℕ) (decode : BitVec hashBits → Option (Fin M))
    (tier : Fin M → ℕ) (m : Message) (L : ℕ) (miss : ℝ≥0∞)
    (hmiss : ∀ a : ℝ≥0∞, E ($ᵗ BitVec hashBits)
      (fun w => if (decode w).isNone then a else 0) ≤ miss*a) :
    ∀ k (tried : Finset (Nonce n)) (c : Cache), tried.card+k ≤ L →
      (∀ η ∉ tried, c ⟨msgBits+n,m++η⟩ = none) →
      E (run (loop n decode tier m k) c) (fun p => if p.1.isNone then 1 else 0) ≤
        (miss + (L : ℝ≥0∞)/2^n)^k := by
  intro k
  induction k with
  | zero => intro tried c _ _; simp [loop,run_pure]
  | succ k ih =>
    intro tried c hL hf
    let a : ℝ≥0∞ := (miss+(L : ℝ≥0∞)/2^n)^k
    have hcard (η : Nonce n) : (insert η tried).card+k ≤ L := by
      have := Finset.card_insert_le η tried
      omega
    have hstep (η : Nonce n) :
        E (run (hash (m++η)) c) (fun q =>
          E (run (loop n decode tier m k) q.2) (fun p =>
            if (best (fun s => tier s.2) (candidate decode η q.1) p.1).isNone then 1 else 0)) ≤
          miss*a + (if η ∈ tried then a else 0) := by
      cases hc : c ⟨msgBits+n,m++η⟩ with
      | none =>
        rw [run_hash_fresh _ c hc,E_bind]
        simp only [E_pure]
        have hpt (w : BitVec hashBits) := after_bound n decode tier m k
          (c.cacheQuery ⟨msgBits+n,m++η⟩ w) η w a
          (ih (insert η tried) _ (hcard η) (fresh_insert m c tried hf η w))
        exact ((E_mono _ hpt).trans (hmiss a)).trans (le_add_right le_rfl)
      | some w =>
        rw [run_hash_cached _ c w hc,E_pure]
        have hη : η ∈ tried := by
          by_contra h
          rw [hf η h] at hc
          cases hc
        have hprev : E (run (loop n decode tier m k) c)
            (fun p => if p.1.isNone then 1 else 0) ≤ a :=
          ih (insert η tried) c (hcard η)
            (fun ζ hζ => hf ζ (fun h => hζ (Finset.mem_insert_of_mem h)))
        have ha := after_bound n decode tier m k c η w a hprev
        have ha' : (if (decode w).isNone then a else 0) ≤ a := by split_ifs <;> simp
        exact (ha.trans ha').trans (by rw [if_pos hη]; exact le_add_left le_rfl)
    rw [run_loop_succ,E_bind]
    simp only [E_bind,E_pure]
    calc
      _ ≤ E ($ᵗ BitVec n) (fun η => miss*a+(if η ∈ tried then a else 0)) := E_mono _ hstep
      _ = (miss+(tried.card : ℝ≥0∞)/2^n)*a := uniform_miss_plus n tried miss a
      _ ≤ (miss+(L : ℝ≥0∞)/2^n)*a := by
        apply mul_le_mul' _ le_rfl
        apply add_le_add le_rfl
        exact ENNReal.div_le_div_right (by exact_mod_cast (show tried.card ≤ L by omega)) _
      _ = _ := by dsimp [a]; rw [pow_succ,mul_comm]

#print axioms loop_failure
end OptimalOTS.WeightedSampling.Availability
