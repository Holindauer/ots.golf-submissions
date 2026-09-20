import Submissions.UpperCompressions.FiniteKernelConcentration

/-! An explicit first-hit/absorbing-state construction over adaptive kernels.
This proves a finite-time maximum without unioning over time prefixes. The
caller still supplies the actual oracle kernel and local exponential drift. -/

noncomputable section
open scoped Classical
namespace WeightedFirstHit
open WeightedKernel

variable {S : Type*}

inductive Status where
  | active
  | hit
  | killed
  deriving DecidableEq

/-- Frozen time and state preserve the exponential potential after stopping.
The hit status carries its event evidence, so no reachability assumption is
silently substituted for a theorem about all stopped states. -/
structure StoppedState (hit kill : ℕ → S → Prop) where
  clock : ℕ
  value : S
  status : Status
  valid : status = .hit → hit clock value
  safe : status = .active → ¬hit clock value ∧ ¬kill clock value

def classify (hit kill : ℕ → S → Prop) (t : ℕ) (s : S) : StoppedState hit kill :=
  if hh : hit t s then ⟨t, s, .hit, fun _ => hh, by simp⟩
  else if hk : kill t s then ⟨t, s, .killed, by simp, by simp⟩
  else ⟨t, s, .active, by simp, fun _ => ⟨hh, hk⟩⟩

@[simp] theorem classify_clock (hit kill : ℕ → S → Prop) (t : ℕ) (s : S) :
    (classify hit kill t s).clock = t := by
  unfold classify
  split_ifs <;> rfl

@[simp] theorem classify_value (hit kill : ℕ → S → Prop) (t : ℕ) (s : S) :
    (classify hit kill t s).value = s := by
  unfold classify
  split_ifs <;> rfl

@[simp] theorem classify_status_hit (hit kill : ℕ → S → Prop) (t : ℕ) (s : S)
    (hh : hit t s) : (classify hit kill t s).status = .hit := by simp [classify, hh]

@[simp] theorem classify_status_killed (hit kill : ℕ → S → Prop) (t : ℕ) (s : S)
    (hh : ¬hit t s) (hk : kill t s) : (classify hit kill t s).status = .killed := by
  simp [classify, hh, hk]

@[simp] theorem classify_status_active (hit kill : ℕ → S → Prop) (t : ℕ) (s : S)
    (hh : ¬hit t s) (hk : ¬kill t s) : (classify hit kill t s).status = .active := by
  simp [classify, hh, hk]

/-- Active states take one original transition and classify the result; stopped
states take a deterministic self-loop, freezing their clock and potential. -/
def stoppedKernel (K : Kernels S) (hit kill : ℕ → S → Prop) : Kernels (StoppedState hit kill) :=
  fun _ st => if st.status = .active then
    (K st.clock st.value).comp
      (LinearMap.pi (fun s' => LinearMap.proj (classify hit kill (st.clock+1) s')))
    else LinearMap.proj st

@[simp] theorem stoppedKernel_apply (K : Kernels S) (hit kill : ℕ → S → Prop)
    (t : ℕ) (st : StoppedState hit kill) (f : StoppedState hit kill → ℝ) :
    stoppedKernel K hit kill t st f =
      if st.status = .active then
        K st.clock st.value (fun s' => f (classify hit kill (st.clock+1) s'))
      else f st := by
  unfold stoppedKernel
  split_ifs <;> rfl

theorem stoppedKernel_mono (K : Kernels S)
    (hmono : ∀ t s f g, (∀ s', f s' ≤ g s') → K t s f ≤ K t s g)
    (hit kill : ℕ → S → Prop) (t : ℕ) (st : StoppedState hit kill)
    (f g : StoppedState hit kill → ℝ) (hfg : ∀ s', f s' ≤ g s') :
    stoppedKernel K hit kill t st f ≤ stoppedKernel K hit kill t st g := by
  simp only [stoppedKernel_apply]
  split_ifs
  · exact hmono _ _ _ _ (fun s' => hfg _)
  · exact hfg st

theorem stoppedKernel_one (K : Kernels S)
    (hnorm : ∀ t s, K t s (fun _ => 1) = 1)
    (hit kill : ℕ → S → Prop) (t : ℕ) (st : StoppedState hit kill) :
    stoppedKernel K hit kill t st (fun _ => 1) = 1 := by
  simp only [stoppedKernel_apply]
  split_ifs
  · exact hnorm _ _
  · rfl

def hitIndicator (hit kill : ℕ → S → Prop) (st : StoppedState hit kill) : ℝ :=
  if st.status = .hit then 1 else 0

/-- Direct recursive event probability: hit has priority over kill. For the
usual variance/good-event stopping, the predicates should be chosen disjoint. -/
def firstHit (K : Kernels S) (hit kill : ℕ → S → Prop) : ℕ → ℕ → S → ℝ
  | 0, t, s => if hit t s then 1 else 0
  | n+1, t, s => if hit t s then 1 else if kill t s then 0
      else K t s (fun s' => firstHit K hit kill n (t+1) s')

theorem iterate_stopped (K : Kernels S) (hit kill : ℕ → S → Prop)
    (st : StoppedState hit kill) (hstop : st.status ≠ .active)
    (n t : ℕ) (f : StoppedState hit kill → ℝ) :
    iterate (stoppedKernel K hit kill) n t st f = f st := by
  induction n generalizing t with
  | zero => rfl
  | succ n ih =>
    rw [iterate_succ, stoppedKernel_apply, if_neg hstop]
    exact ih (t+1)

/-- Exact equality between the absorbing construction and the first-hit-before-
kill event, including the initial time and every time through the horizon. -/
theorem iterate_hit_eq (K : Kernels S) (hit kill : ℕ → S → Prop)
    (n t u : ℕ) (s : S) :
    iterate (stoppedKernel K hit kill) n u (classify hit kill t s) (hitIndicator hit kill) =
      firstHit K hit kill n t s := by
  induction n generalizing t u s with
  | zero =>
    simp only [iterate_zero, firstHit, hitIndicator]
    by_cases hh : hit t s
    · simp [hh]
    · by_cases hk : kill t s <;> simp [classify, hh, hk]
  | succ n ih =>
    by_cases hh : hit t s
    · rw [iterate_stopped K hit kill _ (by simp [hh])]
      simp [firstHit, hitIndicator, hh]
    · by_cases hk : kill t s
      · rw [iterate_stopped K hit kill _ (by simp [hh, hk])]
        simp [firstHit, hitIndicator, hh, hk]
      · simp only [iterate_succ, stoppedKernel_apply, classify_status_active _ _ _ _ hh hk,
          if_true, classify_clock, classify_value, firstHit, if_neg hh, if_neg hk]
        congr 1
        funext s'
        exact ih (t+1) (u+1) s'

/-- Original exponential drift is preserved by the absorbing construction.
Both score and variance proxy use the stored stopping time. -/
theorem stopped_exponential_drift
    (K : Kernels S) (hit kill : ℕ → S → Prop)
    (Z W : ℕ → S → ℝ) (θ J : ℝ)
    (hstep : ∀ t s, ¬hit t s → ¬kill t s →
      K t s (fun s' => Real.exp (θ*Z (t+1) s'-θ^2*W (t+1) s'/(2*(1-θ*J/3)))) ≤
        Real.exp (θ*Z t s-θ^2*W t s/(2*(1-θ*J/3))))
    (t : ℕ) (st : StoppedState hit kill) :
    stoppedKernel K hit kill t st
      (fun st' => Real.exp (θ*Z st'.clock st'.value-θ^2*W st'.clock st'.value/(2*(1-θ*J/3)))) ≤
      Real.exp (θ*Z st.clock st.value-θ^2*W st.clock st.value/(2*(1-θ*J/3))) := by
  simp only [stoppedKernel_apply]
  split_ifs with hs
  · simpa only [classify_clock, classify_value] using
      hstep st.clock st.value (st.safe hs).1 (st.safe hs).2
  · exact le_rfl

/-- Maximal Freedman bound for a hit before an arbitrary killing condition.
There is no factor for the number of time prefixes. A hit can include W≤v;
killing can include W>v or failure of the stopped cache-good predicate. -/
theorem firstHit_freedman
    (K : Kernels S)
    (hmono : ∀ t s f g, (∀ s', f s' ≤ g s') → K t s f ≤ K t s g)
    (Z W : ℕ → S → ℝ) (s₀ : S) (n : ℕ) (a v J : ℝ)
    (ha : 0 < a) (hv : 0 < v) (hJ : 0 ≤ J)
    (hZ0 : Z 0 s₀ = 0) (hW0 : W 0 s₀ = 0)
    (hit kill : ℕ → S → Prop)
    (hstep : ∀ θ, 0 < θ → θ*J < 3 → ∀ t s, ¬hit t s → ¬kill t s →
      K t s (fun s' => Real.exp (θ*Z (t+1) s'-θ^2*W (t+1) s'/(2*(1-θ*J/3)))) ≤
        Real.exp (θ*Z t s-θ^2*W t s/(2*(1-θ*J/3))))
    (hZ : ∀ t s, hit t s → a ≤ Z t s) (hW : ∀ t s, hit t s → W t s ≤ v) :
    firstHit K hit kill n 0 s₀ ≤ Real.exp (-a^2/(2*(v+J*a/3))) := by
  let Ks := stoppedKernel K hit kill
  let Zs : ℕ → StoppedState hit kill → ℝ := fun _ st => Z st.clock st.value
  let Ws : ℕ → StoppedState hit kill → ℝ := fun _ st => W st.clock st.value
  have hz0 : Zs 0 (classify hit kill 0 s₀) = 0 := by simpa [Zs] using hZ0
  have hw0 : Ws 0 (classify hit kill 0 s₀) = 0 := by simpa [Ws] using hW0
  have hstepS : ∀ θ, 0 < θ → θ*J < 3 → ∀ t st,
      Ks t st (fun st' => Real.exp (θ*Zs (t+1) st'-θ^2*Ws (t+1) st'/(2*(1-θ*J/3)))) ≤
        Real.exp (θ*Zs t st-θ^2*Ws t st/(2*(1-θ*J/3))) := by
    intro θ hθ hθJ t st
    exact stopped_exponential_drift K hit kill Z W θ J (hstep θ hθ hθJ) t st
  have hx := finite_kernel_freedman Ks (stoppedKernel_mono K hmono hit kill)
    Zs Ws (classify hit kill 0 s₀) n a v J ha hv hJ hz0 hw0 hstepS
    (fun st => st.status = .hit)
    (fun st hs => hZ st.clock st.value (st.valid hs))
    (fun st hs => hW st.clock st.value (st.valid hs))
  change iterate (stoppedKernel K hit kill) n 0 (classify hit kill 0 s₀)
    (hitIndicator hit kill) ≤ _ at hx
  rw [iterate_hit_eq] at hx
  exact hx

#print axioms stoppedKernel_mono
#print axioms stoppedKernel_one
#print axioms iterate_stopped
#print axioms iterate_hit_eq
#print axioms stopped_exponential_drift
#print axioms firstHit_freedman

end WeightedFirstHit
