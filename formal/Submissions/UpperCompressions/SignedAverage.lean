import Submissions.UpperCompressions.SignedGameExpectation

/-! Joint averages over the actual completed-table all-L signer. These helpers
retain a specific signed nonce/class event while combining the graph and fresh
index analyses on identical public continuations and caches. -/
open OracleSpec OracleComp OracleComp.EvalDist ENNReal
noncomputable section
open scoped Classical
set_option maxRecDepth 10000
namespace OptimalOTS.WeightedConstruction.WideForest
open OptimalOTS.Dag Name WeightedReplacement WeightedSampling
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Finset.univ Finset.filter

abbrev IndexTable := BitVec (msgBits+86) → BitVec hashBits
abbrev SignedWinner := Option (Winner 86 WeightedSchedule.M)

def signedAverage (m : Message) (c : Cache) (k : ℕ) (b : SignedWinner)
    (F : IndexTable → Cache → ℝ≥0∞) : ℝ≥0∞ :=
  E ($ᵗ IndexTable) (fun g =>
    E (run (loop 86 WeightedSchedule.decode WeightedSchedule.tier m k)
      ((lengthSlice (msgBits+86)).preload c g)) (fun p => if p.1=b then F g p.2 else 0))

theorem signedAverage_mono_support (m : Message) (c : Cache) (k : ℕ) (b : SignedWinner)
    (F G : IndexTable → Cache → ℝ≥0∞)
    (h : ∀ g p, p ∈ support (run (loop 86 WeightedSchedule.decode WeightedSchedule.tier m k)
      ((lengthSlice (msgBits+86)).preload c g)) → p.1=b → F g p.2 ≤ G g p.2) :
    signedAverage m c k b F ≤ signedAverage m c k b G := by
  apply E_mono
  intro g
  apply expectedValue_mono_of_support
  intro p hp
  split_ifs with hb
  · exact h g p hp hb
  · exact le_rfl

theorem signedAverage_add (m : Message) (c : Cache) (k : ℕ) (b : SignedWinner)
    (F G : IndexTable → Cache → ℝ≥0∞) :
    signedAverage m c k b (fun g d => F g d+G g d) =
      signedAverage m c k b F+signedAverage m c k b G := by
  let trial (g : IndexTable) := run (loop 86 WeightedSchedule.decode WeightedSchedule.tier m k)
    ((lengthSlice (msgBits+86)).preload c g)
  let latent : ProbComp IndexTable := $ᵗ IndexTable
  change E latent (fun g => E (trial g) (fun p => if p.1=b then F g p.2+G g p.2 else 0)) =
    E latent (fun g => E (trial g) (fun p => if p.1=b then F g p.2 else 0)) +
    E latent (fun g => E (trial g) (fun p => if p.1=b then G g p.2 else 0))
  have hh (P : Prop) [Decidable P] (a b : ℝ≥0∞) : (if P then a+b else 0) =
      (if P then a else 0)+(if P then b else 0) := by split_ifs <;> simp
  simp_rw [hh,auth_E_add]

theorem signedAverage_const_mul (m : Message) (c : Cache) (k : ℕ) (b : SignedWinner)
    (a : ℝ≥0∞) (F : IndexTable → Cache → ℝ≥0∞) :
    signedAverage m c k b (fun g d => a*F g d) = a*signedAverage m c k b F := by
  let trial (g : IndexTable) := run (loop 86 WeightedSchedule.decode WeightedSchedule.tier m k)
    ((lengthSlice (msgBits+86)).preload c g)
  let latent : ProbComp IndexTable := $ᵗ IndexTable
  change E latent (fun g => E (trial g) (fun p => if p.1=b then a*F g p.2 else 0)) =
    a*E latent (fun g => E (trial g) (fun p => if p.1=b then F g p.2 else 0))
  have hh (P : Prop) [Decidable P] (x : ℝ≥0∞) : (if P then a*x else 0) = a*(if P then x else 0) := by
    split_ifs <;> simp
  simp_rw [hh,← E_const_mul]

theorem signedAverage_sum {ι : Type} (m : Message) (c : Cache) (k : ℕ) (b : SignedWinner)
    (T : Finset ι) (F : ι → IndexTable → Cache → ℝ≥0∞) :
    signedAverage m c k b (fun g d => ∑ ξ ∈ T, F ξ g d) =
      ∑ ξ ∈ T, signedAverage m c k b (F ξ) := by
  let trial (g : IndexTable) := run (loop 86 WeightedSchedule.decode WeightedSchedule.tier m k)
    ((lengthSlice (msgBits+86)).preload c g)
  let latent : ProbComp IndexTable := $ᵗ IndexTable
  change E latent (fun g => E (trial g) (fun p => if p.1=b then ∑ ξ∈T, F ξ g p.2 else 0)) =
    ∑ ξ∈T, E latent (fun g => E (trial g) (fun p => if p.1=b then F ξ g p.2 else 0))
  have hh (P : Prop) [Decidable P] (f : ι → ℝ≥0∞) : (if P then ∑ ξ ∈ T, f ξ else 0) =
      ∑ ξ ∈ T, if P then f ξ else 0 := by split_ifs <;> simp
  simp_rw [hh,E_finsetSum]

theorem signedAverage_weighted_sum (m : Message) (c : Cache) (k : ℕ) (b : SignedWinner)
    (T : Finset Rec) (F : Rec → IndexTable → Cache → ℝ≥0∞) :
    signedAverage m c k b (fun g d => ∑ ξ ∈ T, w*F ξ g d) =
      ∑ ξ ∈ T, w*signedAverage m c k b (F ξ) := by
  rw [signedAverage_sum]
  simp_rw [signedAverage_const_mul]

def fixedPost (A : forestScheme.toAlgorithm.Adversary) (ξ : Rec)
    (m : Message) (st : A.State) (η : Nonce 86) (i : Fin WeightedSchedule.M) :=
  stBWithForgery A (pkOf ξ) m st (some (η,revealed (setsName i) ξ))

def graphLoss (A : forestScheme.toAlgorithm.Adversary) (ξ : Rec)
    (m : Message) (st : A.State) (η : Nonce 86) (i : Fin WeightedSchedule.M) (d : Cache) : ℝ≥0∞ :=
  E (run (fixedPost A ξ m st η i) (Cache.extend d (fExp (some (setsName i)) ξ)))
    (fun p => ind (Cache.Hits p.2 (fHid (some (setsName i)) ξ))+ind (Spr p.2 ξ))

def freshLoss (A : forestScheme.toAlgorithm.Adversary) (ξ : Rec)
    (m : Message) (st : A.State) (η : Nonce 86) (i : Fin WeightedSchedule.M)
    (c : Cache) (g : IndexTable) (d : Cache) : ℝ≥0∞ :=
  E (run (A.forge st (some (η,revealed (setsName i) ξ)))
    (Cache.extend d (fExp (some (setsName i)) ξ)))
    (fun p => ind (freshAlternative 86 c (m,η) (forgedInput p.1) ∧
      WeightedSchedule.decode (g (p.1.1++p.1.2.1))=some i))

def postCost (A : forestScheme.toAlgorithm.Adversary) (ξ : Rec)
    (m : Message) (st : A.State) (η : Nonce 86) (i : Fin WeightedSchedule.M)
    (charge : Spec.Domain → ℝ≥0∞) (d : Cache) : ℝ≥0∞ :=
  expectedCharge charge (fixedPost A ξ m st η i) (Cache.extend d (fExp (some (setsName i)) ξ))

def posteriorRate (i : Fin WeightedSchedule.M) : ℝ≥0∞ :=
  ENNReal.ofReal (fraction (fun y => WeightedSchedule.decode y=some i) /
    fraction (weakRank WeightedSchedule.tier i ∘ WeightedSchedule.decode))

private def jointInd (P Q : Prop) : ℝ≥0∞ := if P ∧ Q then 1 else 0

theorem signedAverage_fresh_bound (A : forestScheme.toAlgorithm.Adversary) (ξ : Rec)
    (m : Message) (st : A.State) (c : Cache) (k : ℕ) (η : Nonce 86)
    (i : Fin WeightedSchedule.M) :
    signedAverage m c k (some (η,i)) (freshLoss A ξ m st η i c) ≤
      posteriorRate i * signedAverage m c k (some (η,i))
        (fun _ d => postCost A ξ m st η i (indexPaid (isIndexLength (msgBits+86))) d) := by
  have h := concrete_fresh_overlay A ξ m st c k η i
  unfold signedChosen signedCharge exposeCache at h
  simp only [E_map] at h
  dsimp only [WeightedScheme.Scheme.toAlgorithm] at A
  have hl : (fun g => E (run (loop 86 WeightedSchedule.decode WeightedSchedule.tier m k)
      ((lengthSlice (msgBits+86)).preload c g)) (fun p =>
        if p.1=some (η,i) then E (run (A.forge st (signatureFromWinner ξ p.1))
          (Cache.extend p.2 (fExp (some (setsName i)) ξ)))
          (fun s => jointInd (freshAlternative 86 c (m,η) (forgedInput s.1))
            (WeightedSchedule.decode (g ((forgedInput s.1).1++(forgedInput s.1).2))=some i))
        else 0)) =
      (fun g => E (run (loop 86 WeightedSchedule.decode WeightedSchedule.tier m k)
      ((lengthSlice (msgBits+86)).preload c g)) (fun p =>
        if p.1=some (η,i) then freshLoss A ξ m st η i c g p.2 else 0)) := by
    funext g
    congr 1
    funext p
    split_ifs with hp
    · rw [hp]
      simp only [freshLoss, signatureFromWinner, Option.map_some, forgedInput, ind, jointInd]
      congr 1
      funext s
      split_ifs <;> rfl
    · rfl
  have hr : (fun g => E (run (loop 86 WeightedSchedule.decode WeightedSchedule.tier m k)
      ((lengthSlice (msgBits+86)).preload c g)) (fun p =>
        if p.1=some (η,i) then expectedCharge (indexPaid (isIndexLength (msgBits+86)))
          (stBWithForgery A (pkOf ξ) m st (signatureFromWinner ξ p.1))
          (Cache.extend p.2 (fExp (some (setsName i)) ξ)) else 0)) =
      (fun g => E (run (loop 86 WeightedSchedule.decode WeightedSchedule.tier m k)
      ((lengthSlice (msgBits+86)).preload c g)) (fun p =>
        if p.1=some (η,i) then postCost A ξ m st η i (indexPaid (isIndexLength (msgBits+86))) p.2 else 0)) := by
    funext g
    congr 1
    funext p
    split_ifs with hp
    · rw [hp]
      rfl
    · rfl
  have hlE := congrArg (E ($ᵗ IndexTable)) hl
  have hrE := congrArg (E ($ᵗ IndexTable)) hr
  exact hlE.symm.le.trans (h.trans_eq (congrArg (posteriorRate i * ·) hrE))

theorem signedAverage_graph_bound (A : forestScheme.toAlgorithm.Adversary)
    (pk : BitVec 128) (T : Finset Rec) (hT : T ⊆ fiberA pk)
    (m : Message) (st : A.State) (c : Cache) (k : ℕ) (η : Nonce 86)
    (i : Fin WeightedSchedule.M) (hTc : ∀ ξ∈T, ¬ Cache.Hits c (kc ξ)) :
    signedAverage m c k (some (η,i)) (fun _ d => ∑ ξ∈T, w*graphLoss A ξ m st η i d) ≤
      signedAverage m c k (some (η,i)) (fun _ d => (∑ ξ∈T, w*ind (Spr c ξ)) +
        authRate * ∑ ξ∈fiberA pk, w*postCost A ξ m st η i (otherPaid (isIndexLength (msgBits+86))) d) := by
  apply signedAverage_mono_support
  intro g p hp _
  have hext := preloaded_loop_indexExtension WeightedSchedule.decode WeightedSchedule.tier m k c g p hp
  have h := postsign_auth_expected (isCut_setsName i) pk T hT c p.2 hext hTc
    (isIndexLength (msgBits+86)) (fun q hq => exists_encQuery_of_length q hq)
    (fun dt => stBWithForgery A dt.1 m st (some (η,dt.2.1)))
  exact h

#print axioms signedAverage_fresh_bound
#print axioms signedAverage_graph_bound
end OptimalOTS.WeightedConstruction.WideForest
