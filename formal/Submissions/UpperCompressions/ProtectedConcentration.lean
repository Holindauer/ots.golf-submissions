import Submissions.UpperCompressions.ProtectedCacheStatistics
import Submissions.UpperCompressions.ActualScoreConcentration

/-! Concentration for statistics read directly from the actual protected cache.
The row finite-domain restriction is discharged pathwise for every cache. -/
noncomputable section
open OracleSpec OracleComp
open scoped Classical BigOperators ENNReal
namespace WeightedProtectedCache
open WeightedRealExecution WeightedRow.Weights WeightedCacheCounts WeightedDirectCache
open WeightedOracleExecution WeightedFirstHit WeightedActualScore
set_option maxHeartbeats 800000
variable {ι α : Type} [Fintype ι] [DecidableEq ι]

/-- Every prefix of actual shared-oracle execution obeys the global boundary,
except with probability exp(-2^40); no fixed paid budget or time union is used. -/
theorem global_score (w : WeightedRow.Weights ι)
    (A : Finset OptimalOTS.Query) (decode : BitVec OptimalOTS.hashBits → Option ι)
    (hfiber : ∀ x, ((Finset.univ.filter (fun b => decode b=x)).card:ℝ) /
      Fintype.card (BitVec OptimalOTS.hashBits) = w.classMass x)
    (κ : ℝ) (hκ : 0 < κ) (hm : w.mean ≤ κ) (hg : ∀ i, w.g i ≤ (2^20:ℝ)*κ/2)
    (oa : OracleComp OptimalOTS.Spec α) (cache : OptimalOTS.hashSpec.QueryCache)
    (hq0 : (seen A cache).card = 0) (hk0 : classCounts A cache decode = fun _ => 0) :
    let hit := fun (_ : ℕ) (c : OptimalOTS.hashSpec.QueryCache) =>
      (κ/100)*max ((seen A c).card:ℝ) ((2^86:ℝ)/10) ≤ w.M1 (seen A c).card (classCounts A c decode)
    let kill := fun (_ : ℕ) (_ : OptimalOTS.hashSpec.QueryCache) => False
    Pr[fun out => out.2.status = .hit |
      (simulateQ (stoppedImpl OptimalOTS.oracleImpl hit kill) oa).run (classify hit kill 0 cache)] ≤
      ENNReal.ofReal (Real.exp (-(2^40:ℝ))) := by
  exact WeightedActualScore.mixed_global w OptimalOTS.oracleImpl
    (fun c => (seen A c).card) (fun c => classCounts A c decode)
    (protectedFresh A) (query_law w A decode hfiber) κ hκ hm hg oa cache hq0 hk0

/-- Row concentration for either score tail, with the finite nonce-domain cap
proved automatically from A.card≤2^86. The execution is never killed by a count cap. -/
theorem row_score (w : WeightedRow.Weights ι)
    (A : Finset OptimalOTS.Query) (hcard : A.card ≤ 2^86)
    (decode : BitVec OptimalOTS.hashBits → Option ι)
    (hfiber : ∀ x, ((Finset.univ.filter (fun b => decode b=x)).card:ℝ) /
      Fintype.card (BitVec OptimalOTS.hashBits) = w.classMass x)
    (lower : Bool) (G : ℝ) (hG : 0 < G) (hg : ∀ i, w.g i ≤ G)
    (oa : OracleComp OptimalOTS.Spec α) (cache : OptimalOTS.hashSpec.QueryCache)
    (hq0 : (seen A cache).card = 0) (hk0 : classCounts A cache decode = fun _ => 0) :
    let hit := fun (_ : ℕ) (c : OptimalOTS.hashSpec.QueryCache) =>
      G*(2^86:ℝ)/(100*(2^20:ℝ)) ≤
        signedM1 w (fun c => (seen A c).card) (fun c => classCounts A c decode) lower c
    let kill := fun (_ : ℕ) (_ : OptimalOTS.hashSpec.QueryCache) => False
    Pr[fun out => out.2.status = .hit |
      (simulateQ (stoppedImpl OptimalOTS.oracleImpl hit kill) oa).run (classify hit kill 0 cache)] ≤
      ENNReal.ofReal (Real.exp (-(2^30:ℝ))) := by
  have hx := WeightedActualScore.mixed_row w OptimalOTS.oracleImpl
    (fun c => (seen A c).card) (fun c => classCounts A c decode)
    (protectedFresh A) (query_law w A decode hfiber) lower G hG hg oa cache hq0 hk0
  have hcap (c : OptimalOTS.hashSpec.QueryCache) : ((seen A c).card:ℝ) ≤ 2^86 := by
    exact_mod_cast (seen_card_le A c).trans hcard
  have hhit : (fun (_ : ℕ) (c : OptimalOTS.hashSpec.QueryCache) =>
      ((seen A c).card:ℝ) ≤ 2^86 ∧ G*(2^86:ℝ)/(100*(2^20:ℝ)) ≤
        signedM1 w (fun c => (seen A c).card) (fun c => classCounts A c decode) lower c) =
      (fun (_ : ℕ) (c : OptimalOTS.hashSpec.QueryCache) =>
        G*(2^86:ℝ)/(100*(2^20:ℝ)) ≤
          signedM1 w (fun c => (seen A c).card) (fun c => classCounts A c decode) lower c) := by
    funext n c
    apply propext
    constructor
    · exact And.right
    · intro h; exact ⟨hcap c,h⟩
  have hkill : (fun (_ : ℕ) (c : OptimalOTS.hashSpec.QueryCache) =>
      (2^86:ℝ) < ((seen A c).card:ℝ)) =
      (fun (_ : ℕ) (_ : OptimalOTS.hashSpec.QueryCache) => False) := by
    funext n c
    exact propext (iff_false_intro (not_lt_of_ge (hcap c)))
  dsimp only at hx
  rw [hhit, hkill] at hx
  exact hx

#print axioms global_score
#print axioms row_score
end WeightedProtectedCache
