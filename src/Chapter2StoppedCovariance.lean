import Chapter2LocalStopping
import FullAuditCovarianceBasics

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter2Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written
set_option maxHeartbeats 600000

variable {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
  {T : EReal} [Fact (0 ≤ T)] (F : ClosedTime T → MeasurableSpace Ω)
  (hF : Monotone F) (hle : ∀ t, F t ≤ m)

include hF hle

noncomputable def stopBounded (X : boundedMProcess P F)
    (τ : Ω → ClosedTime T) (hτ : ∀ t, MeasurableSet[F t] {ω | τ ω ≤ t}) :
    boundedMProcess P F :=
  ⟨fun t ω => X.val (min (τ ω) t) ω, bounded_martingale_stopped P F hF hle X τ hτ⟩

/-- Consistency of the ACTUAL constructed covariance under a common stop.
This supplies the essential gluing input of the local covariance construction.
It uses the written uniqueness theorem and stopped product martingale. -/
theorem covariance_of_stopped_bounded
    (hnull : ∀ t N, MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)
    (X Y : boundedMProcess P F)
    (τ : Ω → ClosedTime T) (hτ : ∀ t, MeasurableSet[F t] {ω | τ ω ≤ t}) :
    ∀ᵐ ω ∂P, ∀ t,
      boundedCov P F hF hle hnull (stopBounded P F hF hle X τ hτ)
        (stopBounded P F hF hle Y τ hτ) t ω =
      boundedCov P F hF hle hnull X Y (min (τ ω) t) ω := by
  let C := boundedCov P F hF hle hnull X Y
  have hM := continuous_m2_stopped P F hF hle
    (fun t ω => X.val t ω*Y.val t ω-C t ω)
    (bounded_cov_product_witness P F hF hle hnull X Y) τ hτ
  have hA (ω) : ∃ A B : ClosedTime T → ℝ, Monotone A ∧ Monotone B ∧
      ∀ t, C (min (τ ω) t) ω = A t-B t := by
    obtain ⟨A,B,hA,hB,he⟩ := bounded_cov_in_A P F hF hle hnull X Y ω
    refine ⟨fun t => A (min (τ ω) t),fun t => B (min (τ ω) t),?_,?_,?_⟩
    · exact hA.comp (monotone_const.min monotone_id)
    · exact hB.comp (monotone_const.min monotone_id)
    · intro t; exact he _
  have h := bounded_cov_unique P F hF hle hnull
    (stopBounded P F hF hle X τ hτ) (stopBounded P F hF hle Y τ hτ)
    (fun t ω => C (min (τ ω) t) ω) hA hM
  exact h.mono fun ω hω t => (hω t).symm

/-- For increasing localizers the bounded covariations are compatible.
Both bounded processes here are the actual stopped original processes. -/
theorem covariances_along_localizers_compatible
    (hnull : ∀ t N, MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)
    (X Y : ClosedTime T → Ω → ℝ)
    (τ : ℕ → Ω → ClosedTime T)
    (hτ : ∀ n t, MeasurableSet[F t] {ω | τ n ω ≤ t})
    (hmono : ∀ ω, Monotone (fun n => τ n ω))
    (hX : ∀ n, (fun t ω => X (min (τ n ω) t) ω) ∈ boundedMProcess P F)
    (hY : ∀ n, (fun t ω => Y (min (τ n ω) t) ω) ∈ boundedMProcess P F) :
    ∀ᵐ ω ∂P, ∀ n k, n ≤ k → ∀ t,
      boundedCov P F hF hle hnull ⟨_, hX k⟩ ⟨_, hY k⟩ (min (τ n ω) t) ω =
        boundedCov P F hF hle hnull ⟨_, hX n⟩ ⟨_, hY n⟩ t ω := by
  have hn (n k : ℕ) : ∀ᵐ ω ∂P, n ≤ k → ∀ t,
      boundedCov P F hF hle hnull ⟨_, hX k⟩ ⟨_, hY k⟩ (min (τ n ω) t) ω =
        boundedCov P F hF hle hnull ⟨_, hX n⟩ ⟨_, hY n⟩ t ω := by
    by_cases hnk : n ≤ k
    · have hx : stopBounded P F hF hle ⟨_, hX k⟩ (τ n) (hτ n) = ⟨_, hX n⟩ := by
        apply Subtype.ext
        funext t ω
        change X (min (τ k ω) (min (τ n ω) t)) ω = X (min (τ n ω) t) ω
        rw [← min_assoc, min_eq_right (hmono ω hnk)]
      have hy : stopBounded P F hF hle ⟨_, hY k⟩ (τ n) (hτ n) = ⟨_, hY n⟩ := by
        apply Subtype.ext
        funext t ω
        change Y (min (τ k ω) (min (τ n ω) t)) ω = Y (min (τ n ω) t) ω
        rw [← min_assoc, min_eq_right (hmono ω hnk)]
      have hc := covariance_of_stopped_bounded P F hF hle hnull
        ⟨_, hX k⟩ ⟨_, hY k⟩ (τ n) (hτ n)
      rw [hx, hy] at hc
      exact hc.mono fun ω hω _ t => (hω t).symm
    · exact Filter.Eventually.of_forall fun _ h => (hnk h).elim
  exact ae_all_iff.2 fun n => ae_all_iff.2 (hn n)

/-- Nested stopping is exactly minimum of the stopping times, pathwise. -/
theorem nested_stopping_identity {ι : Type*} [LinearOrder ι]
    (X : ι → Ω → ℝ) (τ σ : Ω → ι) :
    (fun t ω => X (min (τ ω) (min (σ ω) t)) ω) =
      (fun t ω => X (min (min (τ ω) (σ ω)) t) ω) := by
  funext t ω
  rw [min_assoc]

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.covariance_of_stopped_bounded
#print axioms Asakura.Chapter2Complete.nested_stopping_identity

#print axioms Asakura.Chapter2Complete.covariances_along_localizers_compatible
