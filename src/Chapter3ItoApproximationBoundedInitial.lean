import Chapter3ItoErrorQuadraticBound
import Chapter3LocalDyadicCovarianceConvergence

open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter3Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false

/-- Full local convergence with no integrability bound on X or its quadratic
variation. Only boundedness of H(0) remains for the initial-event reduction. -/
theorem ito_approximation_bounded_initial
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (hT : 0 < T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (hnull : ∀ t N, MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)
    (X A H Y : ClosedTime T → Ω → ℝ)
    (hX : LocalMProcessWitness P F X) (hA : LocalCovarianceWitness P F X X A)
    (hY : LocalMProcessWitness P F Y)
    (hYI : ItoCovarianceFormula P F X (fun z => H (realTimeClamp z.2) z.1) Y)
    (hHm : ∀ t, t < ⊤ → Measurable[F t] (H t))
    (hHc : ∀ ω t, t < ⊤ → ContinuousAt (fun s => H s ω) t)
    (K : ℝ) (hK : ∀ᵐ ω ∂P, |H ⊥ ω| ≤ K)
    (c : ℕ → ℝ) (hc : ∀ j, 0 < c j) (hcm : StrictMono c) (hcT : ∀ j, (c j:EReal) < T)
    (hct : StrictMono (fun j => realTimeClamp (T := T) (c j)))
    (hcut : ∀ j, realTimeClamp (T := T) (c j) < ⊤)
    (hcc : ∀ t, t < ⊤ → ∃ j, t < realTimeClamp (T := T) (c j))
    (hAm : ∀ j ω, MonotoneOn (fun r => A (realTimeClamp r) ω) (Icc 0 (c j)))
    (hAc : ∀ j ω, ContinuousOn (fun r => A (realTimeClamp r) ω) (Icc 0 (c j)))
    (hA0 : ∀ ω, A ⊥ ω = 0)
    (τ : ℕ → ℕ → Ω → ClosedTime T)
    (hτ : ∀ n j t, MeasurableSet[F t] {ω | τ n j ω ≤ t})
    (hτm : ∀ n ω, Monotone (fun j => τ n j ω))
    (hτt : ∀ n j ω, τ n j ω < ⊤) (hτ0 : ∀ n ω, τ n 0 ω = ⊥)
    (hτc : ∀ n ω t, t < ⊤ → ∃ j, t < τ n j ω)
    (hosc : ∀ᵐ ω ∂P, ∀ n j t, τ n j ω ≤ t → t ≤ τ n (j+1) ω →
      |H (τ n j ω) ω-H t ω| ≤ (1/2:ℝ)^n)
    (b : ClosedTime T) (hb : b < ⊤) :
    let E := fun n t ω => Y t ω-
      ∑' j, H (τ n j ω) ω*(X (min (τ n (j+1) ω) t) ω-X (min (τ n j ω) t) ω)
    ∃ hE : ∀ n ω, Continuous (fun t => E n (min b t) ω),
      ∀ᵐ ω ∂P, Tendsto (fun n => continuousPath (fun t ω => E n (min b t) ω) (hE n) ω) atTop (𝓝 0) := by
  intro E
  obtain ⟨hE,B,hB,hbound⟩ := ito_discrete_error_quadratic_bound P hT F hF hle hnull
    X A H Y hX hA hY hYI hHm hHc K hK c hc hcm hcT hct hcut hcc hAm hAc hA0
    τ hτ hτm hτt hτ0 hτc hosc
  exact local_dyadic_covariance_ae_uniform P F hF hle hnull X A hX hA E B hE hB hbound b hb

end Asakura.Chapter3Complete
#print axioms Asakura.Chapter3Complete.ito_approximation_bounded_initial
