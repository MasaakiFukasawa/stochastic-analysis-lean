import Chapter8StationaryTimeAverage
import FullAuditTimeAverageCoupling

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal
namespace Asakura.Chapter8
open Asakura.FullAudit
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

/-- Stationary Markov contraction gives the full, continuous-time almost
sure limit for bounded Lipschitz observables, not only a subsequence limit. -/
theorem stationary_markov_time_average_ae {Ω E : Type*} [m : MeasurableSpace Ω]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (π : Measure E) [IsProbabilityMeasure π] (hπ : MemLp (fun x : E => x) 2 π)
    (Y : ℝ → Ω → E) (hmY : Measurable (fun p : Ω × ℝ => Y p.2 p.1))
    (hcY : ∀ ω, Continuous (fun t => Y t ω)) (hlaw : ∀ t, P.map (Y t) = π)
    (G : ℝ → MeasurableSpace Ω) (hG : ∀ t, G t ≤ m)
    (hYG : ∀ t, AEStronglyMeasurable[G t] (Y t) P)
    (X : ℝ → E → Ω → E) (hX : ∀ t ≥ 0, ∀ x, MemLp (X t x) 2 P)
    (κ : ℝ) (hκ : 0 < κ)
    (hLip : ∀ t ≥ 0, ∀ x y, ∀ᵐ ω ∂P,
      ‖X t x ω-X t y ω‖ ≤ Real.exp (-κ*t)*‖x-y‖)
    (f : E → ℝ) (L : ℝ≥0) (hf : LipschitzWith L f)
    (hCE : ∀ s ≥ 0, ∀ t, s ≤ t →
      P[(fun ω => f (Y t ω))|G s] =ᵐ[P] fun ω => ∫ η,f (X (t-s) (Y s ω) η) ∂P)
    (K : ℝ) (hK : 0 ≤ K) (hb : ∀ x, |f x| ≤ K) :
    ∀ᵐ ω ∂P, Tendsto (timeAverage (fun t => f (Y t ω))) atTop (nhds (∫ x,f x ∂π)) := by
  apply bounded_time_average_ae_from_variance P (fun ω t => f (Y t ω))
    (hf.continuous.measurable.comp hmY) (fun ω => hf.continuous.comp (hcY ω))
    K (2*(L:ℝ)^2*(∫ x,‖x‖^2 ∂π)/κ) (∫ x,f x ∂π) hK
    (fun ω t => hb (Y t ω))
  intro T hT
  have h := stationary_markov_time_average P π hπ Y hmY hcY hlaw G hG hYG
    X hX κ T hκ hT hLip f L hf hCE
  simpa only [div_mul_eq_div_div] using h

end Asakura.Chapter8
