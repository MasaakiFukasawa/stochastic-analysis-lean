import Chapter9ScoreLipschitz
import Mathlib.MeasureTheory.Integral.Bochner.Set

open MeasureTheory Set
namespace Asakura.Chapter9
set_option maxHeartbeats 600000

/-- For a compactly supported finite measure, joint continuity can be
integrated. The support condition is used as an a.e. condition. -/
theorem compact_prior_integral_continuous {X E V : Type*}
    [TopologicalSpace X] [FirstCountableTopology X] [LocallyCompactSpace X]
    [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] [NormedAddCommGroup V] [NormedSpace ℝ V]
    (μ : Measure E) [IsFiniteMeasure μ] (K : Set E) (hK : IsCompact K)
    (hμ : ∀ᵐ x ∂μ,x∈K) (f : X → E → V) (hf : Continuous f.uncurry) :
    Continuous (fun z => ∫ x,f z x ∂μ) := by
  have hh := continuous_parametric_integral_of_continuous hf hK (μ := μ)
  rwa [Measure.restrict_eq_self_of_ae_mem hμ] at hh

/-- The actual score is jointly continuous when the initial law has bounded
support and the kernel parameters are continuous with positive variance. -/
theorem compact_radial_score_continuous {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] [ProperSpace E]
    (μ : Measure E) [IsProbabilityMeasure μ] (R : ℝ) (hb : ∀ᵐ x ∂μ,‖x‖≤R)
    (c a v : ℝ → ℝ) (hc : Continuous c) (ha : Continuous a) (hv : Continuous v)
    (hcp : ∀ t,0<c t) (hvp : ∀ t,0<v t) :
    Continuous (fun z : ℝ × E =>
      (∫ x,radialKernel (c z.1) (a z.1) (v z.1) x z.2 ∂μ)⁻¹ •
      (∫ x,(-radialKernel (c z.1) (a z.1) (v z.1) x z.2/v z.1) •
        (z.2-a z.1 • x) ∂μ)) := by
  have hb' : ∀ᵐ x ∂μ,x∈Metric.closedBall (0:E) R := by simpa only [Metric.mem_closedBall,dist_zero_right] using hb
  have hk : Continuous (fun w : (ℝ × E) × E =>
      radialKernel (c w.1.1) (a w.1.1) (v w.1.1) w.2 w.1.2) := by
    dsimp [radialKernel]
    fun_prop (disch := intro w; exact mul_ne_zero (by norm_num) (hvp _).ne')
  have hp := compact_prior_integral_continuous μ (Metric.closedBall 0 R)
    (isCompact_closedBall _ _) hb'
    (fun (z : ℝ × E) x => radialKernel (c z.1) (a z.1) (v z.1) x z.2) hk
  have hg := compact_prior_integral_continuous μ (Metric.closedBall 0 R)
    (isCompact_closedBall _ _) hb'
    (fun (z : ℝ × E) x => (-radialKernel (c z.1) (a z.1) (v z.1) x z.2/v z.1) • (z.2-a z.1 • x))
    (show Continuous (fun w : (ℝ × E) × E =>
      (-radialKernel (c w.1.1) (a w.1.1) (v w.1.1) w.2 w.1.2/v w.1.1) •
        (w.1.2-a w.1.1 • w.2)) by fun_prop (disch := intro w; exact (hvp _).ne'))
  exact (hp.inv₀ (fun z => (radial_mixture_positive μ _ _ _ (hcp _) (hvp _) z.2).ne')).smul hg
end Asakura.Chapter9
