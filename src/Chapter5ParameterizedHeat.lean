import FullAuditHeatKernel

open MeasureTheory Filter
open scoped Topology
namespace Asakura.Chapter5

/-- Parameter-dependent Gaussian (or any probability) averaging is jointly
continuous down to t=0 for bounded continuous integrands. Applied to each
bounded first partial derivative, this is exactly the continuity assertion
in the heat-kernel exercise, including the previously observed coordinates. -/
theorem parameter_average_continuous
    {A E : Type*} [TopologicalSpace A] [FirstCountableTopology A]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (ν : Measure E) [IsProbabilityMeasure ν]
    (g : A × E → ℝ) (hg : Continuous g) (C : ℝ) (hb : ∀ p, ‖g p‖ ≤ C) :
    Continuous (fun p : (A × E) × ℝ =>
      ∫ z, g (p.1.1,p.1.2+Real.sqrt p.2 • z) ∂ν) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  apply tendsto_integral_filter_of_dominated_convergence (fun _ => C)
  · exact Eventually.of_forall fun q => (hg.comp (by fun_prop)).aestronglyMeasurable
  · exact Eventually.of_forall fun q => ae_of_all _ fun z => hb _
  · exact integrable_const C
  · exact ae_of_all _ fun z => (hg.comp (by fun_prop)).continuousAt

theorem parameter_average_at_zero
    {A E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
    (ν : Measure E) [IsProbabilityMeasure ν] (g : A × E → ℝ) (a : A) (x : E) :
    (∫ z, g (a,x+Real.sqrt 0 • z) ∂ν) = g (a,x) := by simp

end Asakura.Chapter5
