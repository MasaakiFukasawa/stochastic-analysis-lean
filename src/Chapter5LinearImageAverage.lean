import Chapter5UnboundedJointHeatRegularity

open MeasureTheory Set Filter
open scoped Topology ENNReal NNReal
namespace Asakura.Chapter5
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false

theorem linear_image_second_moment
    {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace E] [BorelSpace E] [MeasurableSpace V] [BorelSpace V]
    (ν : Measure E) (Q : E →L[ℝ] V) (hi : MemLp (fun z : E => z) 2 ν) :
    MemLp (fun z : V => z) 2 (ν.map Q) := by
  exact (memLp_map_measure_iff continuous_id.aestronglyMeasurable Q.continuous.measurable.aemeasurable).mpr
    (hi.continuousLinearMap_comp Q)

theorem linear_image_average_integral
    {E V U : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [NormedAddCommGroup U] [NormedSpace ℝ U] [CompleteSpace U]
    [MeasurableSpace E] [BorelSpace E] [MeasurableSpace V] [BorelSpace V]
    (ν : Measure E) (Q : E →L[ℝ] V) (f : V → U) (hf : Continuous f) (x : V) (t : ℝ) :
    (∫ y,f (x+Real.sqrt t • y) ∂ν.map Q) = ∫ z,f (x+Real.sqrt t • Q z) ∂ν :=
  integral_map Q.continuous.measurable.aemeasurable (hf.comp (by fun_prop)).aestronglyMeasurable

/-- Only the last observation receives Gaussian noise. Using its image
measure proves joint regularity even when the past coordinates are frozen. -/
theorem subspace_heat_average_C2
    {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace E] [BorelSpace E] [MeasurableSpace V] [BorelSpace V]
    (ν : Measure E) [IsProbabilityMeasure ν] (Q : E →L[ℝ] V)
    (hi : MemLp (fun z : E => z) 2 ν)
    (f : V → ℝ) (D : V → V →L[ℝ] ℝ) (DD : V → V →L[ℝ] V →L[ℝ] ℝ)
    (hd : ∀ x,HasFDerivAt f (D x) x) (hdd : ∀ x,HasFDerivAt D (DD x) x)
    (hDc : Continuous D) (hDDc : Continuous DD)
    (C K : ℝ≥0) (hD : ∀ x,‖D x‖ ≤ C) (hDD : ∀ x,‖DD x‖ ≤ K)
    (p : V × ℝ) (hp : 0 < p.2) :
    ContDiffAt ℝ 2 (fun q : V × ℝ => ∫ z,f (q.1+Real.sqrt q.2 • Q z) ∂ν) p := by
  have hfc : Continuous f := continuous_iff_continuousAt.mpr fun x => (hd x).continuousAt
  have he := joint_heat_average_C2_lipschitz (ν.map Q) (linear_image_second_moment ν Q hi)
    f D DD hd hdd hDc hDDc C K hD hDD p hp
  simpa only [linear_image_average_integral ν Q f hfc] using he

end Asakura.Chapter5
