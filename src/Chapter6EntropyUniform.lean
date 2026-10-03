import Chapter6DensityUniformIntegrability

open MeasureTheory Set Filter
open scoped Topology ENNReal NNReal
namespace Asakura.Chapter6
set_option maxHeartbeats 1800000

/-- The manuscript's common entropy bound proves uniform integrability
of all the localized densities. -/
theorem entropy_bound_uniform_integrable
    {Ω ι : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (D : ι → Ω → ℝ) (hm : ∀ i,Measurable (D i)) (hi : ∀ i,Integrable (D i) P)
    (hp : ∀ i,∀ᵐ w ∂P,0 ≤ D i w)
    (hei : ∀ i,Integrable (fun w => D i w*Real.log (D i w)) P)
    (C : ℝ) (hC : ∀ i,(∫ w,D i w*Real.log (D i w) ∂P) ≤ C) :
    UniformIntegrable D 1 P := by
  apply uniform_integrable_of_nonnegative_tails P D hm hi hp
  intro ε hε
  have hlim : Tendsto (fun R : ℝ => (C+Real.exp (-1))/Real.log R) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop Real.tendsto_log_atTop
  obtain ⟨R,hR,he⟩ := ((eventually_gt_atTop (1:ℝ)).and (hlim.eventually (gt_mem_nhds hε))).exists
  exact ⟨R,by linarith,fun i => (entropy_density_tail_bound P (D i) (hm i) (hi i) (hp i) (hei i) C (hC i) R hR).trans he.le⟩

end Asakura.Chapter6
