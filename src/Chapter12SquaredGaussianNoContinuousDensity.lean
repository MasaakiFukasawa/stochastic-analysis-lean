import Chapter12SquaredGaussianLaw
import Chapter12SquaredGaussianSingularity
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Function.AEEqOfLIntegral

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

theorem squared_gaussian_density_continuous_positive (T : ℝ≥0) (hT : 0<T) :
    ContinuousOn (squaredGaussianDensity T) (Ioi (0:ℝ)) := by
  have hh : ContinuousOn (fun x : ℝ => (Real.sqrt (2*Real.pi*(T:ℝ)*x))⁻¹*
      Real.exp (-x/(2*(T:ℝ)))) (Ioi (0:ℝ)) := by
    intro x hx
    apply ContinuousAt.continuousWithinAt
    apply ContinuousAt.mul
    · apply ContinuousAt.inv₀ (by fun_prop)
      exact (Real.sqrt_pos.mpr (by have hx' : 0<x := hx; positivity)).ne'
    · fun_prop
  apply hh.congr
  intro x hx
  exact if_pos (show 0<x from hx)

/-- No choice of values on a null set repairs the singularity at zero. -/
theorem squared_gaussian_no_continuous_density (T : ℝ≥0) (hT : 0<T)
    (p : ℝ → ℝ) (hp : Continuous p) (hp0 : ∀ x,0≤p x) :
    (gaussianReal 0 T).map (fun x : ℝ => x^2)≠
      volume.withDensity (fun x => ENNReal.ofReal (p x)) := by
  intro hmap
  rw [squared_gaussian_law T hT.ne'] at hmap
  have hae := (withDensity_eq_iff_of_sigmaFinite
    (squared_gaussian_density_measurable T).ennreal_ofReal.aemeasurable
    hp.measurable.ennreal_ofReal.aemeasurable).mp hmap
  have hreal : squaredGaussianDensity T =ᵐ[volume] p := by
    filter_upwards [hae] with x hx
    have hh := congrArg ENNReal.toReal hx
    simpa only [ENNReal.toReal_ofReal (squared_gaussian_density_nonneg T x),
      ENNReal.toReal_ofReal (hp0 x)] using hh
  have he := Measure.eqOn_of_ae_eq (ae_restrict_of_ae hreal)
    (squared_gaussian_density_continuous_positive T hT) hp.continuousOn
    (show Ioi (0:ℝ)⊆closure (interior (Ioi (0:ℝ))) by rw [isOpen_Ioi.interior_eq]; exact subset_closure)
  have ht : Tendsto p (𝓝[>] (0:ℝ)) atTop := by
    apply (squared_gaussian_density_unbounded_at_zero T hT).congr'
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact he hx
  exact not_tendsto_nhds_of_tendsto_atTop ht (p 0)
    (hp.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)

end Asakura.Chapter12
