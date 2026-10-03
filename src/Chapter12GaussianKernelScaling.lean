import Chapter12GaussianNormalization
import Chapter12ScaledDensity

open MeasureTheory Real
open scoped ENNReal
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000

theorem gaussian_kernel_scaling {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (r : ℝ) (hr : 0<r) (x : E) :
    |(r^Module.finrank ℝ E)⁻¹| *normalizedGaussianKernel (1/4) (r⁻¹ • x)=
      normalizedGaussianKernel (1/(4*r^2)) x := by
  unfold normalizedGaussianKernel
  rw [gaussian_scale_normalization _ r hr,norm_smul,Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr hr),abs_of_pos (inv_pos.mpr (pow_pos hr _))]
  have hexp : -(1/4:ℝ)*(r⁻¹*‖x‖)^2=-(1/(4*r^2))*‖x‖^2 := by ring
  rw [hexp]
  have hc : π/(1/4:ℝ)=4*π := by ring
  rw [hc]
  ring

theorem gaussian_kernel_measure_scaling {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (r : ℝ) (hr : 0<r) :
    (volume.withDensity (fun x : E => ENNReal.ofReal (normalizedGaussianKernel (1/4) x))).map
        (fun x => r • x)=
      volume.withDensity (fun x : E => ENNReal.ofReal (normalizedGaussianKernel (1/(4*r^2)) x)) := by
  rw [scaled_density volume _
    (normalized_gaussian_kernel_properties (E := E) (1/4) (by norm_num)).1.measurable.ennreal_ofReal r hr.ne']
  congr 1
  funext x
  rw [← ENNReal.ofReal_mul (abs_nonneg _),gaussian_kernel_scaling r hr x]

end Asakura.Chapter12
