import Chapter12GaussianKernelScaling
import Chapter12ConvolutionWeakLimit

open MeasureTheory Filter Real
open scoped Topology CompactlySupported
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000

theorem gaussian_mixture_weak_limit {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [IsProbabilityMeasure μ]
    (r : ℕ → ℝ) (hr : ∀ n,0<r n) (hl : Tendsto r atTop (𝓝 0)) (f : C_c(E, ℝ)) :
    Tendsto (fun n => ∫ z,f z ∂volume.withDensity (fun z => ENNReal.ofReal
      (∫ x,normalizedGaussianKernel (1/(4*(r n)^2)) (z-x) ∂μ))) atTop
      (𝓝 (∫ z,f z ∂μ)) := by
  let γ := volume.withDensity (fun x : E => ENNReal.ofReal (normalizedGaussianKernel (1/4) x))
  letI : IsProbabilityMeasure γ :=
    (normalized_gaussian_kernel_properties (E := E) (1/4) (by norm_num)).2.2.2.2.2
  have he (n : ℕ) : (μ.prod γ).map (fun z : E × E => z.1+r n • z.2)=
      volume.withDensity (fun z => ENNReal.ofReal
        (∫ x,normalizedGaussianKernel (1/(4*(r n)^2)) (z-x) ∂μ)) := by
    have hmap : (μ.prod γ).map (fun z : E × E => z.1+r n • z.2)=
        (μ.prod (γ.map (fun x => r n • x))).map (fun z : E × E => z.1+z.2) := by
      have hh := Measure.map_prod_map μ γ measurable_id (show Measurable (fun x : E => r n • x) by fun_prop)
      rw [Measure.map_id] at hh
      rw [hh,Measure.map_map (by fun_prop) (by fun_prop)]
      rfl
    rw [hmap]
    change (μ.prod ((volume.withDensity (fun x : E => ENNReal.ofReal (normalizedGaussianKernel (1/4) x))).map _)).map _=_
    rw [gaussian_kernel_measure_scaling (r n) (hr n)]
    have hrn := hr n
    have hg := normalized_gaussian_kernel_properties (E := E) (1/(4*(r n)^2))
      (by positivity : 0<1/(4*(r n)^2))
    exact (real_mixture_density μ volume _ hg.1 (fun x => (hg.2.1 x).le) _ hg.2.2.1).1
  simpa only [he] using small_noise_compact_test_limit μ γ r hl f

end Asakura.Chapter12
