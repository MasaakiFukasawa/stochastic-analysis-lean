import Chapter12GaussianMixtureWeakLimit

open MeasureTheory Set
namespace Asakura.EndToEnd
open Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false

/-- The actual law after adding independent scaled Gaussian noise equals
 the mixture density used in the Fourier calculation. -/
theorem gaussian_smoothed_law {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [IsProbabilityMeasure μ] (r : ℝ) (hr : 0 < r) :
    let γ := volume.withDensity (fun x : E => ENNReal.ofReal (normalizedGaussianKernel (1/4) x))
    (μ.prod γ).map (fun z : E × E => z.1+r • z.2)=
      volume.withDensity (fun z => ENNReal.ofReal
        (∫ x,normalizedGaussianKernel (1/(4*r^2)) (z-x) ∂μ)) := by
  let γ := volume.withDensity (fun x : E => ENNReal.ofReal (normalizedGaussianKernel (1/4) x))
  letI : IsProbabilityMeasure γ :=
    (normalized_gaussian_kernel_properties (E:=E) (1/4) (by norm_num)).2.2.2.2.2
  have hmap : (μ.prod γ).map (fun z : E × E => z.1+r • z.2)=
      (μ.prod (γ.map (fun x => r • x))).map (fun z : E × E => z.1+z.2) := by
    have hh := Measure.map_prod_map μ γ measurable_id (show Measurable (fun x : E => r • x) by fun_prop)
    rw [Measure.map_id] at hh
    rw [hh,Measure.map_map (by fun_prop) (by fun_prop)]
    rfl
  change (μ.prod γ).map _=_
  rw [hmap]
  change (μ.prod ((volume.withDensity (fun x : E => ENNReal.ofReal (normalizedGaussianKernel (1/4) x))).map _)).map _=_
  rw [gaussian_kernel_measure_scaling r hr]
  have hg := normalized_gaussian_kernel_properties (E:=E) (1/(4*r^2)) (by positivity : 0 < 1/(4*r^2))
  exact (real_mixture_density μ volume _ hg.1 (fun x => (hg.2.1 x).le) _ hg.2.2.1).1

#print axioms gaussian_smoothed_law
end Asakura.EndToEnd
