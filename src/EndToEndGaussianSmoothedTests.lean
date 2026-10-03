import EndToEndGaussianSmoothingL1
import EndToEndGaussianSmoothedLaw
import EndToEndDensityTests

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BoundedContinuousFunction
namespace Asakura.EndToEnd
open Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000

/-- Fixed positive noise size: the Fourier and L1 density limits imply
 convergence of expectations on the independent product extension. -/
theorem gaussian_smoothed_tests {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (μ : ℕ → Measure E) (ν : Measure E)
    [∀ n,IsProbabilityMeasure (μ n)] [IsProbabilityMeasure ν]
    (hlim : ∀ ξ,Tendsto (fun n => charFun (μ n) ξ) atTop (𝓝 (charFun ν ξ)))
    (r : ℝ) (hr : 0 < r) (φ : E →ᵇ ℝ) :
    let γ := volume.withDensity (fun x : E => ENNReal.ofReal (normalizedGaussianKernel (1/4) x))
    Tendsto (fun n => ∫ z : E × E,φ (z.1+r • z.2) ∂(μ n).prod γ) atTop
      (𝓝 (∫ z : E × E,φ (z.1+r • z.2) ∂ν.prod γ)) := by
  let γ := volume.withDensity (fun x : E => ENNReal.ofReal (normalizedGaussianKernel (1/4) x))
  let p := fun (ρ : Measure E) x => ∫ y,normalizedGaussianKernel (1/(4*r^2)) (x-y) ∂ρ
  have hp (ρ : Measure E) [IsProbabilityMeasure ρ] := gaussian_mixture_probability_density ρ (r^2) (sq_pos_of_pos hr)
  have he (ρ : Measure E) [IsProbabilityMeasure ρ] :
      (∫ z : E × E,φ (z.1+r • z.2) ∂ρ.prod γ)=∫ x,p ρ x*φ x := by
    rw [← integral_map (show AEMeasurable (fun z : E × E => z.1+r • z.2) (ρ.prod γ) by fun_prop)
      φ.continuous.aestronglyMeasurable]
    rw [gaussian_smoothed_law ρ r hr]
    rw [integral_withDensity_eq_integral_toReal_smul (hp ρ).1.measurable.ennreal_ofReal
      (.of_forall (fun _ => ENNReal.ofReal_lt_top))]
    simp only [ENNReal.toReal_ofReal ((hp ρ).2.1 _),smul_eq_mul,p]
  change Tendsto (fun n => ∫ z : E × E,φ (z.1+r • z.2) ∂(μ n).prod γ) atTop
    (𝓝 (∫ z : E × E,φ (z.1+r • z.2) ∂ν.prod γ))
  simp_rw [he]
  exact density_L1_tests volume _ _ (fun n => (hp (μ n)).2.2.1) (hp ν).2.2.1
    (gaussian_smoothing_L1 μ ν hlim (r^2) (sq_pos_of_pos hr)) φ

#print axioms gaussian_smoothed_tests
end Asakura.EndToEnd
