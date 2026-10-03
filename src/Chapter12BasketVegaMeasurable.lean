import Chapter12GaussianScalePayoffDerivative
import Chapter12GaussianScaleIntegral

open MeasureTheory ProbabilityTheory Set Filter Finset
open scoped ENNReal Topology
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2800000

/-- Proportional-volatility vega for a Borel payoff of polynomial growth,
proved by differentiating the Gaussian density rather than the payoff. -/
theorem basket_vega_measurable {d : ℕ}
    (x b k : Fin d → ℝ) (A : Matrix (Fin d) (Fin d) ℝ)
    (h : (Fin d → ℝ) → ℝ) (hm : Measurable h)
    (C : ℝ) (n : ℕ) (hb : ∀ y,|h y|≤C*(1+‖y‖^n))
    (s : ℝ) (hs : 0<s) :
    HasDerivAt (fun u => ∫ z,h (fun i => x i*Real.exp
      (b i+∑ j,A i j*(u*z j-u^2*k j/2))) ∂Measure.pi (fun _ : Fin d => gaussianReal 0 1))
      (∫ z,h (fun i => x i*Real.exp (b i+∑ j,A i j*(s*z j-s^2*k j/2)))*
        (((∑ i,(z i)^2)-(d:ℝ))/s-(∑ i,k i*z i))
        ∂Measure.pi (fun _ : Fin d => gaussianReal 0 1)) s := by
  let f : (Fin d → ℝ) → ℝ := fun z => h (fun i => x i*Real.exp (b i+∑ j,A i j*z j))
  have hfm : Measurable f := hm.comp (by fun_prop)
  let c := ((Real.sqrt (2*Real.pi))⁻¹^d)
  have hd := lognormal_scale_density_derivative x b A h hm C n hb c s hs k
  have he : (fun u => ∫ z,f (fun i => u*z i-u^2*k i/2)
      ∂Measure.pi (fun _ : Fin d => gaussianReal 0 1)) =ᶠ[𝓝 s]
      (fun u => ∫ z,f z*scaleGaussianKernel c k z u) := by
    filter_upwards [eventually_gt_nhds hs] with u hu
    exact gaussian_scale_integral u hu k f hfm
  have hd' := hd.congr_of_eventuallyEq he
  convert hd' using 1
  have hi := gaussian_scale_integral s hs k
    (fun z => f z*((∑ i,(z i)^2)/s^3-(d:ℝ)/s-s*(∑ i,(k i)^2)/4))
    (hfm.mul (by fun_prop))
  calc
    _=(∫ z,f (fun i => s*z i-s^2*k i/2)*
        ((∑ i,(s*z i-s^2*k i/2)^2)/s^3-(d:ℝ)/s-s*(∑ i,(k i)^2)/4)
        ∂Measure.pi (fun _ : Fin d => gaussianReal 0 1)) := by
      apply integral_congr_ae
      filter_upwards [] with z
      rw [gaussian_scale_score_change s hs.ne']
    _=_ := by
      rw [hi]
      apply integral_congr_ae
      filter_upwards [] with z
      dsimp [f,c]
      ring

end Asakura.Chapter12
