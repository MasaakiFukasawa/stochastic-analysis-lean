import Chapter12GaussianScaleIntegralDerivative
import Chapter12GaussianLebesgueEnvelope

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal NNReal
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000

/-- Polynomial-growth lognormal payoffs meet the domination hypothesis
for differentiating the scale density. -/
theorem lognormal_scale_density_derivative {d : ℕ}
    (x b : Fin d → ℝ) (A : Matrix (Fin d) (Fin d) ℝ)
    (h : (Fin d → ℝ) → ℝ) (hm : Measurable h)
    (C : ℝ) (n : ℕ) (hb : ∀ y,|h y|≤C*(1+‖y‖^n))
    (c s : ℝ) (hs : 0<s) (k : Fin d → ℝ) :
    HasDerivAt (fun u => ∫ z,h (fun i => x i*Real.exp (b i+∑ j,A i j*z j))*
      scaleGaussianKernel c k z u)
      (∫ z,h (fun i => x i*Real.exp (b i+∑ j,A i j*z j))*
        (scaleGaussianKernel c k z s*((∑ i,(z i)^2)/s^3-(d:ℝ)/s-s*(∑ i,(k i)^2)/4))) s := by
  let f : (Fin d → ℝ) → ℝ := fun z => h (fun i => x i*Real.exp (b i+∑ j,A i j*z j))
  have hfm : Measurable f := hm.comp (by fun_prop)
  have henv := gaussian_quadratic_payoff_envelope s hs f
    (lognormal_polynomial_payoff_variance_moments ⟨8*s^2,by positivity⟩ x b A h hm C n hb 2 (by norm_num))
  have hc : 0≤scaleEnvelopeConstant d c s k := by unfold scaleEnvelopeConstant; positivity
  have hi : Integrable (fun z => f z*scaleGaussianKernel c k z s) volume := by
    apply (henv.const_mul (scaleEnvelopeConstant d c s k)).mono'
      (hfm.aestronglyMeasurable.mul (show Continuous (scaleGaussianKernel c k · s) by
        unfold scaleGaussianKernel; fun_prop).aestronglyMeasurable)
    filter_upwards [] with z
    simp only [Real.norm_eq_abs,Pi.mul_apply,abs_mul]
    have hk := scale_gaussian_kernel_envelope c s s hs (by linarith) (by linarith) z k
    have hz : 0≤∑ i,(z i)^2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
    have hh := mul_le_mul_of_nonneg_left hk (abs_nonneg (f z))
    have hmore := mul_nonneg (mul_nonneg (mul_nonneg hc (abs_nonneg (f z))) hz)
      (Real.exp_nonneg (-(∑ i,(z i)^2)/(16*s^2)))
    dsimp [scaleEnvelopeConstant] at *
    nlinarith
  exact gaussian_scale_integral_derivative volume f hfm.aestronglyMeasurable c s hs k hi henv

end Asakura.Chapter12
