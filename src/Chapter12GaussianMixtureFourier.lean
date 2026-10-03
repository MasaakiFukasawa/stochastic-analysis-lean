import Chapter12NormalizedInverseGaussian

open MeasureTheory Real
open scoped RealInnerProductSpace
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000

theorem gaussian_mixture_fourier {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [IsProbabilityMeasure μ] (b : ℝ) (hb : 0<b) (x : E) :
    ((∫ y,normalizedGaussianKernel (1/(4*b)) (x-y) ∂μ : ℝ):ℂ)=
      ((2*π)^Module.finrank ℝ E:ℂ)⁻¹*
        ∫ ξ,Complex.exp (-Complex.I*(inner ℝ ξ x:ℂ))*
          (∫ y,Complex.exp (Complex.I*(inner ℝ ξ y:ℂ)) ∂μ)*
          (Real.exp (-b*‖ξ‖^2):ℂ) := by
  have hq : Integrable (fun ξ : E => (Real.exp (-b*‖ξ‖^2):ℂ)) := by
    have hh := GaussianFourier.integrable_cexp_neg_mul_sq_norm_add
      (V := E) (b := (b:ℂ)) (show 0<(b:ℂ).re from hb) 0 (0:E)
    simpa only [zero_mul,add_zero,← Complex.ofReal_pow,← Complex.ofReal_mul,
      ← Complex.ofReal_neg,← Complex.ofReal_exp] using hh
  have hc : ((∫ y,normalizedGaussianKernel (1/(4*b)) (x-y) ∂μ : ℝ):ℂ)=
      ∫ y,(normalizedGaussianKernel (1/(4*b)) (x-y):ℂ) ∂μ :=
    by
      exact (Complex.ofRealLI.integral_comp_comm (μ := μ)
        (fun y : E => normalizedGaussianKernel (1/(4*b)) (x-y))).symm
  rw [hc]
  simp_rw [normalized_inverse_gaussian b hb]
  rw [integral_const_mul,mixture_inverse_fourier μ volume _ hq x]

end Asakura.Chapter12
