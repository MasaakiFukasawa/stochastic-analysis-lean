import Chapter12GaussianScaleDerivativeEnvelope
import Mathlib.Analysis.Calculus.ParametricIntegral

open MeasureTheory Set Filter Finset
open scoped Topology
namespace Asakura.Chapter12
set_option maxHeartbeats 2400000

/-- A weighted Gaussian envelope justifies scale differentiation for a
measurable payoff; differentiability of the payoff is unnecessary. -/
theorem gaussian_scale_integral_derivative {d : ℕ} (μ : Measure (Fin d → ℝ))
    (f : (Fin d → ℝ) → ℝ) (hf : AEStronglyMeasurable f μ)
    (C s : ℝ) (hs : 0<s) (k : Fin d → ℝ)
    (hi : Integrable (fun z => f z*scaleGaussianKernel C k z s) μ)
    (henv : Integrable (fun z => |f z| *((1+∑ i,(z i)^2)*
      Real.exp (-(∑ i,(z i)^2)/(16*s^2)))) μ) :
    HasDerivAt (fun u => ∫ z,f z*scaleGaussianKernel C k z u ∂μ)
      (∫ z,f z*(scaleGaussianKernel C k z s*
        ((∑ i,(z i)^2)/s^3-(d:ℝ)/s-s*(∑ i,(k i)^2)/4)) ∂μ) s := by
  have hn : Ioo (s/2) (2*s)∈𝓝 s := Ioo_mem_nhds (by linarith) (by linarith)
  have hm (u : ℝ) : AEStronglyMeasurable (fun z => f z*scaleGaussianKernel C k z u) μ := by
    apply hf.mul
    apply Continuous.aestronglyMeasurable
    unfold scaleGaussianKernel
    fun_prop
  have hmd : AEStronglyMeasurable (fun z => f z*(scaleGaussianKernel C k z s*
        ((∑ i,(z i)^2)/s^3-(d:ℝ)/s-s*(∑ i,(k i)^2)/4))) μ := by
    apply hf.mul
    apply Continuous.aestronglyMeasurable
    unfold scaleGaussianKernel
    fun_prop
  let B := scaleEnvelopeConstant d C s k*(8/s^3+2*(d:ℝ)/s+s*(∑ i,(k i)^2)/2)
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ) hn
    (Eventually.of_forall hm) hi hmd _ (henv.const_mul B) _).2
  · filter_upwards [] with z u hu
    rw [Real.norm_eq_abs,abs_mul]
    have hh := mul_le_mul_of_nonneg_left
      (gaussian_scale_derivative_envelope C s u hs hu.1.le hu.2.le z k) (abs_nonneg (f z))
    dsimp [B]
    nlinarith [hh]
  · exact ae_of_all _ (fun z u hu =>
      (scale_gaussian_kernel_derivative C u (ne_of_gt (by linarith [hu.1])) z k).const_mul (f z))

end Asakura.Chapter12
