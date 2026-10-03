import Chapter9PosteriorHessian
import Mathlib.Analysis.Calculus.MeanValue

open MeasureTheory
open scoped NNReal RealInnerProductSpace
namespace Asakura.Chapter9
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false

/-- A bounded prior gives a global, quantitative Lipschitz estimate for
the actual Gaussian-mixture score. This connects the posterior covariance
calculation to the ODE regularity requirement. -/
theorem radial_score_global_lipschitz {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] (μ : Measure E) [IsProbabilityMeasure μ]
    (c a v : ℝ) (hc : 0<c) (hv : 0<v) (R : ℝ) (hR : 0≤R)
    (hb : ∀ᵐ x ∂μ,‖x‖≤R) :
    LipschitzWith ⟨1/v+a^2/v^2*R^2,by positivity⟩
      (fun y => (∫ x,radialKernel c a v x y ∂μ)⁻¹ •
        (∫ x,(-radialKernel c a v x y/v) • (y-a • x) ∂μ)) := by
  let p := fun y => ∫ x,radialKernel c a v x y ∂μ
  let score := fun y => (p y)⁻¹ • (∫ x,(-radialKernel c a v x y/v) • (y-a • x) ∂μ)
  have hd y := radial_score_posterior_hessian μ c a v hc hv R hR hb y
  apply lipschitzWith_of_nnnorm_fderiv_le (fun y => (hd y).differentiableAt)
  intro y
  rw [(hd y).fderiv]
  apply NNReal.coe_le_coe.mp
  change ‖(-1/v) • ContinuousLinearMap.id ℝ E+(a^2/v^2) •
    covarianceOperator (μ.withDensity (fun x => ENNReal.ofReal (radialKernel c a v x y/p y)))‖ ≤ _
  let P := μ.withDensity (fun x => ENNReal.ofReal (radialKernel c a v x y/p y))
  haveI : IsProbabilityMeasure P := (radial_mixture_score μ c a v hc hv y).1
  have hbP : ∀ᵐ x ∂P,‖x‖≤R := normalized_density_preserves_ae μ
    (fun x => radialKernel c a v x y) (p y) {x | ‖x‖≤R} hb
  have hcov := bounded_covariance_operator P R hR hbP
  have hi : ‖(-1/v) • ContinuousLinearMap.id ℝ E‖ ≤ 1/v := by
    rw [norm_smul,Real.norm_eq_abs,abs_div,abs_neg,abs_one,abs_of_pos hv]
    exact (mul_le_mul_of_nonneg_left ContinuousLinearMap.norm_id_le (by positivity)).trans_eq (mul_one _)
  have hc2 : ‖(a^2/v^2) • covarianceOperator P‖ ≤ a^2/v^2*R^2 := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (by positivity : 0≤a^2/v^2)]
    exact mul_le_mul_of_nonneg_left hcov (by positivity)
  exact (norm_add_le _ _).trans (add_le_add hi hc2)

/-- The probability-flow velocity is globally Lipschitz at every
positive time, with its explicit bound expressed in OU coefficients. -/
theorem radial_probability_velocity_lipschitz {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] (μ : Measure E) [IsProbabilityMeasure μ]
    (c a v : ℝ) (hc : 0<c) (hv : 0<v) (R : ℝ) (hR : 0≤R)
    (hb : ∀ᵐ x ∂μ,‖x‖≤R) :
    LipschitzWith (1+⟨1/v+a^2/v^2*R^2,by positivity⟩)
      (fun y => -y-(∫ x,radialKernel c a v x y ∂μ)⁻¹ •
        (∫ x,(-radialKernel c a v x y/v) • (y-a • x) ∂μ)) :=
  LipschitzWith.id.neg.sub (radial_score_global_lipschitz μ c a v hc hv R hR hb)
end Asakura.Chapter9
