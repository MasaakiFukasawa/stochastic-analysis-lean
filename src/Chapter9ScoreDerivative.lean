import Chapter9RadialHessian
import Chapter9MixtureScore
import Mathlib.Analysis.Calculus.Deriv.Inv

open MeasureTheory
open scoped RealInnerProductSpace
namespace Asakura.Chapter9
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

theorem radial_mixture_positive {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] (μ : Measure E) [IsProbabilityMeasure μ]
    (c a v : ℝ) (hc : 0<c) (hv : 0<v) (y : E) :
    0<∫ x,radialKernel c a v x y ∂μ := by
  have hm : Continuous (fun x : E => radialKernel c a v x y) := by
    unfold radialKernel
    fun_prop
  have hp x : 0<radialKernel c a v x y := mul_pos hc (Real.exp_pos _)
  have hi : Integrable (fun x => radialKernel c a v x y) μ := by
    apply (integrable_const c).mono' hm.aestronglyMeasurable
    apply ae_of_all
    intro x
    rw [Real.norm_eq_abs,abs_of_pos (hp x)]
    exact mul_le_of_le_one_right hc.le (Real.exp_le_one_iff.mpr
      (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg _)) (by positivity)))
  apply (integral_pos_iff_support_of_nonneg (fun x => (hp x).le) hi).mpr
  have he : Function.support (fun x => radialKernel c a v x y)=Set.univ := by
    ext x
    simp [Function.mem_support,(hp x).ne']
  rw [he,measure_univ]
  exact zero_lt_one

/-- Differentiate the actual ratio of the integrated kernel gradient and
the mixture density. The two terms are precisely the second-density term
and the square-score term in the logarithmic Hessian. -/
theorem radial_score_fderiv {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] [CompleteSpace E]
    (μ : Measure E) [IsProbabilityMeasure μ] (c a v : ℝ)
    (hc : 0<c) (hv : 0<v) (y : E) :
    let p := fun z => ∫ x,radialKernel c a v x z ∂μ
    let g := fun z => ∫ x,(-radialKernel c a v x z/v) • (z-a • x) ∂μ
    let D := ∫ x,(-radialKernel c a v x y/v) • innerSL ℝ (y-a • x) ∂μ
    let H := ∫ x,(-radialKernel c a v x y/v) • ContinuousLinearMap.id ℝ E +
        ((radialKernel c a v x y/v^2) • innerSL ℝ (y-a • x)).smulRight (y-a • x) ∂μ
    HasFDerivAt (fun z => (p z)⁻¹ • g z)
      ((p y)⁻¹ • H + ((-((p y)^2)⁻¹) • D).smulRight (g y)) y := by
  dsimp only
  have hp := radial_mixture_positive μ c a v hc hv y
  have hd := radial_mixture_fderiv μ c a v hc.le hv y
  have hg := radial_mixture_gradient_fderiv μ c a v hc.le hv y
  exact ((hasDerivAt_inv hp.ne').comp_hasFDerivAt y hd).smul hg

/-- Identify that ratio with the gradient of the actual logarithmic
density, not merely with a formally chosen vector field. -/
theorem radial_log_density_fderiv {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] [CompleteSpace E]
    (μ : Measure E) [IsProbabilityMeasure μ] (c a v : ℝ)
    (hc : 0<c) (hv : 0<v) (y : E) :
    let p := fun z => ∫ x,radialKernel c a v x z ∂μ
    let g := fun z => ∫ x,(-radialKernel c a v x z/v) • (z-a • x) ∂μ
    HasFDerivAt (fun z => Real.log (p z)) (innerSL ℝ ((p y)⁻¹ • g y)) y := by
  have hp := radial_mixture_positive μ c a v hc hv y
  have hm : Measurable (fun x => radialKernel c a v x y) := by
    unfold radialKernel
    fun_prop
  have hpos x : 0≤radialKernel c a v x y := mul_nonneg hc.le (Real.exp_pos _).le
  have he := normalized_density_integral μ _ hm hpos _ hp
    (fun x => (-1/v) • (y-a • x))
  have hf : (fun x => radialKernel c a v x y • ((-1/v) • (y-a • x)))=
      (fun x => (-radialKernel c a v x y/v) • (y-a • x)) := by
    funext x
    rw [smul_smul]
    congr 1
    ring
  rw [hf] at he
  have hd := (radial_mixture_score μ c a v hc hv y).2
  dsimp only at hd ⊢
  rw [he] at hd
  exact hd
end Asakura.Chapter9
