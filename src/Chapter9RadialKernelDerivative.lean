import Chapter9GaussianDomination
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.ParametricIntegral

open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace
namespace Asakura.Chapter9
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

noncomputable def radialKernel {E : Type*} [Norm E] [Sub E] [SMul ℝ E]
    (c a v : ℝ) (x y : E) := c*Real.exp (-‖y-a • x‖^2/(2*v))

theorem radial_kernel_fderiv {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (c a v : ℝ) (hv : v≠0) (x y : E) :
    HasFDerivAt (radialKernel c a v x)
      ((-radialKernel c a v x y/v) • innerSL ℝ (y-a • x)) y := by
  have hN := (hasStrictFDerivAt_norm_sq (y-a • x)).hasFDerivAt.comp y ((hasFDerivAt_id y).sub_const (a • x))
  have hd := ((hN.const_mul (-1/(2*v))).exp).const_mul c
  convert hd using 1
  · funext z
    dsimp [radialKernel]
    congr 2
    ring
  · ext h
    simp only [Function.comp_def,id_eq,radialKernel,smul_apply,ContinuousLinearMap.comp_apply,ContinuousLinearMap.id_apply,
      innerSL_apply_apply,neg_apply,smul_eq_mul]
    rw [show -1/(2*v)*‖y-a • x‖^2= -‖y-a • x‖^2/(2*v) by ring]
    field_simp
    <;> ring

/-- The spatial derivative is bounded uniformly in both x and y. Thus
integrating against any finite initial measure is legitimate. -/
theorem radial_kernel_derivative_bound {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (c a v : ℝ) (hc : 0≤c) (hv : 0<v) :
    ∃ B : ℝ,0≤B ∧ ∀ x y : E,
      ‖(-radialKernel c a v x y/v) • innerSL ℝ (y-a • x)‖≤B := by
  obtain ⟨C,hC,hb⟩ := polynomial_gaussian_bound (1/(2*v)) (by positivity) 1
  refine ⟨c/v*C,by positivity,?_⟩
  intro x y
  have h := hb ‖y-a • x‖ (norm_nonneg _)
  have he : -‖y-a • x‖^2/(2*v)= -(1/(2*v))*‖y-a • x‖^2 := by ring
  have hK : 0≤radialKernel c a v x y := mul_nonneg hc (Real.exp_pos _).le
  rw [norm_smul,Real.norm_eq_abs,abs_div,abs_neg,abs_of_nonneg hK,abs_of_pos hv,innerSL_apply_norm]
  dsimp [radialKernel]
  rw [he]
  have hr := mul_le_mul_of_nonneg_right (show ‖y-a • x‖≤1+‖y-a • x‖ by linarith)
    (Real.exp_pos (-(1/(2*v))*‖y-a • x‖^2)).le
  have hh : ‖y-a • x‖*Real.exp (-(1/(2*v))*‖y-a • x‖^2)≤C := hr.trans (by simpa only [pow_one] using h)
  have hh' := mul_le_mul_of_nonneg_left hh (div_nonneg hc hv.le)
  convert hh' using 1 <;> ring

/-- The actual derivative of the Gaussian mixture is the integral of the
actual kernel derivative; no differentiability of the mixture is assumed. -/
theorem radial_mixture_fderiv {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [CompleteSpace E]
    (μ : Measure E) [IsFiniteMeasure μ] (c a v : ℝ) (hc : 0≤c) (hv : 0<v) (y : E) :
    HasFDerivAt (fun z => ∫ x,radialKernel c a v x z ∂μ)
      (∫ x,(-radialKernel c a v x y/v) • innerSL ℝ (y-a • x) ∂μ) y := by
  obtain ⟨B,hB,hbound⟩ := radial_kernel_derivative_bound (E := E) c a v hc hv
  have hm z : Continuous (fun x : E => radialKernel c a v x z) := by unfold radialKernel; fun_prop
  have hdm z : Continuous (fun x : E => (-radialKernel c a v x z/v) • innerSL ℝ (z-a • x)) := by fun_prop
  have hi : Integrable (fun x => radialKernel c a v x y) μ := by
    apply (integrable_const c).mono' (hm y).aestronglyMeasurable
    apply ae_of_all
    intro x
    rw [radialKernel,Real.norm_eq_abs,abs_of_nonneg (mul_nonneg hc (Real.exp_pos _).le)]
    exact mul_le_of_le_one_right hc (Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg _)) (by positivity)))
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := μ) (F := fun z x => radialKernel c a v x z)
    (F' := fun z x => (-radialKernel c a v x z/v) • innerSL ℝ (z-a • x))
    (s := univ) (bound := fun _ => B) univ_mem
  · exact Eventually.of_forall (fun z => (hm z).aestronglyMeasurable)
  · exact hi
  · exact (hdm y).aestronglyMeasurable
  · exact ae_of_all _ (fun x z _ => hbound x z)
  · exact integrable_const _
  · exact ae_of_all _ (fun x z _ => radial_kernel_fderiv c a v hv.ne' x z)
end Asakura.Chapter9
