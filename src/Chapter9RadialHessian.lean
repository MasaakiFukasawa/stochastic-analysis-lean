import Chapter9RadialKernelDerivative

open MeasureTheory
open scoped RealInnerProductSpace
namespace Asakura.Chapter9
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

/-- Actual derivative of the kernel gradient as a vector-valued function.
This is the Hessian before integration against the prior. -/
theorem radial_kernel_hessian {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (c a v : ℝ) (hv : v≠0) (x y : E) :
    HasFDerivAt (fun z => (-radialKernel c a v x z/v) • (z-a • x))
      ((-radialKernel c a v x y/v) • ContinuousLinearMap.id ℝ E +
        ((radialKernel c a v x y/v^2) • innerSL ℝ (y-a • x)).smulRight
          (y-a • x)) y := by
  have hk := (radial_kernel_fderiv c a v hv x y).const_mul (-1/v)
  have hz := (hasFDerivAt_id (𝕜 := ℝ) y).sub_const (a • x)
  have hd := hk.smul hz
  convert hd using 1
  · funext z
    dsimp only [Function.comp_def,id_eq,Pi.smul_apply]
    congr 1
    ring
  · ext h
    simp only [add_apply,smul_apply,ContinuousLinearMap.smulRight_apply,
      ContinuousLinearMap.id_apply,innerSL_apply_apply,smul_smul,
      Function.comp_def,id_eq]
    congr 1
    · congr 1
      ring
    · congr 1
      ring

theorem radial_kernel_hessian_bound {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (c a v : ℝ) (hc : 0≤c) (hv : 0<v) :
    ∃ B : ℝ, 0≤B ∧ ∀ x y : E,
      ‖(-radialKernel c a v x y/v) • ContinuousLinearMap.id ℝ E +
        ((radialKernel c a v x y/v^2) • innerSL ℝ (y-a • x)).smulRight
          (y-a • x)‖≤B := by
  obtain ⟨C,hC,hb⟩ := polynomial_gaussian_bound (1/(2*v)) (by positivity) 2
  refine ⟨c*(1/v+1/v^2)*C,by positivity,?_⟩
  intro x y
  let k := radialKernel c a v x y
  let r := ‖y-a • x‖
  have hk : 0≤k := mul_nonneg hc (Real.exp_pos _).le
  have h0 : ‖(-k/v) • ContinuousLinearMap.id ℝ E‖≤k/v := by
    rw [norm_smul,Real.norm_eq_abs,abs_div,abs_neg,abs_of_nonneg hk,abs_of_pos hv]
    exact (mul_le_mul_of_nonneg_left ContinuousLinearMap.norm_id_le
      (div_nonneg hk hv.le)).trans_eq (mul_one _)
  have h1 : ‖((k/v^2) • innerSL ℝ (y-a • x)).smulRight (y-a • x)‖=
      k/v^2*r^2 := by
    rw [ContinuousLinearMap.norm_smulRight_apply,norm_smul,Real.norm_eq_abs,
      abs_of_nonneg (div_nonneg hk (sq_nonneg v)),innerSL_apply_norm]
    dsimp [r]
    ring
  have h2 : k/v+k/v^2*r^2≤c*(1/v+1/v^2)*C := by
    have hh := hb r (norm_nonneg _)
    have he : -r^2/(2*v)= -(1/(2*v))*r^2 := by ring
    have ht : k*(1+r^2)≤c*C := by
      dsimp [k,radialKernel]
      change c*Real.exp (-r^2/(2*v))*(1+r^2)≤c*C
      rw [he]
      nlinarith [mul_le_mul_of_nonneg_left hh hc]
    have ha : 0≤k/v*r^2+k/v^2 := by positivity
    have hb' := mul_le_mul_of_nonneg_left ht (show 0≤1/v+1/v^2 by positivity)
    simp only [div_eq_mul_inv] at ha hb' ⊢
    nlinarith only [ha,hb']
  exact (norm_add_le _ _).trans ((add_le_add h0 h1.le).trans h2)

/-- Differentiate the actual integral of the kernel gradient. Both
integrability and differentiation under the integral follow from Gaussian
decay; no moments of the initial finite measure are required. -/
theorem radial_mixture_gradient_fderiv {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] [CompleteSpace E]
    (μ : Measure E) [IsFiniteMeasure μ] (c a v : ℝ)
    (hc : 0≤c) (hv : 0<v) (y : E) :
    HasFDerivAt (fun z => ∫ x,(-radialKernel c a v x z/v) • (z-a • x) ∂μ)
      (∫ x,(-radialKernel c a v x y/v) • ContinuousLinearMap.id ℝ E +
        ((radialKernel c a v x y/v^2) • innerSL ℝ (y-a • x)).smulRight
          (y-a • x) ∂μ) y := by
  obtain ⟨B,hB,hbound⟩ := radial_kernel_hessian_bound (E := E) c a v hc hv
  obtain ⟨A,hA,hfirst⟩ := radial_kernel_derivative_bound (E := E) c a v hc hv
  have hm z : Continuous (fun x : E => (-radialKernel c a v x z/v) • (z-a • x)) := by
    unfold radialKernel
    fun_prop
  have hd z : Continuous (fun x : E =>
      (-radialKernel c a v x z/v) • ContinuousLinearMap.id ℝ E +
        ((radialKernel c a v x z/v^2) • innerSL ℝ (z-a • x)).smulRight
          (z-a • x)) := by
    unfold radialKernel
    fun_prop
  have hi : Integrable (fun x => (-radialKernel c a v x y/v) • (y-a • x)) μ := by
    apply (integrable_const A).mono' (hm y).aestronglyMeasurable
    apply ae_of_all
    intro x
    simpa only [norm_smul,innerSL_apply_norm] using hfirst x y
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := μ)
    (F := fun z x => (-radialKernel c a v x z/v) • (z-a • x))
    (F' := fun z x => (-radialKernel c a v x z/v) • ContinuousLinearMap.id ℝ E +
      ((radialKernel c a v x z/v^2) • innerSL ℝ (z-a • x)).smulRight (z-a • x))
    (s := Set.univ) (bound := fun _ => B) Filter.univ_mem
  · exact Filter.Eventually.of_forall (fun z => (hm z).aestronglyMeasurable)
  · exact hi
  · exact (hd y).aestronglyMeasurable
  · exact ae_of_all _ (fun x z _ => hbound x z)
  · exact integrable_const _
  · exact ae_of_all _ (fun x z _ => radial_kernel_hessian c a v hv.ne' x z)
end Asakura.Chapter9
