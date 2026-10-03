import Chapter9PosteriorHessian

open MeasureTheory
open scoped RealInnerProductSpace
namespace Asakura.Chapter9
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false

/-- Density gradient and score derivative share the same actual integrated
first and second kernel derivatives. -/
theorem radial_density_score_derivatives {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] (μ : Measure E) [IsProbabilityMeasure μ]
    (c a v : ℝ) (hc : 0<c) (hv : 0<v) (y : E) :
    let p := fun z => ∫ x,radialKernel c a v x z ∂μ
    let g := fun z => ∫ x,(-radialKernel c a v x z/v) • (z-a • x) ∂μ
    let H := ∫ x,(-radialKernel c a v x y/v) • ContinuousLinearMap.id ℝ E+
      ((radialKernel c a v x y/v^2) • innerSL ℝ (y-a • x)).smulRight (y-a • x) ∂μ
    HasFDerivAt p (innerSL ℝ (g y)) y ∧
      HasFDerivAt (fun z => (p z)⁻¹ • g z)
        ((p y)⁻¹ • H-dyad ((p y)⁻¹ • g y) ((p y)⁻¹ • g y)) y := by
  dsimp only
  obtain ⟨B,_,hbound⟩ := radial_kernel_derivative_bound (E := E) c a v hc.le hv
  have hgi : Integrable (fun x => (-radialKernel c a v x y/v) • (y-a • x)) μ := by
    apply (integrable_const B).mono' (by unfold radialKernel; fun_prop)
    apply ae_of_all
    intro x
    simpa only [norm_smul,innerSL_apply_norm] using hbound x y
  have hD : (∫ x,(-radialKernel c a v x y/v) • innerSL ℝ (y-a • x) ∂μ)=
      innerSL ℝ (∫ x,(-radialKernel c a v x y/v) • (y-a • x) ∂μ) := by
    simpa only [map_smul] using (innerSL ℝ : E →L[ℝ] E →L[ℝ] ℝ).integral_comp_comm hgi
  have hp := radial_mixture_fderiv μ c a v hc.le hv y
  rw [hD] at hp
  have hs := radial_score_fderiv μ c a v hc hv y
  dsimp only at hs
  rw [hD,quotient_rank_one] at hs
  exact ⟨hp,by simpa only [sub_eq_add_neg] using hs⟩
end Asakura.Chapter9
