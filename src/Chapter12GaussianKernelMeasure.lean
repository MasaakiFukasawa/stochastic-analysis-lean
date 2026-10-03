import Chapter12InverseGaussianKernel
import Chapter12RealMixtureDensity

open MeasureTheory Real
open scoped ENNReal
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000

noncomputable def normalizedGaussianKernel {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (c : ℝ) (x : E) : ℝ :=
  Real.exp (-c*‖x‖^2)/(π/c)^(Module.finrank ℝ E/2:ℝ)

theorem normalized_gaussian_kernel_properties {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (c : ℝ) (hc : 0<c) :
    Continuous (normalizedGaussianKernel (E := E) c) ∧
    (∀ x : E,0<normalizedGaussianKernel c x) ∧
    (∀ x : E,normalizedGaussianKernel c x≤1/(π/c)^(Module.finrank ℝ E/2:ℝ)) ∧
    Integrable (normalizedGaussianKernel (E := E) c) ∧
    (∫ x : E,normalizedGaussianKernel c x)=1 ∧
    IsProbabilityMeasure (volume.withDensity (fun x : E => ENNReal.ofReal (normalizedGaussianKernel c x))) := by
  have hC : 0<(π/c)^(Module.finrank ℝ E/2:ℝ) := Real.rpow_pos_of_pos (div_pos pi_pos hc) _
  have hi : Integrable (fun x : E => Real.exp (-c*‖x‖^2)) := by
    have hh := (GaussianFourier.integrable_cexp_neg_mul_sq_norm_add
      (V := E) (b := (c:ℂ)) (show 0<(c:ℂ).re from hc) 0 (0:E)).re
    change Integrable (fun x : E => (Complex.exp (-(c:ℂ)*(‖x‖:ℂ)^2+(0:ℂ)*(inner ℝ (0:E) x:ℂ))).re) at hh
    simpa only [zero_mul,add_zero,← Complex.ofReal_pow,← Complex.ofReal_mul,
      ← Complex.ofReal_neg,← Complex.ofReal_exp,Complex.ofReal_re] using hh
  have hint : (∫ x : E,normalizedGaussianKernel c x)=1 := by
    simp only [normalizedGaussianKernel,integral_div,
      GaussianFourier.integral_rexp_neg_mul_sq_norm hc,div_self hC.ne']
  have hpos (x : E) : 0<normalizedGaussianKernel c x :=
    div_pos (Real.exp_pos _) hC
  have hi' : Integrable (normalizedGaussianKernel (E := E) c) := hi.div_const _
  refine ⟨by unfold normalizedGaussianKernel; fun_prop,hpos,?_,hi',hint,?_⟩
  · intro x
    apply div_le_div_of_nonneg_right _ hC.le
    apply Real.exp_le_one_iff.mpr
    nlinarith [sq_nonneg ‖x‖]
  · constructor
    rw [withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal hi' (ae_of_all _ (fun x => (hpos x).le)),hint]
    simp

end Asakura.Chapter12
