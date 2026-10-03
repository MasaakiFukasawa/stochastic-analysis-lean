import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic

open MeasureTheory ProbabilityTheory Set
open scoped NNReal
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000

theorem gaussian_pdf_lower_bound_near_zero (T : ℝ≥0) (x : ℝ) (hx : x∈Ioo (0:ℝ) 1) :
    gaussianPDFReal 0 T 1≤gaussianPDFReal 0 T x := by
  unfold gaussianPDFReal
  simp only [sub_zero,one_pow]
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (Real.sqrt_nonneg _))
  apply Real.exp_le_exp.mpr
  apply div_le_div_of_nonneg_right _ (by positivity)
  nlinarith [hx.1,hx.2,sq_nonneg (x-1)]

/-- A positive Gaussian density at zero makes the inverse square fail to
be integrable. This supplies a concrete failed inverse moment in the example. -/
theorem gaussian_inverse_square_not_integrable (T : ℝ≥0) (hT : T≠0) :
    ¬Integrable (fun x : ℝ => (x^2)⁻¹) (gaussianReal 0 T) := by
  intro hi
  rw [gaussianReal_of_var_ne_zero _ hT,gaussianPDF_def] at hi
  have hw := (integrable_withDensity_iff_integrable_smul'
    (measurable_gaussianPDFReal 0 T).ennreal_ofReal
    (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))).mp hi
  simp only [ENNReal.toReal_ofReal (gaussianPDFReal_nonneg _ _ _),smul_eq_mul] at hw
  let c := gaussianPDFReal 0 T 1
  have hc : 0<c := gaussianPDFReal_pos 0 T 1 hT
  have hdom := (hw.div_const c).integrableOn (s := Ioo (0:ℝ) 1)
  have hinv : IntegrableOn (fun x : ℝ => (x^2)⁻¹) (Ioo (0:ℝ) 1) := by
    apply hdom.mono' (by fun_prop)
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    have hg := gaussian_pdf_lower_bound_near_zero T x hx
    rw [Real.norm_eq_abs,abs_of_nonneg (inv_nonneg.mpr (sq_nonneg x))]
    apply (le_div_iff₀ hc).mpr
    nlinarith [mul_le_mul_of_nonneg_right hg (inv_nonneg.mpr (sq_nonneg x))]
  have hr : IntegrableOn (fun x : ℝ => x^(-2:ℝ)) (Ioo (0:ℝ) 1) := by
    apply hinv.congr_fun _ measurableSet_Ioo
    intro x hx
    change (x^2)⁻¹=x^(-(2:ℝ))
    rw [Real.rpow_neg hx.1.le,Real.rpow_two]
  have hh := (intervalIntegral.integrableOn_Ioo_rpow_iff (t := 1) zero_lt_one).mp hr
  norm_num at hh

end Asakura.Chapter12
