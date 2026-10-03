import Chapter12GaussianTranslationDerivative
import Chapter12LognormalPayoffMoments
import Chapter12BasketLogPriceShift
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal Topology
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2800000

/-- Delta for an arbitrary Borel payoff of polynomial growth, including
basket digitals. A is the volatility matrix multiplied by sqrt(T). -/
theorem basket_measurable_delta {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ) (hA : A.det≠0)
    (x b : Fin d → ℝ) (i : Fin d) (hx : 0<x i)
    (h : (Fin d → ℝ) → ℝ) (hm : Measurable h)
    (C : ℝ) (n : ℕ) (hb : ∀ s,|h s|≤C*(1+‖s‖^n)) :
    HasDerivAt
      (fun u : ℝ => ∫ z,h (fun k => (if k=i then u else x k)*Real.exp (b k+∑ j,A k j*z j))
        ∂Measure.pi (fun _ : Fin d => gaussianReal 0 1))
      (∫ z,h (fun k => x k*Real.exp (b k+∑ j,A k j*z j))*
        ((∑ j,(A⁻¹) j i*z j)/x i) ∂Measure.pi (fun _ : Fin d => gaussianReal 0 1)) (x i) := by
  classical
  let μ := Measure.pi (fun _ : Fin d => gaussianReal 0 1)
  let f : (Fin d → ℝ) → ℝ := fun z => h (fun k => x k*Real.exp (b k+∑ j,A k j*z j))
  let q : Fin d → ℝ := fun j => (A⁻¹) j i
  let G : ℝ → ℝ := fun t => ∫ z,f (t • q+z) ∂μ
  have hfm : Measurable f := hm.comp (by fun_prop)
  have hfi : MemLp f 2 μ := lognormal_polynomial_payoff_moments x b A h hm C n hb 2 (by norm_num)
  have hd : HasDerivAt G (∫ z,f z*(∑ j,q j*z j) ∂μ) 0 :=
    finite_gaussian_translation_derivative_zero q f hfm hfi
  have hl : HasDerivAt (fun u => Real.log u-Real.log (x i)) ((x i)⁻¹) (x i) :=
    (Real.hasDerivAt_log hx.ne').sub_const _
  have hd' : HasDerivAt G (∫ z,f z*(∑ j,q j*z j) ∂μ) (Real.log (x i)-Real.log (x i)) := by
    simpa only [sub_self] using hd
  have hdcomp := hd'.comp (x i) hl
  have he : (fun u : ℝ => ∫ z,h (fun k => (if k=i then u else x k)*Real.exp (b k+∑ j,A k j*z j)) ∂μ)
      =ᶠ[𝓝 (x i)] (fun u => G (Real.log u-Real.log (x i))) := by
    filter_upwards [eventually_gt_nhds hx] with u hu
    dsimp only [G]
    apply integral_congr_ae
    apply ae_of_all
    intro z
    dsimp only [f,q]
    have hh := basket_log_price_shift A hA x b z i (Real.log u-Real.log (x i))
    change h (fun k => (if k=i then u else x k)*Real.exp (b k+∑ j,A k j*z j))=
      h (fun k => x k*Real.exp (b k+∑ j,A k j*((Real.log u-Real.log (x i))*(A⁻¹) j i+z j)))
    rw [hh]
    have hexp : x i*Real.exp (Real.log u-Real.log (x i))=u := by
      rw [Real.exp_sub,Real.exp_log hu,Real.exp_log hx]
      field_simp
    rw [hexp]
  have hfinal := hdcomp.congr_of_eventuallyEq he
  convert hfinal using 1
  rw [← integral_mul_const]
  apply integral_congr_ae
  exact ae_of_all _ (fun z => by dsimp only [f,q]; ring)

end Asakura.Chapter12
