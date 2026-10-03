import Chapter12GaussianWeightedShiftDerivative
import Chapter12BasketDeltaMeasurable

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal Topology
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2800000

/-- Differentiation of the first delta score under a change of another
initial stock price. This is the covariance-corrected part of gamma. -/
theorem basket_measurable_score_derivative {d : ℕ}
    (A : Matrix (Fin d) (Fin d) ℝ) (hA : A.det≠0) (x b : Fin d → ℝ)
    (i j : Fin d) (hx : 0<x j)
    (h : (Fin d → ℝ) → ℝ) (hm : Measurable h)
    (C : ℝ) (n : ℕ) (hb : ∀ s,|h s|≤C*(1+‖s‖^n)) :
    HasDerivAt
      (fun u : ℝ => ∫ z,h (fun k => (if k=j then u else x k)*Real.exp (b k+∑ a,A k a*z a))*
        (∑ a,(A⁻¹) a i*z a) ∂Measure.pi (fun _ : Fin d => gaussianReal 0 1))
      ((∫ z,h (fun k => x k*Real.exp (b k+∑ a,A k a*z a))*
        ((∑ a,(A⁻¹) a i*z a)*(∑ a,(A⁻¹) a j*z a)-(∑ a,(A⁻¹) a i*(A⁻¹) a j))
        ∂Measure.pi (fun _ : Fin d => gaussianReal 0 1))/x j) (x j) := by
  classical
  let μ := Measure.pi (fun _ : Fin d => gaussianReal 0 1)
  let f : (Fin d → ℝ) → ℝ := fun z => h (fun k => x k*Real.exp (b k+∑ a,A k a*z a))
  let q : Fin d → ℝ := fun a => (A⁻¹) a i
  let v : Fin d → ℝ := fun a => (A⁻¹) a j
  let G : ℝ → ℝ := fun t => ∫ z,f (t • v+z)*(∑ a,q a*z a) ∂μ
  have hfm : Measurable f := hm.comp (by fun_prop)
  have hfi : MemLp f 4 μ := lognormal_polynomial_payoff_moments x b A h hm C n hb 4 (by norm_num)
  have hd := finite_gaussian_weighted_shift_derivative q v f hfm hfi
  have hl : HasDerivAt (fun u => Real.log u-Real.log (x j)) ((x j)⁻¹) (x j) :=
    (Real.hasDerivAt_log hx.ne').sub_const _
  have hd' : HasDerivAt G
      (∫ z,f z*((∑ a,q a*z a)*(∑ a,v a*z a)-(∑ a,q a*v a)) ∂μ)
      (Real.log (x j)-Real.log (x j)) := by simpa only [sub_self] using hd
  have hdcomp := hd'.comp (x j) hl
  have he : (fun u : ℝ => ∫ z,h (fun k => (if k=j then u else x k)*Real.exp (b k+∑ a,A k a*z a))*
      (∑ a,q a*z a) ∂μ) =ᶠ[𝓝 (x j)] (fun u => G (Real.log u-Real.log (x j))) := by
    filter_upwards [eventually_gt_nhds hx] with u hu
    dsimp only [G]
    apply integral_congr_ae
    apply ae_of_all
    intro z
    apply congrArg (fun r : ℝ => r*(∑ a,q a*z a))
    dsimp only [f,v]
    have hh := basket_log_price_shift A hA x b z j (Real.log u-Real.log (x j))
    change h (fun k => (if k=j then u else x k)*Real.exp (b k+∑ a,A k a*z a))=
      h (fun k => x k*Real.exp (b k+∑ a,A k a*((Real.log u-Real.log (x j))*(A⁻¹) a j+z a)))
    rw [hh]
    have hexp : x j*Real.exp (Real.log u-Real.log (x j))=u := by
      rw [Real.exp_sub,Real.exp_log hu,Real.exp_log hx]
      field_simp
    rw [hexp]
  simpa only [div_eq_mul_inv] using hdcomp.congr_of_eventuallyEq he

end Asakura.Chapter12
