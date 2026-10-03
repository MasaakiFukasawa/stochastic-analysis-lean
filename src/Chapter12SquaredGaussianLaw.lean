import Chapter12SquaredGaussianIntegrable

open MeasureTheory ProbabilityTheory Set
open scoped NNReal
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2800000

theorem squared_gaussian_law (T : ℝ≥0) (hT : T≠0) :
    (gaussianReal 0 T).map (fun x : ℝ => x^2)=
      volume.withDensity (fun x => ENNReal.ofReal (squaredGaussianDensity T x)) := by
  classical
  apply Measure.ext
  intro s hs
  have hpre : MeasurableSet ((fun x : ℝ => x^2) ⁻¹' s) := hs.preimage (by fun_prop)
  rw [Measure.map_apply (by fun_prop) hs,gaussianReal_apply_eq_integral 0 hT,
    withDensity_apply _ hs,←ofReal_integral_eq_lintegral_ofReal
      (squared_gaussian_density_integrable T hT).integrableOn
      (ae_of_all _ (squared_gaussian_density_nonneg T))]
  congr 1
  let f := s.indicator (fun _ : ℝ => (1:ℝ))
  have hp : ((fun x : ℝ => x^2) ⁻¹' s).indicator (gaussianPDFReal 0 T)=
      fun x => gaussianPDFReal 0 T x*f (x^2) := by
    funext x
    by_cases hx : x^2∈s <;> simp [f,hx]
  have hq : s.indicator (squaredGaussianDensity T)=fun x => squaredGaussianDensity T x*f x := by
    funext x
    by_cases hx : x∈s <;> simp [f,hx]
  rw [←integral_indicator hpre,←integral_indicator hs,hp,hq]
  have hi : Integrable (fun x => gaussianPDFReal 0 T x*f (x^2)) volume := by
    rw [←hp]
    exact (integrable_gaussianPDFReal 0 T).indicator hpre
  have hev (x : ℝ) : gaussianPDFReal 0 T (-x)*f ((-x)^2)=gaussianPDFReal 0 T x*f (x^2) := by
    rw [gaussian_pdf_even,neg_sq]
  rw [even_integral_positive_half _ hi hev]
  have hrestrict : (∫ x in Ioi (0:ℝ),squaredGaussianDensity T x*f x)=
      ∫ x,squaredGaussianDensity T x*f x := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    rw [squaredGaussianDensity,if_neg (show ¬0<x from hx),zero_mul]
  rw [←hrestrict,squared_gaussian_change_variables T hT f,←integral_const_mul]
  apply integral_congr_ae
  exact ae_of_all _ (fun x => by ring)

end Asakura.Chapter12
