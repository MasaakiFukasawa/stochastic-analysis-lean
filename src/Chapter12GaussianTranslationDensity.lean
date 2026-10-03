import Chapter12AffineGaussianSmoothDensity

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

theorem standard_gaussian_translation_density {d : ℕ} (q : Fin d → ℝ) (t : ℝ) :
    (Measure.pi (fun _ : Fin d => gaussianReal 0 1)).map (fun z => t • q+z)=
      (Measure.pi (fun _ : Fin d => gaussianReal 0 1)).withDensity
        (fun z => ENNReal.ofReal (Real.exp (t*(∑ i,q i*z i)-t^2*(∑ i,(q i)^2)/2))) := by
  let L : (Fin d → ℝ) ≃L[ℝ] (Fin d → ℝ) := ContinuousLinearEquiv.refl ℝ _
  have h0 : Measure.pi (fun _ : Fin d => gaussianReal 0 1)=
      volume.withDensity (fun z => ENNReal.ofReal (affineGaussianDensity L 0 z)) := by
    simpa [L] using
      affine_gaussian_density_law L 0
  have ht := affine_gaussian_density_law L (t • q)
  change (Measure.pi (fun _ : Fin d => gaussianReal 0 1)).map (fun z => t • q+z)=_ at ht
  rw [ht,h0,← withDensity_mul volume
    (show Measurable (fun z => ENNReal.ofReal (affineGaussianDensity L 0 z)) from
      (affine_gaussian_density_smooth L 0).continuous.measurable.ennreal_ofReal)
    (show Measurable (fun z : Fin d → ℝ => ENNReal.ofReal
      (Real.exp (t*(∑ i,q i*z i)-t^2*(∑ i,(q i)^2)/2))) by fun_prop)]
  congr 1
  funext z
  rw [Pi.mul_apply,← ENNReal.ofReal_mul (affine_gaussian_density_positive L 0 z).le]
  congr 1
  unfold affineGaussianDensity
  simp only [L,ContinuousLinearEquiv.refl_symm,ContinuousLinearEquiv.refl_apply,Pi.sub_apply,
    Pi.zero_apply,sub_zero,Pi.smul_apply,smul_eq_mul]
  conv_rhs => rw [mul_assoc,← Real.exp_add]
  congr 2
  have he : (∑ i,(z i-t*q i)^2)=
      (∑ i,(z i)^2)-2*t*(∑ i,q i*z i)+t^2*(∑ i,(q i)^2) := by
    simp only [Finset.mul_sum,← Finset.sum_sub_distrib,← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  rw [he]
  ring

/-- Integration against a shifted Gaussian can be rewritten with a smooth
likelihood ratio even when the payoff is merely measurable. -/
theorem standard_gaussian_translation_integral {d : ℕ} (q : Fin d → ℝ) (t : ℝ)
    (f : (Fin d → ℝ) → ℝ) (hf : Measurable f) :
    (∫ z,f (t • q+z) ∂Measure.pi (fun _ : Fin d => gaussianReal 0 1))=
      ∫ z,f z*Real.exp (t*(∑ i,q i*z i)-t^2*(∑ i,(q i)^2)/2)
        ∂Measure.pi (fun _ : Fin d => gaussianReal 0 1) := by
  rw [← integral_map (by fun_prop : AEMeasurable (fun z : Fin d → ℝ => t • q+z) _)
    hf.aestronglyMeasurable,standard_gaussian_translation_density]
  rw [integral_withDensity_eq_integral_toReal_smul (by fun_prop)
    (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
  apply integral_congr_ae
  exact ae_of_all _ (fun z => by simp [ENNReal.toReal_ofReal (Real.exp_nonneg _),mul_comm])

end Asakura.Chapter12
