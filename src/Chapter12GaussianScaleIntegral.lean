import Chapter12GaussianScaleDensity

open MeasureTheory ProbabilityTheory Set Finset
open scoped ENNReal Topology
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

theorem gaussian_scale_integral {d : ℕ} (s : ℝ) (hs : 0<s) (k : Fin d → ℝ)
    (f : (Fin d → ℝ) → ℝ) (hf : Measurable f) :
    (∫ z,f (fun i => s*z i-s^2*k i/2) ∂Measure.pi (fun _ : Fin d => gaussianReal 0 1))=
      ∫ z,f z*scaleGaussianKernel ((Real.sqrt (2*Real.pi))⁻¹^d) k z s := by
  rw [← integral_map ((show Measurable (fun z : Fin d → ℝ => fun i => s*z i-s^2*k i/2) by fun_prop).aemeasurable)
    hf.aestronglyMeasurable,gaussian_scale_density_law s hs k]
  rw [integral_withDensity_eq_integral_toReal_smul (by unfold scaleGaussianKernel; fun_prop)
    (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
  apply integral_congr_ae
  filter_upwards [] with z
  have hp : 0≤scaleGaussianKernel ((Real.sqrt (2*Real.pi))⁻¹^d) k z s := by
    unfold scaleGaussianKernel
    positivity
  simp only [ENNReal.toReal_ofReal hp,smul_eq_mul]
  ring

 theorem gaussian_scale_score_change {d : ℕ} (s : ℝ) (hs : s≠0) (z k : Fin d → ℝ) :
    (∑ i,(s*z i-s^2*k i/2)^2)/s^3-(d:ℝ)/s-s*(∑ i,(k i)^2)/4=
      ((∑ i,(z i)^2)-(d:ℝ))/s-(∑ i,k i*z i) := by
  have hi (i : Fin d) : (s*z i-s^2*k i/2)^2/s^3-s*(k i)^2/4=
      (z i)^2/s-k i*z i := by
      field_simp [hs]
      <;> ring
  have hh := Finset.sum_congr rfl (fun i (_ : i∈Finset.univ) => hi i)
  simp only [Finset.sum_sub_distrib,← Finset.sum_div,← Finset.mul_sum] at hh
  calc
    _=((∑ i,(s*z i-s^2*k i/2)^2)/s^3-s*(∑ i,(k i)^2)/4)-(d:ℝ)/s := by ring
    _=_ := by rw [hh]; ring

end Asakura.Chapter12
