import Chapter12GaussianKernelMeasure

open MeasureTheory Set
namespace Asakura.EndToEnd
open Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

/-- The Gaussian noise in the appendix smoothing proof has a finite first
 moment, proved directly from its density. -/
theorem gaussian_kernel_first_moment {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] :
    Integrable (fun x : E => ‖x‖)
      (volume.withDensity (fun x : E => ENNReal.ofReal (normalizedGaussianKernel (1/4) x))) := by
  have hg := normalized_gaussian_kernel_properties (E:=E) (1/4) (by norm_num)
  rw [integrable_withDensity_iff_integrable_smul' hg.1.measurable.ennreal_ofReal
    (.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (hg.2.1 _).le,smul_eq_mul]
  have hi : Integrable (fun x : E => Real.exp (-(1/8:ℝ)*‖x‖^2)) := by
    have hh := (GaussianFourier.integrable_cexp_neg_mul_sq_norm_add
      (V:=E) (b:=((1/8:ℝ):ℂ)) (by norm_num) 0 (0:E)).re
    change Integrable (fun x : E => (Complex.exp (-((1/8:ℝ):ℂ)*(‖x‖:ℂ)^2+(0:ℂ)*(inner ℝ (0:E) x:ℂ))).re) at hh
    simpa only [zero_mul,add_zero,← Complex.ofReal_pow,← Complex.ofReal_mul,
      ← Complex.ofReal_neg,← Complex.ofReal_exp,Complex.ofReal_re] using hh
  let D := (Real.pi/(1/4:ℝ))^(Module.finrank ℝ E/2:ℝ)
  have hD : 0 < D := Real.rpow_pos_of_pos (by positivity) _
  apply (hi.const_mul (8/D)).mono' (hg.1.mul continuous_norm).aestronglyMeasurable
  apply ae_of_all
  intro x
  change ‖normalizedGaussianKernel (1/4) x * ‖x‖‖ ≤ (8/D)*Real.exp (-(1/8:ℝ)*‖x‖^2)
  rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (hg.2.1 x).le (norm_nonneg _))]
  have hnorm : ‖x‖ ≤ 8*Real.exp (‖x‖^2/8) := by
    have he := Real.add_one_le_exp (‖x‖^2/8)
    nlinarith [sq_nonneg (‖x‖-1)]
  have hm := mul_le_mul_of_nonneg_left hnorm (Real.exp_pos (-(1/4:ℝ)*‖x‖^2)).le
  have he : Real.exp (-(1/4:ℝ)*‖x‖^2) * (8*Real.exp (‖x‖^2/8)) =
      8*Real.exp (-(1/8:ℝ)*‖x‖^2) := by
    rw [← mul_assoc,mul_comm _ (8:ℝ),mul_assoc,← Real.exp_add]
    congr 2
    ring
  rw [he] at hm
  change Real.exp (-(1/4:ℝ)*‖x‖^2)/D * ‖x‖ ≤ (8/D)*Real.exp (-(1/8:ℝ)*‖x‖^2)
  simpa only [div_mul_eq_mul_div] using div_le_div_of_nonneg_right hm hD.le

#print axioms gaussian_kernel_first_moment
end Asakura.EndToEnd
