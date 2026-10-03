import Chapter5GaussianFirstMomentDerivative

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal BigOperators
namespace Asakura.Chapter5
open Asakura.FullAudit
set_option maxHeartbeats 3800000
set_option backward.isDefEq.respectTransparency false

/-- A second spatial derivative of the actual Gaussian average is
obtained by differentiating the coordinate-moment formula. The input
requires only a continuous bounded first derivative. -/
theorem gaussian_average_second_coordinate
    (n : ℕ) (i : Fin (n+1)) (f : (Fin (n+1) → ℝ) → ℝ)
    (D : (Fin (n+1) → ℝ) → (Fin (n+1) → ℝ) →L[ℝ] ℝ)
    (hd : ∀ x,HasFDerivAt f (D x) x) (hDc : Continuous D)
    (C : ℝ≥0) (hD : ∀ x,‖D x‖≤C) (x : Fin (n+1) → ℝ) (t : ℝ) (ht : 0<t) :
    let A := fun y => ∫ z,f (y+Real.sqrt t • z) ∂Measure.pi (fun _ : Fin (n+1) => gaussianReal 0 1)
    HasDerivAt (fun s : ℝ => fderiv ℝ A (x+s • (Pi.single i 1)) (Pi.single i 1))
      ((∫ z,z i*D (x+Real.sqrt t • z) (Pi.single i 1) ∂Measure.pi (fun _ : Fin (n+1) => gaussianReal 0 1))/Real.sqrt t) 0 := by
  dsimp only
  let ν := Measure.pi (fun _ : Fin (n+1) => gaussianReal 0 1)
  let e : Fin (n+1) → ℝ := Pi.single i 1
  obtain ⟨hfirst,_,_,_⟩ := averaged_bounded_fderiv ν (gaussian_product_first_moment (n+1)) f D hd hDc C hD
  have hgrad y : fderiv ℝ (fun y => ∫ z,f (y+Real.sqrt t • z) ∂ν) y e=
      (∫ z,z i*f (y+Real.sqrt t • z) ∂ν)/Real.sqrt t := by
    have hDi : Integrable (fun z => D (y+Real.sqrt t • z)) ν :=
      Integrable.of_bound (hDc.comp (by fun_prop)).aestronglyMeasurable C (ae_of_all _ fun z => hD _)
    rw [(hfirst y t).fderiv,ContinuousLinearMap.integral_apply hDi]
    exact gaussian_gradient_coordinate_moment n i f D hd hDc C hD y t ht
  have hz : Integrable (fun z : Fin (n+1) → ℝ => z i) ν :=
    integrable_comp_eval (μ := fun _ : Fin (n+1) => gaussianReal 0 1) (i := i) (f := fun z : ℝ => z)
      ((memLp_id_gaussianReal' 1 (by norm_num)).integrable (by norm_num))
  have hDi : Integrable (fun z => z i • D (x+Real.sqrt t • z)) ν := by
    apply (hz.norm.mul_const C).mono' (((continuous_apply i).smul (hDc.comp (by fun_prop))).aestronglyMeasurable)
    exact ae_of_all _ fun z => by
      change ‖z i • D (x+Real.sqrt t • z)‖≤‖z i‖ * (C:ℝ)
      rw [norm_smul,Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (hD _) (abs_nonneg _)
  have hpath : HasDerivAt (fun s : ℝ => x+s • e) e 0 := by
    simpa only [one_smul,id_eq] using ((hasDerivAt_id (0:ℝ)).smul_const e).const_add x
  have hh := ((gaussian_coordinate_moment_fderiv n i f D hd hDc C hD (x+(0:ℝ) • e) t).comp_hasDerivAt (0:ℝ)
    hpath).div_const (Real.sqrt t)
  simp only [zero_smul,add_zero] at hh
  have he : (∫ z,z i • D (x+Real.sqrt t • z) ∂ν) e=
      ∫ z,z i*D (x+Real.sqrt t • z) e ∂ν := by
    rw [ContinuousLinearMap.integral_apply hDi]
    rfl
  rw [he] at hh
  simp only [Function.comp_def] at hh
  convert hh using 1
  funext s
  exact hgrad (x+s • e)

end Asakura.Chapter5
