import Chapter5GaussianLipschitzLp
import Chapter5GaussianTrace

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal BigOperators
namespace Asakura.Chapter5
open Asakura.FullAudit
set_option maxHeartbeats 3600000
set_option backward.isDefEq.respectTransparency false

/-- Differentiate the Gaussian coordinate moment using only the bounded
first derivative of f. The dominating function is C times |z_i|. -/
theorem gaussian_coordinate_moment_fderiv
    (n : ℕ) (i : Fin (n+1)) (f : (Fin (n+1) → ℝ) → ℝ)
    (D : (Fin (n+1) → ℝ) → (Fin (n+1) → ℝ) →L[ℝ] ℝ)
    (hd : ∀ x,HasFDerivAt f (D x) x) (hDc : Continuous D)
    (C : ℝ≥0) (hD : ∀ x,‖D x‖≤C) (x : Fin (n+1) → ℝ) (t : ℝ) :
    HasFDerivAt (fun y => ∫ z,z i*f (y+Real.sqrt t • z) ∂Measure.pi (fun _ : Fin (n+1) => gaussianReal 0 1))
      (∫ z,z i • D (x+Real.sqrt t • z) ∂Measure.pi (fun _ : Fin (n+1) => gaussianReal 0 1)) x := by
  let ν := Measure.pi (fun _ : Fin (n+1) => gaussianReal 0 1)
  have hfc : Continuous f := continuous_iff_continuousAt.mpr (fun y => (hd y).continuousAt)
  have hl : LipschitzWith C f := lipschitzWith_of_nnnorm_fderiv_le
    (fun y => (hd y).differentiableAt) (fun y => by rw [(hd y).fderiv];exact_mod_cast hD y)
  have hz : Integrable (fun z : Fin (n+1) → ℝ => z i) ν :=
    integrable_comp_eval (μ := fun _ : Fin (n+1) => gaussianReal 0 1) (i := i) (f := fun z : ℝ => z)
      ((memLp_id_gaussianReal' 1 (by norm_num)).integrable (by norm_num))
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := ν) (s := univ)
    (bound := fun z => |z i| * (C:ℝ)) (F' := fun y z => z i • D (y+Real.sqrt t • z)) univ_mem
  · exact Eventually.of_forall fun y => ((continuous_apply i).mul (hfc.comp (by fun_prop))).aestronglyMeasurable
  · exact gaussian_lipschitz_coordinate_integrable n i f C hl x t
  · exact ((continuous_apply i).smul (hDc.comp (by fun_prop))).aestronglyMeasurable
  · exact ae_of_all _ fun z y _ => by
      rw [norm_smul,Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (hD _) (abs_nonneg _)
  · exact hz.norm.mul_const C
  · exact ae_of_all _ fun z y _ => by
      have hh := ((hd (y+Real.sqrt t • z)).comp y ((hasFDerivAt_id y).add_const (Real.sqrt t • z))).const_mul (z i)
      simpa only [ContinuousLinearMap.comp_id,Function.comp_def,id_eq] using hh

/-- Gaussian integration by parts represents the averaged gradient by
z_i f, even when f is unbounded. This avoids any Hessian bound. -/
theorem gaussian_gradient_coordinate_moment
    (n : ℕ) (i : Fin (n+1)) (f : (Fin (n+1) → ℝ) → ℝ)
    (D : (Fin (n+1) → ℝ) → (Fin (n+1) → ℝ) →L[ℝ] ℝ)
    (hd : ∀ x,HasFDerivAt f (D x) x) (hDc : Continuous D)
    (C : ℝ≥0) (hD : ∀ x,‖D x‖≤C) (x : Fin (n+1) → ℝ) (t : ℝ) (ht : 0<t) :
    (∫ z,D (x+Real.sqrt t • z) (Pi.single i 1) ∂Measure.pi (fun _ : Fin (n+1) => gaussianReal 0 1))=
      (∫ z,z i*f (x+Real.sqrt t • z) ∂Measure.pi (fun _ : Fin (n+1) => gaussianReal 0 1))/Real.sqrt t := by
  let ν := Measure.pi (fun _ : Fin (n+1) => gaussianReal 0 1)
  have hfc : Continuous f := continuous_iff_continuousAt.mpr (fun y => (hd y).continuousAt)
  have hl : LipschitzWith C f := lipschitzWith_of_nnnorm_fderiv_le
    (fun y => (hd y).differentiableAt) (fun y => by rw [(hd y).fderiv];exact_mod_cast hD y)
  have hi : MemLp (fun z : Fin (n+1) → ℝ => z) 2 ν := finite_gaussian_all_moments 2 (by norm_num)
  have hfi := (lipschitz_affine_average_memLp_two ν hi f C hl x (Real.sqrt t)).integrable (by norm_num)
  have hm : Measurable (fun z => Real.sqrt t*D (x+Real.sqrt t • z) (Pi.single i 1)) :=
    ((((hDc.comp (by fun_prop)).clm_apply continuous_const).const_mul _).measurable)
  have hdi : Integrable (fun z => Real.sqrt t*D (x+Real.sqrt t • z) (Pi.single i 1)) ν := by
    apply Integrable.of_bound hm.aestronglyMeasurable (Real.sqrt t*C)
    exact ae_of_all _ fun z => by
      rw [norm_mul,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _)]
      apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
      calc
        _ ≤ ‖D (x+Real.sqrt t • z)‖*‖(Pi.single i 1 : Fin (n+1) → ℝ)‖ := ContinuousLinearMap.le_opNorm _ _
        _ ≤ C := by simpa [Pi.norm_single] using hD _
  have hder (v : Fin n → ℝ) (y : ℝ) :
      HasDerivAt (fun u => f (x+Real.sqrt t • i.insertNth u v))
        (Real.sqrt t*D (x+Real.sqrt t • i.insertNth y v) (Pi.single i 1)) y := by
    have hh := (hd _).comp_hasDerivAt y (((insertNth_hasDerivAt n i v y).const_smul (Real.sqrt t)).const_add x)
    simpa only [map_smul,smul_eq_mul,Function.comp_def,Pi.smul_apply] using hh
  have hh := gaussian_product_coordinate_ibp_integrable n i _ _ (hfc.comp (by fun_prop)).measurable hm
    hfi hdi (gaussian_lipschitz_coordinate_integrable n i f C hl x t) hder
  rw [integral_const_mul] at hh
  apply (eq_div_iff (Real.sqrt_pos.mpr ht).ne').mpr
  simpa only [mul_comm,Function.comp_def] using hh

end Asakura.Chapter5
