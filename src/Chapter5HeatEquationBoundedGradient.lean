import Chapter5HeatSecondCoordinate

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal BigOperators
namespace Asakura.Chapter5
open Asakura.FullAudit
set_option maxHeartbeats 4200000
set_option backward.isDefEq.respectTransparency false

/-- The heat equation under the exercise's actual hypothesis: a
continuous bounded first derivative. The second coordinate derivatives
are computed from Gaussian moments, without assuming a bounded Hessian. -/
theorem gaussian_heat_equation_bounded_gradient
    (n : ℕ) (f : (Fin (n+1) → ℝ) → ℝ)
    (D : (Fin (n+1) → ℝ) → (Fin (n+1) → ℝ) →L[ℝ] ℝ)
    (hd : ∀ x,HasFDerivAt f (D x) x) (hDc : Continuous D)
    (C : ℝ≥0) (hD : ∀ x,‖D x‖≤C) (x : Fin (n+1) → ℝ) (t : ℝ) (ht : 0<t) :
    let A := fun s y => ∫ z,f (y+Real.sqrt s • z) ∂Measure.pi (fun _ : Fin (n+1) => gaussianReal 0 1)
    HasDerivAt (fun s => A s x)
      ((1/2:ℝ)*∑ i,deriv (fun r : ℝ => fderiv ℝ (A t) (x+r • Pi.single i 1) (Pi.single i 1)) 0) t := by
  dsimp only
  let ν := Measure.pi (fun _ : Fin (n+1) => gaussianReal 0 1)
  have hl : LipschitzWith C f := lipschitzWith_of_nnnorm_fderiv_le
    (fun y => (hd y).differentiableAt) (fun y => by rw [(hd y).fderiv];exact_mod_cast hD y)
  have hfi := (lipschitz_affine_average_memLp_two ν (finite_gaussian_all_moments 2 (by norm_num)) f C hl x (Real.sqrt t)).integrable (by norm_num)
  have htime := vector_average_time_derivative_of_integrable ν (gaussian_product_first_moment (n+1)) f D hd hDc C hD x t ht hfi
  have hi (i : Fin (n+1)) : Integrable (fun z => z i*D (x+Real.sqrt t • z) (Pi.single i 1)) ν := by
    have hz : Integrable (fun z : Fin (n+1) → ℝ => z i) ν :=
      integrable_comp_eval (μ := fun _ : Fin (n+1) => gaussianReal 0 1) (i := i) (f := fun z : ℝ => z)
        ((memLp_id_gaussianReal' 1 (by norm_num)).integrable (by norm_num))
    apply (hz.norm.mul_const C).mono' (((continuous_apply i).mul
      ((hDc.comp (by fun_prop)).clm_apply continuous_const)).aestronglyMeasurable)
    exact ae_of_all _ fun z => by
      change ‖z i*D (x+Real.sqrt t • z) (Pi.single i 1)‖≤‖z i‖ * (C:ℝ)
      rw [norm_mul,Real.norm_eq_abs]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      calc
        _ ≤ ‖D (x+Real.sqrt t • z)‖*‖(Pi.single i 1 : Fin (n+1) → ℝ)‖ := ContinuousLinearMap.le_opNorm _ _
        _ ≤ C := by simpa [Pi.norm_single] using hD _
  have hsum : (∫ z,D (x+Real.sqrt t • z) z ∂ν)=
      ∑ i,∫ z,z i*D (x+Real.sqrt t • z) (Pi.single i 1) ∂ν := by
    calc
      _ = ∫ z,∑ i,z i*D (x+Real.sqrt t • z) (Pi.single i 1) ∂ν :=
        integral_congr_ae (ae_of_all _ fun z => linear_form_coordinate_sum (n+1) _ z)
      _ = _ := integral_finsetSum _ (fun i _ => hi i)
  have hsecs i := (gaussian_average_second_coordinate n i f D hd hDc C hD x t ht).deriv
  convert htime using 1
  simp_rw [hsecs]
  rw [integral_div,hsum,← Finset.sum_div]
  ring

end Asakura.Chapter5
