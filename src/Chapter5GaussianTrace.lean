import Chapter5GaussianGradientIBP
import Chapter5HeatTimeDerivative
import Chapter5HeatC2Preservation
import Mathlib.Algebra.BigOperators.Pi

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal BigOperators
namespace Asakura.Chapter5
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

theorem linear_form_coordinate_sum (d : ℕ) (L : (Fin d → ℝ) →L[ℝ] ℝ) (z : Fin d → ℝ) :
    L z = ∑ i, z i * L (Pi.single i 1) := by
  conv_lhs => rw [pi_eq_sum_univ' z]
  simp only [map_sum,map_smul,smul_eq_mul]

/-- The trace identity is derived from Gaussian integration by parts,
not introduced as a heat-equation hypothesis. -/
theorem gaussian_gradient_trace
    (n : ℕ)
    (D : (Fin (n+1) → ℝ) → (Fin (n+1) → ℝ) →L[ℝ] ℝ)
    (DD : (Fin (n+1) → ℝ) → (Fin (n+1) → ℝ) →L[ℝ] (Fin (n+1) → ℝ) →L[ℝ] ℝ)
    (hd : ∀ x,HasFDerivAt D (DD x) x) (hDc : Continuous D) (hDDc : Continuous DD)
    (C K : ℝ) (hD : ∀ x,‖D x‖ ≤ C) (hDD : ∀ x,‖DD x‖ ≤ K)
    (x : Fin (n+1) → ℝ) (t : ℝ) :
    (∫ z,D (x+Real.sqrt t • z) z ∂Measure.pi (fun _ : Fin (n+1) => gaussianReal 0 1)) =
      Real.sqrt t * ∑ i, (∫ z,DD (x+Real.sqrt t • z) (Pi.single i 1) (Pi.single i 1)
        ∂Measure.pi (fun _ : Fin (n+1) => gaussianReal 0 1)) := by
  let ν := Measure.pi (fun _ : Fin (n+1) => gaussianReal 0 1)
  have hi (i : Fin (n+1)) : Integrable (fun z => z i * D (x+Real.sqrt t • z) (Pi.single i 1)) ν := by
    have hz : Integrable (fun z : Fin (n+1) → ℝ => z i) ν :=
      integrable_comp_eval (μ := fun _ : Fin (n+1) => gaussianReal 0 1) (i := i) (f := fun z : ℝ => z)
        ((memLp_id_gaussianReal' 1 (by norm_num)).integrable (by norm_num))
    apply (hz.norm.mul_const C).mono' (((continuous_apply i).mul
      ((hDc.comp (by fun_prop)).clm_apply continuous_const)).aestronglyMeasurable)
    apply ae_of_all
    intro z
    change ‖z i * D (x+Real.sqrt t • z) (Pi.single i 1)‖ ≤ ‖z i‖ * C
    rw [norm_mul]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    calc
      _ ≤ ‖D (x+Real.sqrt t • z)‖ * ‖(Pi.single i 1 : Fin (n+1) → ℝ)‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ C := by simpa [Pi.norm_single] using hD (x+Real.sqrt t • z)
  calc
    _ = ∫ z, ∑ i, z i * D (x+Real.sqrt t • z) (Pi.single i 1) ∂ν := by
      apply integral_congr_ae
      exact ae_of_all _ fun z => linear_form_coordinate_sum (n+1) _ z
    _ = _ := by
      rw [integral_finsetSum _ (fun i _ => hi i)]
      dsimp only [ν]
      simp_rw [gaussian_gradient_coordinate_ibp n _ D DD hd hDc hDDc C K hD hDD x t]
      rw [Finset.mul_sum]

end Asakura.Chapter5
