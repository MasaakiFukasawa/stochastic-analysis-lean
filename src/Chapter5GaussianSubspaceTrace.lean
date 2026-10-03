import Chapter5GaussianSubspaceIBP
import Chapter5GaussianTrace

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal BigOperators
namespace Asakura.Chapter5
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

theorem gaussian_subspace_gradient_trace
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (n : ℕ) (Q : (Fin (n+1) → ℝ) →L[ℝ] E)
    (D : E → E →L[ℝ] ℝ) (DD : E → E →L[ℝ] E →L[ℝ] ℝ)
    (hd : ∀ x,HasFDerivAt D (DD x) x) (hDc : Continuous D) (hDDc : Continuous DD)
    (C K : ℝ) (hD : ∀ x,‖D x‖ ≤ C) (hDD : ∀ x,‖DD x‖ ≤ K)
    (x : E) (t : ℝ) :
    (∫ z,D (x+Real.sqrt t • Q z) (Q z) ∂Measure.pi (fun _ : Fin (n+1) => gaussianReal 0 1)) =
      Real.sqrt t * ∑ i, (∫ z,DD (x+Real.sqrt t • Q z) (Q (Pi.single i 1)) (Q (Pi.single i 1))
        ∂Measure.pi (fun _ : Fin (n+1) => gaussianReal 0 1)) := by
  let ν := Measure.pi (fun _ : Fin (n+1) => gaussianReal 0 1)
  have hC : 0 ≤ C := (norm_nonneg (D x)).trans (hD x)
  have hi (i : Fin (n+1)) : Integrable (fun z => z i * D (x+Real.sqrt t • Q z) (Q (Pi.single i 1))) ν := by
    have hz : Integrable (fun z : Fin (n+1) → ℝ => z i) ν :=
      integrable_comp_eval (μ := fun _ : Fin (n+1) => gaussianReal 0 1) (i := i) (f := fun z : ℝ => z)
        ((memLp_id_gaussianReal' 1 (by norm_num)).integrable (by norm_num))
    apply hz.mul_bdd (g := fun z => D (x+Real.sqrt t • Q z) (Q (Pi.single i 1))) (((hDc.comp (by fun_prop)).clm_apply continuous_const).aestronglyMeasurable)
      (c := C*‖Q‖)
    apply ae_of_all
    intro z
    have hQe : ‖Q (Pi.single i 1)‖ ≤ ‖Q‖ := by simpa [Pi.norm_single] using Q.le_opNorm (Pi.single i 1)
    exact (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul (hD _) hQe (norm_nonneg _) hC)
  calc
    _ = ∫ z, ∑ i, z i * D (x+Real.sqrt t • Q z) (Q (Pi.single i 1)) ∂ν := by
      apply integral_congr_ae
      apply ae_of_all
      intro z
      exact linear_form_coordinate_sum (n+1) ((D (x+Real.sqrt t • Q z)).comp Q) z
    _ = _ := by
      rw [integral_finsetSum _ (fun i _ => hi i)]
      dsimp only [ν]
      simp_rw [gaussian_subspace_coordinate_ibp n _ Q D DD hd hDc hDDc C K hD hDD x t]
      rw [Finset.mul_sum]

end Asakura.Chapter5
