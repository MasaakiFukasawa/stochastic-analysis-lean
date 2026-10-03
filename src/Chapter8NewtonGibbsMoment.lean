import Chapter8NewtonGibbsMaxwell
import Chapter8NormalizedGibbsMeasure

open MeasureTheory
open scoped BigOperators ENNReal
namespace Asakura.Chapter8
open Asakura.Chapter3Complete
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false

/-- The Gibbs-Maxwell law constructed for the actual Newton SDE belongs
to P2; this supplies the moment hypothesis of the transport argument. -/
theorem newton_gibbs_memLp {d : ℕ}
    (U : (Fin d → ℝ) → ℝ) (hU : Continuous U)
    (β m : ℝ) (hβ : 0<β) (hm : 0<m)
    (hi : Integrable (fun x : Fin d → ℝ => (1+∑ i,x i^2)*Real.exp (-β*U x))) :
    let H := newtonHamiltonian U m
    let π := volume.withDensity (fun x : Fin (d+d) → ℝ =>
      ENNReal.ofReal ((∫ y : Fin (d+d) → ℝ,Real.exp (-β*H y))⁻¹*Real.exp (-β*H x)))
    MemLp (fun x => x) 2 π := by
  have hH : Continuous (newtonHamiltonian U m) := by
    unfold newtonHamiltonian
    exact (hU.comp (positionProjection d).continuous).add
      ((kineticBilinear d m).continuous.clm_apply continuous_id)
  have hh := newton_hamiltonian_integrability U hU β m hβ hm hi
  have hn : Integrable (fun x : Fin (d+d) → ℝ => (1+‖x‖^2)*Real.exp (-β*newtonHamiltonian U m x)) := by
    apply hh.mono' (by fun_prop)
    apply ae_of_all
    intro x
    rw [Real.norm_eq_abs,abs_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_right (add_le_add le_rfl (pi_norm_sq_le_sum_sq x)) (Real.exp_pos _).le
  exact (memLp_two_iff_integrable_sq_norm measurable_id.aestronglyMeasurable).mpr
    (normalized_gibbs_measure (newtonHamiltonian U m) hH β hn).2.2.2.1

end Asakura.Chapter8
