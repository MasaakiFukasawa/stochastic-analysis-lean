import Chapter12DerivativeGrowthBilinear
import Chapter12LinearCylinder
import Mathlib.Analysis.InnerProductSpace.Calculus

open scoped ContDiff
namespace Asakura.Chapter12
set_option maxHeartbeats 2000000

theorem hilbert_norm_square_growth (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (k:ℕ) : ∃C:ℝ,0≤C ∧ ∃a:ℕ,∀x:H,
      ‖iteratedFDeriv ℝ k (fun y:H => ‖y‖^2) x‖≤C*(1+‖x‖)^a := by
  have h := iterated_polynomial_growth_bilinear (innerSL ℝ (E:=H))
    (fun x:H => x) (fun x:H => x) contDiff_id contDiff_id
    (linear_map_all_derivatives_growth (ContinuousLinearMap.id ℝ H))
    (linear_map_all_derivatives_growth (ContinuousLinearMap.id ℝ H)) k
  have he : (fun y:H => innerSL ℝ y y)=(fun y:H => ‖y‖^2) := by
    funext y
    exact real_inner_self_eq_norm_sq y
  rw [he] at h
  exact h
end Asakura.Chapter12
#print axioms Asakura.Chapter12.hilbert_norm_square_growth
