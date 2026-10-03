import Chapter12BrownianDirectionContinuity
import Chapter12PrefixTerminalPairing

open MeasureTheory Set
open scoped RealInnerProductSpace
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

/-- The actual time directions constructed from Brownian interval
indicators meet all deterministic hypotheses of the Asian Greek theorems. -/
theorem brownian_coordinate_direction_properties (d : ℕ) (T : ℝ) (hT : 0 ≤ T) (i : Fin (d+1)) :
    Continuous (fun t : Icc (0:ℝ) T => brownianTimeDirection (i,t)) ∧
    (∀ t : Icc (0:ℝ) T, ‖brownianTimeDirection (i,t)‖ ≤ Real.sqrt T) ∧
    (∀ t : Icc (0:ℝ) T, inner ℝ (brownianTimeDirection (i,t))
      (brownianTimeDirection (i,⟨T,hT,le_rfl⟩)) = t.val) := by
  refine ⟨(brownian_time_direction_continuous d T).comp (continuous_const.prodMk continuous_id),
    fun t => brownian_time_direction_norm_le (i,t),fun t => ?_⟩
  let J := singleCoordinateIsometry
    (H := Lp ℝ 2 ((volume.restrict (Ioi (0:ℝ))).restrict (Iic T))) i
  change inner ℝ (J (finiteTimeIntervalVector T 0 t.val)) (J (finiteTimeIntervalVector T 0 T)) = _
  rw [J.inner_map_map]
  exact finite_prefix_terminal_inner T t.val t.property.1 t.property.2

end Asakura.Chapter12
