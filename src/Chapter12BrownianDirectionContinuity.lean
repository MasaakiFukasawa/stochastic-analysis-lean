import Chapter12TimeDirectionContinuity
import Chapter12BrownianCylinderDensity

open MeasureTheory Set
open scoped ENNReal
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

theorem brownian_time_direction_continuous (d : ℕ) (T : ℝ) :
    Continuous (brownianTimeDirection : BrownianTimeCoordinates d T → FiniteWienerHilbert d T) := by
  apply continuous_prod_of_discrete_left.mpr
  intro i
  have hi : Isometry (fun f : Lp ℝ 2 ((volume.restrict (Ioi (0:ℝ))).restrict (Iic T)) =>
      (WithLp.toLp 2 (Pi.single i f) : FiniteWienerHilbert d T)) := by
    apply isometry_iff_dist_eq.mpr
    intro f g
    exact PiLp.dist_single_same 2
      (fun _ : Fin (d+1) => Lp ℝ 2 ((volume.restrict (Ioi (0:ℝ))).restrict (Iic T))) i f g
  change Continuous (fun t : Icc (0:ℝ) T =>
    (WithLp.toLp 2 (Pi.single i (finiteTimeIntervalVector T 0 t.val)) : FiniteWienerHilbert d T))
  exact hi.continuous.comp (finite_time_prefix_continuous T)

theorem brownian_time_direction_norm {d : ℕ} {T : ℝ}
    (z : BrownianTimeCoordinates d T) :
    ‖brownianTimeDirection z‖ = Real.sqrt z.2.val := by
  unfold brownianTimeDirection
  rw [show ‖(WithLp.toLp 2 (Pi.single z.1 (finiteTimeIntervalVector T 0 z.2.val)) :
      FiniteWienerHilbert d T)‖ = ‖finiteTimeIntervalVector T 0 z.2.val‖ from
    PiLp.norm_single 2 (fun _ : Fin (d+1) => Lp ℝ 2 ((volume.restrict (Ioi (0:ℝ))).restrict (Iic T)))
      z.1 (finiteTimeIntervalVector T 0 z.2.val)]
  simpa using finite_time_interval_norm T 0 z.2.val (le_refl 0) z.2.property.1 z.2.property.2

theorem brownian_time_direction_norm_le {d : ℕ} {T : ℝ}
    (z : BrownianTimeCoordinates d T) :
    ‖brownianTimeDirection z‖ ≤ Real.sqrt T := by
  rw [brownian_time_direction_norm]
  exact Real.sqrt_le_sqrt z.2.property.2

end Asakura.Chapter12
