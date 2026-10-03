import Chapter12TimeDirectionContinuity

open MeasureTheory Set
open scoped ENNReal
namespace Asakura.Chapter12
set_option maxHeartbeats 1200000

/-- The linear interpolation kernel converges in the deterministic time
Hilbert space uniformly on each mesh cell, with error at most sqrt(mesh). -/
theorem interpolation_kernel_error (T : ℝ) (a t b : Icc (0:ℝ) T)
    (hat : a.val ≤ t.val) (htb : t.val ≤ b.val) (α : ℝ) (hα : 0 ≤ α) (hα1 : α ≤ 1) :
    ‖(1-α) • finiteTimeIntervalVector T 0 a.val + α • finiteTimeIntervalVector T 0 b.val -
      finiteTimeIntervalVector T 0 t.val‖ ≤ Real.sqrt (b.val-a.val) := by
  let f := fun s : Icc (0:ℝ) T => finiteTimeIntervalVector T 0 s.val
  have h1 : ‖f a-f t‖ ≤ Real.sqrt (b.val-a.val) := by
    rw [← dist_eq_norm,finite_time_prefix_dist,Real.dist_eq,abs_sub_comm,
      abs_of_nonneg (sub_nonneg.mpr hat)]
    exact Real.sqrt_le_sqrt (sub_le_sub_right htb _)
  have h2 : ‖f b-f t‖ ≤ Real.sqrt (b.val-a.val) := by
    rw [← dist_eq_norm,finite_time_prefix_dist,Real.dist_eq,
      abs_of_nonneg (sub_nonneg.mpr htb)]
    exact Real.sqrt_le_sqrt (sub_le_sub_left hat _)
  change ‖(1-α) • f a + α • f b - f t‖ ≤ _
  have he : (1-α) • f a + α • f b - f t = (1-α) • (f a-f t) + α • (f b-f t) := by module
  rw [he]
  calc
    _ ≤ ‖(1-α) • (f a-f t)‖ + ‖α • (f b-f t)‖ := norm_add_le _ _
    _ = (1-α)*‖f a-f t‖ + α*‖f b-f t‖ := by
      simp only [norm_smul,Real.norm_eq_abs,abs_of_nonneg hα,abs_of_nonneg (sub_nonneg.mpr hα1)]
    _ ≤ (1-α)*Real.sqrt (b.val-a.val) + α*Real.sqrt (b.val-a.val) :=
      add_le_add (mul_le_mul_of_nonneg_left h1 (sub_nonneg.mpr hα1))
        (mul_le_mul_of_nonneg_left h2 hα)
    _ = _ := by ring

theorem interpolation_kernel_norm (T : ℝ) (a b : Icc (0:ℝ) T)
    (α : ℝ) (hα : 0 ≤ α) (hα1 : α ≤ 1) :
    ‖(1-α) • finiteTimeIntervalVector T 0 a.val + α • finiteTimeIntervalVector T 0 b.val‖ ≤
      Real.sqrt T := by
  have hb (s : Icc (0:ℝ) T) : ‖finiteTimeIntervalVector T 0 s.val‖ ≤ Real.sqrt T := by
    rw [finite_time_interval_norm T 0 s.val (le_refl 0) s.property.1 s.property.2,sub_zero]
    exact Real.sqrt_le_sqrt s.property.2
  calc
    _ ≤ ‖(1-α) • finiteTimeIntervalVector T 0 a.val‖ + ‖α • finiteTimeIntervalVector T 0 b.val‖ := norm_add_le _ _
    _ = (1-α)*‖finiteTimeIntervalVector T 0 a.val‖ + α*‖finiteTimeIntervalVector T 0 b.val‖ := by
      simp only [norm_smul,Real.norm_eq_abs,abs_of_nonneg hα,abs_of_nonneg (sub_nonneg.mpr hα1)]
    _ ≤ (1-α)*Real.sqrt T + α*Real.sqrt T :=
      add_le_add (mul_le_mul_of_nonneg_left (hb a) (sub_nonneg.mpr hα1))
        (mul_le_mul_of_nonneg_left (hb b) hα)
    _ = _ := by ring

end Asakura.Chapter12
