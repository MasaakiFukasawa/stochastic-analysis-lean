import FullAuditBVClamp
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

open MeasureTheory Set
namespace Asakura.Chapter4
open Asakura.FullAudit

/-- The Stieltjes measure of stopped clock time is exactly Lebesgue
measure on the time interval. This identifies the actual energy measure
used by the Chapter 2 integral construction, not just its interval masses. -/
theorem clock_stieltjes_measure (a b : ℝ) (hab : a ≤ b) :
    (intervalStieltjes a b hab id (monotone_id.monotoneOn _)
      (fun _ _ => continuous_id.continuousWithinAt)).measure =
      volume.restrict (Ioc a b) := by
  letI := intervalStieltjes_finite a b hab id (monotone_id.monotoneOn _)
    (fun _ _ => continuous_id.continuousWithinAt)
  apply Measure.ext_of_Ioc
  intro s t hst
  rw [StieltjesFunction.measure_Ioc, Measure.restrict_apply measurableSet_Ioc,
    Ioc_inter_Ioc, Real.volume_Ioc]
  change ENNReal.ofReal (max a (min b t) - max a (min b s)) =
    ENNReal.ofReal (min t b - max s a)
  by_cases hs : s < a
  · by_cases ht : t < a
    · rw [max_eq_left (by grind), max_eq_left (by grind)]
      simp only [sub_self, ENNReal.ofReal_zero]
      symm
      apply ENNReal.ofReal_eq_zero.mpr
      have : min t b ≤ t := min_le_left _ _
      have : a ≤ max s a := le_max_right _ _
      linarith
    · rw [max_eq_right (by grind), max_eq_left (by grind), max_eq_right hs.le]
      rw [min_comm]
  · by_cases hs' : b ≤ s
    · rw [min_eq_left hs', min_eq_left (by grind), max_eq_right hab, sub_self]
      simp only [ENNReal.ofReal_zero]
      symm
      apply ENNReal.ofReal_eq_zero.mpr
      have := min_le_right t b
      have := le_max_left s a
      linarith
    · have hsa : a ≤ s := le_of_not_gt hs
      have hsb : s ≤ b := (lt_of_not_ge hs').le
      have hta : a ≤ min b t := le_min hab (hsa.trans hst.le)
      rw [show min b s = s from min_eq_right hsb,
        show max a s = s from max_eq_right hsa,
        show max a (min b t) = min b t from max_eq_right hta,
        show max s a = s from max_eq_left hsa, min_comm b t]

/-- Brownian quadratic-variation energy is the usual time integral. -/
theorem clock_stieltjes_integral (a b : ℝ) (hab : a ≤ b) (f : ℝ → ℝ) :
    (∫ r, f r ∂(intervalStieltjes a b hab id (monotone_id.monotoneOn _)
      (fun _ _ => continuous_id.continuousWithinAt)).measure) = ∫ r in a..b, f r := by
  rw [clock_stieltjes_measure, intervalIntegral.integral_of_le hab]

end Asakura.Chapter4
