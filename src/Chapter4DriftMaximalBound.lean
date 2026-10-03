import Chapter2CumulativeBound
import Chapter4BrownianTimeMeasure
import Mathlib.Topology.ContinuousMap.Compact

open MeasureTheory Set
open scoped ENNReal
namespace Asakura.Chapter4
open Asakura.Chapter2Complete

/-- Cauchy--Schwarz uniformly over all terminal times, for the actual
indefinite time integral. The norm is the continuous-path supremum norm. -/
theorem drift_path_square_bound (T : ℝ) (hT : 0 ≤ T)
    (g : ℝ → ℝ) (hg : MemLp g 2 (volume.restrict (Ioc 0 T)))
    (D : C(Icc (0:ℝ) T, ℝ))
    (hD : ∀ t, D t = ∫ r in 0..t.val, g r) :
    ‖D‖^2 ≤ T * ∫ r in 0..T, g r^2 := by
  let μ := volume.restrict (Ioc (0:ℝ) T)
  have hm : μ.real univ = T := by
    simp only [μ, measureReal_def, Measure.restrict_apply_univ, Real.volume_Ioc,
      sub_zero, ENNReal.toReal_ofReal hT]
  have he (t : Icc (0:ℝ) T) :
      (∫ r in Ioc 0 t.val, g r ∂μ) = ∫ r in 0..t.val, g r := by
    rw [intervalIntegral.integral_of_le t.property.1]
    congr 1
    rw [Measure.restrict_restrict measurableSet_Ioc]
    congr 1
    exact inter_eq_left.mpr (Ioc_subset_Ioc_right t.property.2)
  have hsq (t : Icc (0:ℝ) T) : ‖D t‖^2 ≤ T * ∫ r in 0..T, g r^2 := by
    have h := cumulative_integral_square_bound μ g hg (Ioc 0 t.val)
    rw [hm,he t,← hD t] at h
    simpa only [intervalIntegral.integral_of_le hT,μ] using h
  have hC : 0 ≤ T * ∫ r in 0..T, g r^2 := by
    apply mul_nonneg hT
    rw [intervalIntegral.integral_of_le hT]
    exact integral_nonneg (fun r => sq_nonneg _)
  have hn : ‖D‖ ≤ Real.sqrt (T * ∫ r in 0..T, g r^2) := by
    apply (ContinuousMap.norm_le D (Real.sqrt_nonneg _)).2
    intro t
    nlinarith [hsq t,Real.sq_sqrt hC,norm_nonneg (D t),Real.sqrt_nonneg (T * ∫ r in 0..T, g r^2)]
  nlinarith [Real.sq_sqrt hC,norm_nonneg D,Real.sqrt_nonneg (T * ∫ r in 0..T, g r^2)]

end Asakura.Chapter4
