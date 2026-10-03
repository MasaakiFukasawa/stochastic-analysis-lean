import Chapter4IntervalPowerEstimate
import Chapter4DriftMaximalBound

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter4
set_option maxHeartbeats 1500000

/-- The drift supremum estimate for arbitrary real p≥1, with merely
measurable coefficients and the actual indefinite integral. -/
theorem drift_path_power_bound (T : ℝ) (hT : 0≤T)
    (g : ℝ → ℝ) (p : ℝ) (hp : 1≤p)
    (hi : IntervalIntegrable (fun r => |g r|^p) volume 0 T)
    (D : C(Icc (0:ℝ) T,ℝ)) (hD : ∀ t,D t=∫ r in 0..t.val,g r) :
    ‖D‖^p≤T^(p-1)*(∫ r in 0..T,|g r|^p) := by
  let μ := volume.restrict (Ioc (0:ℝ) T)
  obtain ⟨hiabs,hb⟩ := interval_integral_power_holder T hT (fun r => |g r|) (fun _ => abs_nonneg _) p hp hi
  have hn : ‖D‖≤∫ r in 0..T,|g r| := by
    apply (ContinuousMap.norm_le _ (intervalIntegral.integral_nonneg_of_forall hT (fun _ => abs_nonneg _))).2
    intro t
    have he : (∫ r in Ioc 0 t.val,g r ∂μ)=∫ r in 0..t.val,g r := by
      rw [intervalIntegral.integral_of_le t.property.1]
      dsimp only [μ]
      rw [Measure.restrict_restrict measurableSet_Ioc,inter_eq_left.mpr (Ioc_subset_Ioc_right t.property.2)]
    rw [hD t,← he]
    have hh := norm_integral_le_integral_norm (f := g) (μ := μ.restrict (Ioc 0 t.val))
    have hu := setIntegral_le_integral (μ := μ) (s := Ioc 0 t.val) hiabs.1
      (.of_forall (fun r => abs_nonneg (g r)))
    simpa only [Real.norm_eq_abs,intervalIntegral.integral_of_le hT,μ] using hh.trans hu
  exact (Real.rpow_le_rpow (norm_nonneg _) hn (zero_le_one.trans hp)).trans hb

end Asakura.Chapter4
