import Chapter6ContinuousItoGridLimit

open MeasureTheory Set Filter Finset
open scoped Topology BigOperators
namespace Asakura.Chapter6
set_option maxHeartbeats 1600000

theorem euclidean_time_energy_bound {d : ℕ} (H : ℝ → Fin d → ℝ)
    (R : ℝ) (hR : 0≤R) (hH : ContinuousOn H (Icc 0 R))
    (K : ℝ) (hK : 0≤K) (hb : ∀ r∈Icc 0 R,‖WithLp.toLp 2 (H r)‖≤K) :
    0≤(∫ r in 0..R,∑ j,H r j^2) ∧ (∫ r in 0..R,∑ j,H r j^2)≤K^2*R := by
  have hi : IntervalIntegrable (fun r => ∑ j,H r j^2) volume 0 R := by
    apply ContinuousOn.intervalIntegrable
    simpa only [uIcc_of_le hR,Pi.pow_apply,Function.comp_def] using continuousOn_finset_sum univ (fun j _ => ((continuous_apply j).continuousOn.comp hH (mapsTo_univ _ _)).pow 2)
  constructor
  · apply intervalIntegral.integral_nonneg_of_forall hR
    exact fun r => sum_nonneg (fun _ _ => sq_nonneg _)
  · have hl : (∫ r in 0..R,∑ j,H r j^2)≤∫ r in 0..R,K^2 := by
      apply intervalIntegral.integral_mono_on hR hi intervalIntegrable_const
      intro r hr
      have hh := hb r hr
      simpa only [EuclideanSpace.real_norm_sq_eq] using pow_le_pow_left₀ (norm_nonneg _) hh 2
    simpa [mul_comm] using hl

end Asakura.Chapter6
