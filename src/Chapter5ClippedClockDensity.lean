import Chapter5ClockSemimartingale

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter5
set_option maxHeartbeats 1600000

/-- Using the open cutoff makes the covariance density vanish at the
past observation time itself; endpoint choices do not affect the integral. -/
theorem clipped_clock_density_integral
    (a r : ℝ) (ha : 0≤a) (hr : 0≤r) :
    (∫ s in 0..r,(Iio a).indicator (fun _ => (1:ℝ)) s) = min a r := by
  rw [intervalIntegral.integral_of_le hr,integral_indicator measurableSet_Iio,
    Measure.restrict_restrict measurableSet_Iio]
  by_cases h : a≤r
  · have he : Iio a ∩ Ioc (0:ℝ) r = Ioo 0 a := by
      ext s
      simp only [mem_inter_iff,mem_Iio,mem_Ioc,mem_Ioo]
      constructor
      · rintro ⟨hsa,hs0,_⟩; exact ⟨hs0,hsa⟩
      · rintro ⟨hs0,hsa⟩; exact ⟨hsa,hs0,hsa.le.trans h⟩
    rw [he,min_eq_left h]
    simp [Real.volume_real_Ioo_of_le ha]
  · have he : Iio a ∩ Ioc (0:ℝ) r = Ioc 0 r := by
      ext s
      simp only [mem_inter_iff,mem_Iio,mem_Ioc]
      constructor
      · exact fun hs => hs.2
      · intro hs; exact ⟨hs.2.trans_lt (lt_of_not_ge h),hs⟩
    rw [he,min_eq_right (le_of_not_ge h)]
    simp [Real.volume_real_Ioc_of_le hr]

theorem clipped_clock_density_integrable (a b : ℝ) :
    IntervalIntegrable (fun s => (Iio a).indicator (fun _ => (1:ℝ)) s) volume 0 b := by
  constructor <;> exact (integrable_const (1:ℝ)).indicator measurableSet_Iio

open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete

theorem clipped_clock_time_density
    {T : EReal} [Fact (0 ≤ T)] (R : ℝ) (hR : 0≤R)
    (r : ℝ) (hr : 0≤r) (hrT : (r:EReal)<T) :
    (finitePrefixTime (T := T) R hR (realTimeClamp r)).val =
      ∫ s in 0..r,(Iio R).indicator (fun _ => (1:ℝ)) s := by
  rw [clipped_clock_density_integral R r hR hr]
  change (min (realTimeClamp r:EReal) (R:EReal)).toReal=min R r
  rw [real_time_clamp_eq r hr hrT.le]
  by_cases h : R≤r
  · rw [min_eq_right (EReal.coe_le_coe h),EReal.toReal_coe,min_eq_left h]
  · rw [min_eq_left (EReal.coe_le_coe (le_of_not_ge h)),EReal.toReal_coe,min_eq_right (le_of_not_ge h)]

end Asakura.Chapter5
