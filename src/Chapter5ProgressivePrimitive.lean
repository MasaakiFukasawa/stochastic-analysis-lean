import Chapter2CumulativeAdapted
import Chapter5FiniteTimeEnergy

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter5
open Asakura.FullAudit Asakura.Chapter2Complete
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

/-- The ordinary time primitive of a progressive driver is adapted.
This supplies the adaptedness of M_t minus the driver primitive in the
frozen BSDE construction. -/
theorem progressive_time_primitive_adapted
    {Ω : Type*} (R : ℝ) (hR : 0 ≤ R)
    (F : Icc (0:ℝ) R → MeasurableSpace Ω)
    (H : Ω × ℝ → ℝ)
    (hH : @Measurable _ _ (progressiveSpace F) inferInstance
      (fun z : Ω × Icc (0:ℝ) R => H (z.1,z.2.val)))
    (t : Icc (0:ℝ) R) :
    @Measurable _ _ (F t) inferInstance (fun w => ∫ r in 0..t.val,H (w,r)) := by
  letI : MeasurableSpace Ω := F t
  have hp := progressive_clamped_measurable 0 R hR F
    (fun z : Ω × Icc (0:ℝ) R => H (z.1,z.2.val)) hH t
  have hi := hp.stronglyMeasurable.integral_prod_right' (ν := volume.restrict (Ioc 0 t.val))
  have he w : (∫ r in Ioc 0 t.val,H (w,(projIcc 0 R hR (intervalClamp 0 t.val t.property.1 r)).val)) =
      ∫ r in 0..t.val,H (w,r) := by
    rw [intervalIntegral.integral_of_le t.property.1]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    rw [intervalClamp_eq 0 t.val t.property.1 ⟨hr.1.le,hr.2⟩,
      projIcc_of_mem hR ⟨hr.1.le,hr.2.trans t.property.2⟩]
  simpa only [he] using hi.measurable

/-- Almost every primitive is continuous, including both endpoints. -/
theorem progressive_time_primitive_continuous
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (R : ℝ) (hR : 0 ≤ R) (H : Ω × ℝ → ℝ)
    (hi : ∀ᵐ w ∂P,IntervalIntegrable (fun r => H (w,r)) volume 0 R) :
    ∀ᵐ w ∂P,ContinuousOn (fun t => ∫ r in 0..t,H (w,r)) (Icc 0 R) := by
  filter_upwards [hi] with w hw
  simpa only [uIcc_of_le hR] using intervalIntegral.continuousOn_primitive_interval' hw left_mem_uIcc

end Asakura.Chapter5
