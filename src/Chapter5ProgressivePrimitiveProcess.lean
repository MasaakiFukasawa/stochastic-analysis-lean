import Chapter5ProgressivePrimitive
import Chapter5PrimitiveEnergySpace

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter5
open Asakura.FullAudit Asakura.Chapter2Complete
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false

/-- The whole primitive process is progressive, not merely adapted at
each time. This remains true when path integrability is only almost sure. -/
theorem time_primitive_progressive
    {Ω : Type*} (R : ℝ) (hR : 0 ≤ R)
    (F : Icc (0:ℝ) R → MeasurableSpace Ω)
    (H : Ω × ℝ → ℝ)
    (hH : @Measurable _ _ (progressiveSpace F) inferInstance
      (fun z : Ω × Icc (0:ℝ) R => H (z.1,z.2.val))) :
    @Measurable _ _ (progressiveSpace F) inferInstance
      (fun z : Ω × Icc (0:ℝ) R => ∫ r in 0..z.2.val,H (z.1,r)) := by
  apply (measurable_progressive_iff F _).mpr
  intro t
  let : MeasurableSpace Ω := F t
  let G := fun z : Ω × ℝ => H (z.1,(projIcc 0 R hR (intervalClamp 0 t.val t.property.1 z.2)).val)
  have hG : Measurable G := progressive_clamped_measurable 0 R hR F
    (fun z : Ω × Icc (0:ℝ) R => H (z.1,z.2.val)) hH t
  have hm : Measurable (fun z : Ω × Iic t => (z.1,z.2.val.val)) :=
    measurable_fst.prodMk (measurable_subtype_coe.comp (measurable_subtype_coe.comp measurable_snd))
  have hp := (time_primitive_joint_measurable G hG).comp hm
  convert hp using 1
  funext z
  apply intervalIntegral.integral_congr
  intro r hr
  rw [uIcc_of_le z.2.val.property.1] at hr
  dsimp only [G]
  rw [intervalClamp_eq 0 t.val t.property.1 ⟨hr.1,hr.2.trans z.2.property⟩,
    projIcc_of_mem hR ⟨hr.1,hr.2.trans z.2.val.property.2⟩]

end Asakura.Chapter5
