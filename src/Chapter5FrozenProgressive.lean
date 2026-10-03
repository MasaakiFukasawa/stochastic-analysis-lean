import Chapter5ProgressivePrimitiveProcess
import Chapter5GeneratorL2

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter5
open Asakura.FullAudit Asakura.Chapter2Complete
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false

/-- The manuscript's joint progressive measurability hypothesis survives
substitution of two progressive input processes. -/
theorem generator_progressive_substitution
    {Ω : Type*} (R : ℝ) (F : Icc (0:ℝ) R → MeasurableSpace Ω)
    (f : Ω → ℝ → ℝ → ℝ → ℝ)
    (hf : ∀ t : Icc (0:ℝ) R,
      @Measurable _ _ ((F t).prod inferInstance) inferInstance
        (fun p : Ω × (Iic t × (ℝ × ℝ)) => f p.1 p.2.1.val.val p.2.2.1 p.2.2.2))
    (Y Z : Ω × ℝ → ℝ)
    (hY : @Measurable _ _ (progressiveSpace F) inferInstance
      (fun z : Ω × Icc (0:ℝ) R => Y (z.1,z.2.val)))
    (hZ : @Measurable _ _ (progressiveSpace F) inferInstance
      (fun z : Ω × Icc (0:ℝ) R => Z (z.1,z.2.val))) :
    @Measurable _ _ (progressiveSpace F) inferInstance
      (fun z : Ω × Icc (0:ℝ) R => f z.1 z.2.val (Y (z.1,z.2.val)) (Z (z.1,z.2.val))) := by
  apply (measurable_progressive_iff F _).mpr
  intro t
  let : MeasurableSpace Ω := F t
  have hy := (measurable_progressive_iff F _).mp hY t
  have hz := (measurable_progressive_iff F _).mp hZ t
  exact (hf t).comp (measurable_fst.prodMk (measurable_snd.prodMk (hy.prodMk hz)))

/-- The explicitly constructed frozen solution stays in the progressive
space on which the contraction argument is carried out. -/
theorem frozen_output_progressive
    {Ω : Type*} (R : ℝ) (hR : 0 ≤ R)
    (F : Icc (0:ℝ) R → MeasurableSpace Ω)
    (M H : Ω × ℝ → ℝ)
    (hM : @Measurable _ _ (progressiveSpace F) inferInstance
      (fun z : Ω × Icc (0:ℝ) R => M (z.1,z.2.val)))
    (hH : @Measurable _ _ (progressiveSpace F) inferInstance
      (fun z : Ω × Icc (0:ℝ) R => H (z.1,z.2.val))) :
    @Measurable _ _ (progressiveSpace F) inferInstance
      (fun z : Ω × Icc (0:ℝ) R => M (z.1,z.2.val)-(∫ r in 0..z.2.val,H (z.1,r))) :=
  hM.sub (time_primitive_progressive R hR F H hH)

end Asakura.Chapter5
