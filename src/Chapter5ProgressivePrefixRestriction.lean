import Chapter2ProgressiveEnergySpace

open MeasureTheory Set
namespace Asakura.Chapter5
open Asakura.Chapter2Complete
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

/-- Progressiveness on an exhaustion supplies progressiveness on every
smaller real-time prefix, with no continuity assumption on the integrand. -/
theorem progressive_real_prefix_restriction
    {Ω : Type*} (F : ℝ → MeasurableSpace Ω) (H : Ω × ℝ → ℝ)
    (R b : ℝ) (hRb : R≤b)
    (hH : @Measurable _ _ (progressiveSpace (fun t : Icc (0:ℝ) b => F t.val)) inferInstance
      (fun z : Ω × Icc (0:ℝ) b => H (z.1,z.2.val))) :
    @Measurable _ _ (progressiveSpace (fun t : Icc (0:ℝ) R => F t.val)) inferInstance
      (fun z : Ω × Icc (0:ℝ) R => H (z.1,z.2.val)) := by
  apply (measurable_progressive_iff _ _).mpr
  intro t
  let u : Icc (0:ℝ) b := ⟨t.val,t.property.1,t.property.2.trans hRb⟩
  let q : Iic t → Iic u := fun s => ⟨⟨s.val.val,s.val.property.1,s.val.property.2.trans hRb⟩,s.property⟩
  have hq : Measurable q := ((measurable_subtype_coe.comp measurable_subtype_coe).subtype_mk).subtype_mk
  let : MeasurableSpace Ω := F t.val
  exact ((measurable_progressive_iff _ _).mp hH u).comp (measurable_fst.prodMk (hq.comp measurable_snd))

end Asakura.Chapter5
