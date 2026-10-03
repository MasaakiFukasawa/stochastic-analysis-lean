import Chapter12FiniteCompactTime
import Chapter2ProgressiveEnergySpace

open MeasureTheory Set
open scoped ENNReal
namespace Asakura.Chapter12
open Asakura.FullAudit Asakura.Chapter2Written Asakura.Chapter2Complete
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

theorem compact_time_restriction_memLp {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] (T : ℝ) (hT : 0 ≤ T)
    (H : Ω × ℝ → ℝ) (hH : MemLp H 2 (P.prod (volume.restrict (Ioi (0:ℝ))))) :
    MemLp (fun z : Ω × Icc (0:ℝ) T => H (z.1,z.2.val)) 2
      (P.prod (compactTimeMeasure T hT)) := by
  have hi := hH.restrict (univ ×ˢ Iic T)
  rw [← Measure.prod_restrict,Measure.restrict_univ] at hi
  exact hi.comp_measurePreserving ((MeasurePreserving.id P).prod (compact_time_val_preserving T hT))

theorem compact_progressive_restriction {Ω : Type*} [MeasurableSpace Ω]
    (F : HalfClosedTime → MeasurableSpace Ω) (c : ℕ → ℝ) (hco : ∀ r,∃ n,r ≤ c n)
    (H : Ω × ℝ → ℝ)
    (hp : ∀ n,@Measurable _ _
      (progressiveSpace (fun t : Icc (0:ℝ) (c n) => F (realTimeClamp t.val))) inferInstance
      (fun z : Ω × Icc (0:ℝ) (c n) => H (z.1,z.2.val))) (T : ℝ) :
    @Measurable _ _ (progressiveSpace (fun t : Icc (0:ℝ) T => F (realTimeClamp t.val))) inferInstance
      (fun z : Ω × Icc (0:ℝ) T => H (z.1,z.2.val)) := by
  obtain ⟨n,hn⟩ := hco T
  apply (measurable_progressive_iff _ _).mpr
  intro u
  let v : Icc (0:ℝ) (c n) := ⟨u.val,u.property.1,u.property.2.trans hn⟩
  let e : Iic u → Iic v := fun s =>
    ⟨⟨s.val.val,s.val.property.1,s.val.property.2.trans hn⟩,s.property⟩
  have he : Measurable e :=
    ((measurable_subtype_coe.comp measurable_subtype_coe).subtype_mk).subtype_mk
  have hv := (measurable_progressive_iff _ _).mp (hp n) v
  exact hv.comp (measurable_fst.prodMk (he.comp measurable_snd))

end Asakura.Chapter12
