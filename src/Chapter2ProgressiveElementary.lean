import Chapter2ProgressiveSpace

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter2Complete
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false

/-- Bounded-past elementary integrands are progressive, including the
left endpoint of their half-open time interval. -/
theorem progressive_elementary_measurable
    {Ω : Type*} (a b : ℝ) (F : Icc a b → MeasurableSpace Ω) (hF : Monotone F)
    (s t : Icc a b) (Z : Ω → ℝ) (hZ : Measurable[F s] Z) :
    @Measurable _ _ (progressiveSpace F) inferInstance
      (fun p : Ω × Icc a b => (Ico s t).indicator (fun _ => Z p.1) p.2) := by
  apply (measurable_progressive_iff F _).2
  intro u
  letI : MeasurableSpace Ω := F u
  by_cases hsu : s ≤ u
  · have hZu : Measurable Z := hZ.mono (hF hsu) le_rfl
    have htime : Measurable (fun p : Ω × Iic u => p.2.val) :=
      measurable_subtype_coe.comp measurable_snd
    have he : (fun p : Ω × Iic u => (Ico s t).indicator (fun _ => Z p.1) p.2.val) =
        ((fun p : Ω × Iic u => p.2.val) ⁻¹' Ico s t).indicator (fun p => Z p.1) := by
      funext p
      by_cases hp : p.2.val ∈ Ico s t <;> simp [Set.indicator,hp]
    rw [he]
    exact (hZu.comp measurable_fst).indicator (measurableSet_Ico.preimage htime)
  · have he : (fun p : Ω × Iic u => (Ico s t).indicator (fun _ => Z p.1) p.2.val) = 0 := by
      funext p
      have hp : p.2.val ∉ Ico s t := fun h => hsu (h.1.trans p.2.property)
      simp [hp]
    rw [he]
    exact measurable_const

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.progressive_elementary_measurable
