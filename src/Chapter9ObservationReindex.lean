import Chapter9FiniteObservationExtension

open MeasureTheory
namespace Asakura.Chapter9
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

/-- Reindexing the same collection of observations leaves its sigma algebra unchanged. -/
theorem observation_information_congr {Ω E ι κ : Type*} [MeasurableSpace E]
    (X : ι → Ω → E) (Y : κ → Ω → E)
    (hXY : ∀ i,∃ j,X i=Y j) (hYX : ∀ j,∃ i,Y j=X i) :
    MeasurableSpace.comap (fun w i => X i w) MeasurableSpace.pi=
      MeasurableSpace.comap (fun w j => Y j w) MeasurableSpace.pi := by
  apply le_antisymm
  · letI : MeasurableSpace Ω := MeasurableSpace.comap (fun w j => Y j w) MeasurableSpace.pi
    have hm : Measurable[MeasurableSpace.comap (fun w j => Y j w) MeasurableSpace.pi] (fun w i => X i w) := by
      apply Measurable.of_eval
      intro i
      obtain ⟨j,hj⟩ := hXY i
      rw [hj]
      exact (measurable_pi_apply j).comp (comap_measurable (fun w j => Y j w))
    exact hm.comap_le
  · letI : MeasurableSpace Ω := MeasurableSpace.comap (fun w i => X i w) MeasurableSpace.pi
    have hm : Measurable[MeasurableSpace.comap (fun w i => X i w) MeasurableSpace.pi] (fun w j => Y j w) := by
      apply Measurable.of_eval
      intro j
      obtain ⟨i,hi⟩ := hYX j
      rw [hi]
      exact (measurable_pi_apply i).comp (comap_measurable (fun w i => X i w))
    exact hm.comap_le
end Asakura.Chapter9
