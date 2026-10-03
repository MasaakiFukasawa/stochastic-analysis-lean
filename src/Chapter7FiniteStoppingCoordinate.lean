import Chapter7NaturalBrownianSystem
import Chapter7NullEventTransfer

open MeasureTheory Set Filter
open scoped Topology ENNReal NNReal
namespace Asakura.Chapter7
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 1800000

/-- Passing an almost surely finite extended stopping time to its real
coordinate preserves the stopping property in the completed filtration. -/
theorem finite_stopping_coordinate
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω)
    (F0 : ℝ≥0 → MeasurableSpace Ω) (hF0 : Monotone F0) (hl : ∀ t,F0 t ≤ m)
    (hn : ∀ t N,MeasurableSet[m] N → P N = 0 → MeasurableSet[F0 t] N)
    (τ : Ω → HalfClosedTime)
    (hτ : ∀ t,MeasurableSet[halfClosedFiltration m F0 t] {w | τ w ≤ t})
    (hf : ∀ᵐ w ∂P,τ w < ⊤) :
    ∀ t : ℝ≥0,MeasurableSet[F0 t] {w | halfTimeReal (τ w) ≤ t} := by
  have htm : Measurable[m] τ := by
    have h := stopped_min_measurable (halfClosedFiltration m F0)
      (half_closed_filtration_mono m F0 hF0 hl) τ hτ ⊤
    have heF : halfClosedFiltration m F0 ⊤ = m := by simp [halfClosedFiltration]
    rw [heF] at h
    simpa only [min_top_right] using h
  have hreal : Measurable[m] (fun w => halfTimeReal (τ w)) :=
    (measurable_ereal_toReal.comp (measurable_subtype_coe.comp htm)).subtype_mk
  intro t
  have he : halfTimeReal (realTimeClamp (t:ℝ)) = t := by
    apply Subtype.ext
    exact changed_time_real t t.property
  have hcut : MeasurableSet[F0 t] {w | τ w ≤ realTimeClamp (t:ℝ)} := by
    have heF : halfClosedFiltration m F0 (realTimeClamp (t:ℝ)) = F0 t := by
      simp only [halfClosedFiltration,ite_eq_left (changed_time_finite t t.property),he]
    rw [← heF]
    exact hτ _
  apply measurable_event_of_augmented_ae P (F0 t) (hl t) (hn t) _ _
    (measurableSet_le hreal measurable_const) hcut
  filter_upwards [hf] with w hw
  obtain ⟨r,hr,_,hrw⟩ := finite_closed_time_real (τ w) hw
  change halfTimeReal (τ w) ≤ t ↔ τ w ≤ realTimeClamp (t:ℝ)
  rw [← hrw]
  change (halfTimeReal (realTimeClamp r):ℝ) ≤ (t:ℝ) ↔ _
  rw [changed_time_real r hr,changed_time_le_iff r hr _ (changed_time_finite t t.property),changed_time_real t t.property]

end Asakura.Chapter7
