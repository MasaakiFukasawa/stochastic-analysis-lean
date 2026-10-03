import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

open MeasureTheory Set
open scoped ENNReal
namespace Asakura.Chapter6
set_option maxHeartbeats 1800000

theorem measurable_equiv_map_density {E F : Type*} [MeasurableSpace E] [MeasurableSpace F]
    (ν : Measure E) (e : E ≃ᵐ F) (g : E → ℝ≥0∞) (hg : Measurable g) :
    (ν.withDensity g).map e=(ν.map e).withDensity (fun y => g (e.symm y)) := by
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply e.measurable hs,withDensity_apply _ (e.measurable hs),withDensity_apply _ hs,
    ←lintegral_indicator hs]
  have hgm : Measurable (fun y => g (e.symm y)) := hg.comp e.symm.measurable
  rw [lintegral_map (hgm.indicator hs) e.measurable]
  rw [←lintegral_indicator (e.measurable hs)]
  apply lintegral_congr
  intro x
  by_cases hx : e x∈s <;> simp [indicator,hx]

end Asakura.Chapter6
