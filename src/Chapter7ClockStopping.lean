import Chapter7InverseClock
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

open MeasureTheory Set Filter
open scoped NNReal Topology
namespace Asakura.Chapter7

/-- No abstract stopping-time assumption: the event is identified with an
adapted clock's measurable superlevel set. -/
theorem inverse_clock_stopping {Ω : Type*}
    (F : ℝ≥0 → MeasurableSpace Ω) (A : ℝ≥0 → Ω → ℝ≥0)
    (ha : ∀ t,Measurable[F t] (A t))
    (hc : ∀ w,Continuous (fun t => A t w))
    (hm : ∀ w,Monotone (fun t => A t w))
    (hu : ∀ w s,∃ t,s ≤ A t w) (s t : ℝ≥0) :
    MeasurableSet[F t] {w | firstClockTime (fun t => A t w) s ≤ t} := by
  have he : {w | firstClockTime (fun t => A t w) s ≤ t} = {w | s ≤ A t w} := by
    ext w
    exact firstClockTime_le_iff _ (hc w) (hm w) (hu w) s t
  rw [he]
  exact measurableSet_le measurable_const (ha t)

end Asakura.Chapter7
