import Chapter3RegularizedWeightRegularity

open MeasureTheory Set Filter
open scoped Topology
namespace Asakura.Chapter3Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete

theorem open_path_real_measurable {T : EReal} [Fact (0 ≤ T)]
    (Y : ClosedTime T → ℝ) (hc : ∀ t, t < ⊤ → ContinuousAt Y t) :
    Measurable (fun r : ℝ => Y (realTimeClamp r)) := by
  have hh : ContinuousOn Y (Iio ⊤) := fun t ht => (hc t ht).continuousWithinAt
  have hm : Measurable Y := hh.measurable_of_countable_compl (by simp)
  exact hm.comp real_time_clamp_continuous.measurable

end Asakura.Chapter3Complete
#print axioms Asakura.Chapter3Complete.open_path_real_measurable
