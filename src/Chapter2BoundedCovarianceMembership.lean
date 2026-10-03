import Chapter2ActualLocalVariation
import FullAuditCovarianceBasics

open MeasureTheory Set Filter
open scoped Topology ENNReal Classical
namespace Asakura.Chapter2Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written
set_option backward.isDefEq.respectTransparency false

/-- The polarization belongs to the actual A of the manuscript, not only
pathwise bounded variation: its increasing parts are adapted and continuous. -/
theorem bounded_covariance_adapted_variation
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (F : ClosedTime T → MeasurableSpace Ω)
    (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (hnull : ∀ t N, MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)
    (X Y : boundedMProcess P F) :
    AdaptedVariationWitness F (boundedCov P F hF hle hnull X Y) := by
  let Q := boundedQV P F hF hle hnull
  have hp := boundedQV_properties P F hF hle hnull (X+Y)
  have hn := boundedQV_properties P F hF hle hnull (X-Y)
  refine ⟨fun t ω => Q (X+Y) t ω/4,fun t ω => Q (X-Y) t ω/4,?_,?_,?_,?_⟩
  · intro t
    exact ⟨(hp.1 t).div_const 4,(hn.1 t).div_const 4⟩
  · intro ω
    exact ⟨fun s t hst => div_le_div_of_nonneg_right (hp.2.2.1 ω hst) (by norm_num),
      fun s t hst => div_le_div_of_nonneg_right (hn.2.2.1 ω hst) (by norm_num)⟩
  · intro ω t
    exact ⟨((hp.2.1 ω).div_const 4).continuousAt.continuousWithinAt,
      ((hn.2.1 ω).div_const 4).continuousAt.continuousWithinAt⟩
  · intro t ω
    dsimp only [boundedCov,Q]
    ring

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.bounded_covariance_adapted_variation
