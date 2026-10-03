import Chapter7DDSRepresentatives
import Chapter7DDSRegularSystem
import Chapter7NullEventTransfer

open MeasureTheory Set Filter
open scoped Topology ENNReal NNReal
namespace Asakura.Chapter7
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

/-- DDS from the manuscript's original local martingale, its actual bracket
and divergence almost surely. No time-changed martingale, path-flatness,
pointwise bracket monotonicity, or Brownian representation is assumed.
The BrownianSystem is constructed by optional sampling and Levy's actual
local-martingale/covariance criterion from the preceding chapters. -/
theorem dds_written
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (hT : 0 < T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t ≤ m)
    (hnull : ∀ t N,MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)
    (X C : ClosedTime T → Ω → ℝ) (hX : LocalMProcessWitness P F X)
    (hC : LocalCovarianceWitness P F X X C)
    (hdiv : ∀ᵐ w ∂P,∀ r : ℝ,∃ t,t < ⊤ ∧ r < C t w) :
    ∃ B : BrownianSystem P 1,
      (∀ᵐ w ∂P,∀ t,B.W 0 t w = X (inverseRealClock (fun a => C a w) (halfTimeReal t)) w) ∧
      (∀ᵐ w ∂P,∀ a,a < ⊤ → X a w = B.W 0 (realTimeClamp (C a w)) w) ∧
      (∀ a,a < ⊤ → ∀ t,MeasurableSet[B.F t] {w | realTimeClamp (T := (⊤:EReal)) (C a w) ≤ t}) := by
  obtain ⟨Y,A,hY,hA,he,hAm,hAc,h0,hAu,hflat⟩ :=
    dds_regular_representatives P hT F hF hle hnull X C hX hC hdiv
  obtain ⟨B,hB,hrec,hstop⟩ := dds_system_from_regular_paths P hT F hF hle hnull Y A hY hA
    hAm (fun w => (h0 w).2) hAu hflat
  refine ⟨B,?_,?_,?_⟩
  · filter_upwards [he] with w hw
    have hclock : (fun a => A a w) = fun a => C a w := funext (fun a => (hw a).2)
    intro t
    rw [hB,hclock,(hw _).1]
  · filter_upwards [he] with w hw
    intro a ha
    have hh := hrec a ha w
    rwa [(hw a).1,(hw a).2] at hh
  · intro a ha t
    apply measurable_event_of_augmented_ae P (B.F t) (B.le t) (B.null t)
      _ {w | realTimeClamp (T := (⊤:EReal)) (A a w) ≤ t}
    · exact measurableSet_le
        (real_time_clamp_continuous.measurable.comp ((hC.adapted P F hX hX a ha).mono (hle a) le_rfl))
        measurable_const
    · exact hstop a ha t
    · filter_upwards [he] with w hw
      rw [(hw a).2]

end Asakura.Chapter7
