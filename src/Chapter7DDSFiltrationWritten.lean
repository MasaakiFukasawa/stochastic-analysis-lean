import Chapter7DDSWritten
import Chapter7StoppedSpaceAE

open MeasureTheory Set Filter
open scoped Topology ENNReal NNReal
namespace Asakura.Chapter7
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4
set_option maxHeartbeats 3500000
set_option backward.isDefEq.respectTransparency false

/-- DDS with the manuscript's right-continuous stopped filtration made
explicit. A is a simultaneous representative of the original bracket;
the inverse clocks therefore agree off one null set as well. -/
theorem dds_written_with_filtration
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (hT : 0 < T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t ≤ m)
    (hnull : ∀ t N,MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)
    (X C : ClosedTime T → Ω → ℝ) (hX : LocalMProcessWitness P F X)
    (hC : LocalCovarianceWitness P F X X C)
    (hdiv : ∀ᵐ w ∂P,∀ r : ℝ,∃ t,t < ⊤ ∧ r < C t w) :
    ∃ (A : ClosedTime T → Ω → ℝ) (B : BrownianSystem P 1),
      (∀ᵐ w ∂P,∀ a,A a w = C a w) ∧
      (∀ᵐ w ∂P,∀ r,inverseRealClock (fun a => A a w) r = inverseRealClock (fun a => C a w) r) ∧
      (∀ᵐ w ∂P,∀ t,B.W 0 t w = X (inverseRealClock (fun a => C a w) (halfTimeReal t)) w) ∧
      (∀ᵐ w ∂P,∀ a,a < ⊤ → X a w = B.W 0 (realTimeClamp (C a w)) w) ∧
      (∀ a,a < ⊤ → ∀ t,MeasurableSet[B.F t] {w | realTimeClamp (T := (⊤:EReal)) (C a w) ≤ t}) ∧
      (∃ hτ : ∀ r t,MeasurableSet[F t] {w | inverseRealClock (fun a => A a w) r ≤ t},
        B.F = halfClosedFiltration m (fun s : ℝ≥0 =>
          ⨅ r : Ioi (s:ℝ),writtenStoppedSpace m F
            (fun w => inverseRealClock (fun a => A a w) r.val) (hτ r.val))) := by
  obtain ⟨Y,A,hY,hA,he,hAm,hAc,h0,hAu,hflat⟩ :=
    dds_regular_representatives P hT F hF hle hnull X C hX hC hdiv
  obtain ⟨B,hB,hrec,hstop,hBF⟩ := dds_system_from_regular_paths_with_filtration P hT F hF hle hnull Y A hY hA
    hAm (fun w => (h0 w).2) hAu hflat
  refine ⟨A,B,he.mono (fun w hw a => (hw a).2),?_,?_,?_,?_,hBF⟩
  · filter_upwards [he] with w hw
    have hc : (fun a => A a w) = fun a => C a w := funext fun a => (hw a).2
    intro r
    rw [hc]
  · filter_upwards [he] with w hw
    have hc : (fun a => A a w) = fun a => C a w := funext fun a => (hw a).2
    intro t
    rw [hB,hc,(hw _).1]
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
