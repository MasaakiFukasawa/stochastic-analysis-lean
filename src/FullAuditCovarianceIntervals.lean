import FullAuditQVPolynomial
import FullAuditQuadraticCS

open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace Asakura.FullAudit
open Asakura.Chapter1Written Asakura.Chapter2Written
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false

/-- One null set suffices for all real time intervals: first intersect the
 events for rational scalars, then extend the quadratic polynomial by density.
 The preceding identities already hold simultaneously at all times. -/
theorem bounded_cov_interval_cs {Ω : Type*} {m : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] {T : EReal} [Fact (0 ≤ T)]
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (hnull : ∀ t N, MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)
    (X Y : boundedMProcess P F) :
    ∀ᵐ ω ∂P, ∀ s t : ClosedTime T, s ≤ t →
      |boundedCov P F hF hle hnull X Y t ω-boundedCov P F hF hle hnull X Y s ω| ≤
      Real.sqrt (boundedQV P F hF hle hnull X t ω-boundedQV P F hF hle hnull X s ω)*
      Real.sqrt (boundedQV P F hF hle hnull Y t ω-boundedQV P F hF hle hnull Y s ω) := by
  have hq := ae_all_iff.mpr (fun q : ℚ => bounded_qv_quadratic P F hF hle hnull X Y (q:ℝ))
  filter_upwards [hq] with ω hω
  intro s t hst
  apply quadratic_interval_cs
  · exact sub_nonneg.mpr ((boundedQV_properties P F hF hle hnull X).2.2.1 ω hst)
  · exact sub_nonneg.mpr ((boundedQV_properties P F hF hle hnull Y).2.2.1 ω hst)
  · intro q
    have h := (boundedQV_properties P F hF hle hnull ((q:ℝ) • X+Y)).2.2.1 ω hst
    change boundedQV P F hF hle hnull ((q:ℝ) • X+Y) s ω ≤
      boundedQV P F hF hle hnull ((q:ℝ) • X+Y) t ω at h
    rw [hω q s,hω q t] at h
    nlinarith

end Asakura.FullAudit
