import FullAuditContinuousOptional

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter7
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

/-- Optional sampling supplies the martingale property after an increasing
family of random times; no martingale identity for the changed process is assumed. -/
theorem random_time_martingale_identity
    {Ω ι : Type*} {m : MeasurableSpace Ω} [Preorder ι]
    (P : Measure Ω) [IsProbabilityMeasure P] {T : EReal} (hT : 0 ≤ T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t ≤ m)
    (X : ClosedTime T → Ω → ℝ) (ha : ∀ t,Measurable[F t] (X t))
    (hi : ∀ t,Integrable (X t) P) (hc : ∀ w,Continuous (fun t => X t w))
    (hM : ∀ s t,s ≤ t → P[X t|F s] =ᵐ[P] X s)
    (τ : ι → Ω → ClosedTime T)
    (hτ : ∀ s t,MeasurableSet[F t] {w | τ s w ≤ t})
    (hm : ∀ w,Monotone (fun s => τ s w))
    (s t : ι) (hst : s ≤ t) :
    P[(fun w => X (τ t w) w)|writtenStoppedSpace m F (τ s) (hτ s)] =ᵐ[P]
      (fun w => X (τ s w) w) := by
  have h := continuous_optional_sampling_written P hT F hF hle X ha hi
    (fun w t => (hc w).continuousAt.continuousWithinAt) hM (τ t) (τ s) (hτ t) (hτ s)
  simpa only [min_eq_right (hm _ hst)] using h

/-- The time-changed value is genuinely measurable for its stopped sigma algebra. -/
theorem random_time_adapted
    {Ω ι : Type*} {m : MeasurableSpace Ω}
    {T : EReal} (hT : 0 ≤ T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t ≤ m)
    (X : ClosedTime T → Ω → ℝ) (ha : ∀ t,Measurable[F t] (X t))
    (hc : ∀ w,Continuous (fun t => X t w))
    (τ : ι → Ω → ClosedTime T)
    (hτ : ∀ s t,MeasurableSet[F t] {w | τ s w ≤ t}) (s : ι) :
    Measurable[writtenStoppedSpace m F (τ s) (hτ s)] (fun w => X (τ s w) w) :=
  stopped_value_measurable_right_continuous m hT F hF hle (τ s) (hτ s) X ha
    (fun w t => (hc w).continuousAt.continuousWithinAt)

end Asakura.Chapter7
