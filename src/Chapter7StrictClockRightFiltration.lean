import Chapter7StoppedSpaceLimit
import Chapter7InverseClockODEConnection

open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
namespace Asakura.Chapter7
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency false

/-- The raw stopped sigma algebras in the clock-ODE construction are
right-continuous when the original filtration is right-continuous. -/
theorem strict_inverse_clock_right_filtration
    {Ω : Type*} (m : MeasurableSpace Ω)
    (F : HalfClosedTime → MeasurableSpace Ω) (hF : Monotone F)
    (hright : ∀ t,t < ⊤ → F t = ⨅ s : Ioi t,F s.val)
    (A : HalfClosedTime → Ω → ℝ)
    (ha : ∀ t,t < ⊤ → Measurable[F t] (A t))
    (hm : ∀ w,StrictMonoOn (fun t => A t w) (Iio ⊤))
    (hc : ∀ w t,t < ⊤ → ContinuousAt (fun s => A s w) t)
    (hz : ∀ w,A ⊥ w = 0) (hu : ∀ w r,∃ t,t < ⊤ ∧ r < A t w) :
    let τ := fun r w => inverseRealClock (fun t => A t w) r
    ∃ hτ : ∀ r t,MeasurableSet[F t] {w | τ r w ≤ t},
      ∀ r,writtenStoppedSpace m F (τ r) (hτ r) =
        ⨅ s : Ioi r,writtenStoppedSpace m F (τ s.val) (hτ s.val) := by
  let τ := fun r w => inverseRealClock (fun t => A t w) r
  have hT : (0:EReal) < ⊤ := by simp
  have hτ := real_clock_inverse_stopping hT F A ha (fun w => (hm w).monotoneOn) hc hz hu
  have hp w := real_clock_inverse_properties hT (fun t => A t w) (hm w).monotoneOn (hc w) (hz w) (hu w)
  have hτc w : Continuous (fun r => τ r w) := by
    have hr := real_clock_changed_path_continuous hT (fun t => A t w) (hm w).monotoneOn
      (hc w) (hz w) (hu w) (fun t => (halfTimeReal t:ℝ)) changed_time_coordinate_continuousAt
      (fun a b ha hb he => by rw [(hm w).injOn ha hb he])
    have hh := (real_time_clamp_continuous (T := (⊤:EReal))).comp hr
    convert hh using 1
    funext r
    exact (finite_clock_clamp_coordinate _ ((hp w).2.2.1 r)).symm
  exact ⟨hτ,fun r => stopped_clock_right_continuous m F hF hright τ hτ
    (fun w => (hp w).1) hτc r⟩

end Asakura.Chapter7
