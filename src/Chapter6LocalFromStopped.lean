import Chapter2CommonStopLimit
import Chapter2ContinuousLocalizers

open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace Asakura.Chapter6
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

/-- A process is local if each member of an increasing cofinal family of
its stopped processes is local. Common bounded localizers are constructed
from the original path, rather than postulated. -/
theorem local_of_local_stopped
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (hT : 0 < T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t ≤ m)
    (Y : ClosedTime T → Ω → ℝ)
    (ha : ∀ t,Measurable[F t] (Y t))
    (hc : ∀ w t,t < ⊤ → ContinuousAt (fun s => Y s w) t)
    (hz : Y ⊥ =ᵐ[P] 0)
    (τ : ℕ → Ω → ClosedTime T)
    (hm : ∀ w,Monotone (fun n => τ n w))
    (hco : ∀ w t,t < ⊤ → ∃ n,t < τ n w)
    (hlocal : ∀ n,LocalMProcessWitness P F (fun t w => Y (min (τ n w) t) w)) :
    LocalMProcessWitness P F Y := by
  obtain ⟨σ,hs,hsm,hst,hsc,hb⟩ := halfopen_continuous_bounded_localizers P hT F hF Y ha hc hz
  refine local_limit_of_common_bounded_stops P F hF hle _ hlocal Y hc ?_ σ hs hsm hst hsc
    (fun k => (k:ℝ)) ?_
  · intro w t ht
    obtain ⟨n,hn⟩ := hco w t ht
    apply tendsto_const_nhds.congr'
    apply eventually_atTop.mpr
    refine ⟨n,fun k hk => ?_⟩
    change Y t w = Y (min (τ k w) t) w
    rw [min_eq_right (hn.le.trans (hm w hk))]
  · intro k n
    filter_upwards [hb k] with w hw
    intro t
    change ‖Y (min (τ n w) (min (σ k w) t)) w‖ ≤ (k:ℝ)
    rw [min_left_comm]
    exact hw (min (τ n w) t)

end Asakura.Chapter6
