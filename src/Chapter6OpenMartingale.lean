import Chapter6DensityLocalBounded
import Chapter6LocalFromStopped

open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology
namespace Asakura.Chapter6
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

/-- Deterministic truncation of a martingale only uses identities before
the truncation time. There is no continuity assumption at the endpoint. -/
theorem deterministic_stopped_martingale
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)]
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t ≤ m)
    (X : ClosedTime T → Ω → ℝ) (ha : ∀ t,Measurable[F t] (X t))
    (hi : ∀ t,t < ⊤ → Integrable (X t) P)
    (hm : ∀ s t,s ≤ t → t < ⊤ → P[X t|F s] =ᵐ[P] X s)
    (v : ClosedTime T) (hv : v < ⊤) :
    ∀ s t,s ≤ t → P[(fun w => X (min v t) w)|F s] =ᵐ[P] fun w => X (min v s) w := by
  intro s t hst
  by_cases hsv : s ≤ v
  · rw [min_eq_right hsv]
    exact hm s (min v t) (le_min hsv hst) ((min_le_left _ _).trans_lt hv)
  · have hvs := le_of_not_ge hsv
    rw [min_eq_left hvs, min_eq_left (hvs.trans hst)]
    exact Filter.EventuallyEq.of_eq (condExp_of_stronglyMeasurable (hle s)
      ((ha v).mono (hF hvs) le_rfl).stronglyMeasurable (hi v hv))

/-- A martingale continuous on the manuscript's half-open time interval
is local, without adding continuity or integrability at its endpoint. -/
theorem open_continuous_martingale_is_local
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (hT : 0 < T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t ≤ m)
    (X : ClosedTime T → Ω → ℝ)
    (ha : ∀ t,Measurable[F t] (X t))
    (hc : ∀ w t,t < ⊤ → ContinuousAt (fun s => X s w) t)
    (hi : ∀ t,t < ⊤ → Integrable (X t) P)
    (hm : ∀ s t,s ≤ t → t < ⊤ → P[X t|F s] =ᵐ[P] X s)
    (hz : X ⊥ =ᵐ[P] 0)
    (u : ℕ → ClosedTime T) (hu : Monotone u) (hut : ∀ n,u n < ⊤)
    (huc : ∀ t,t < ⊤ → ∃ n,t < u n) : LocalMProcessWitness P F X := by
  apply local_of_local_stopped P hT F hF hle X ha hc hz (fun n _ => u n)
    (fun _ => hu) (fun _ => huc)
  intro n
  apply continuous_martingale_is_local P F hF hle _
    (fun t => (ha _).mono (hF (min_le_right _ _)) le_rfl)
    (fun w => continuous_iff_continuousAt.mpr fun t =>
      (hc w _ ((min_le_left _ _).trans_lt (hut n))).comp
        (continuous_const.min continuous_id).continuousAt)
    (fun t => hi _ ((min_le_left _ _).trans_lt (hut n)))
    (deterministic_stopped_martingale P F hF hle X ha hi hm (u n) (hut n))
    (by simpa only [min_bot_right] using hz) u hu hut huc

end Asakura.Chapter6
