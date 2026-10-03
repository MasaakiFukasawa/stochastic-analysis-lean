import Chapter4BoundedLocalConditional

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter4
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

/-- The local martingale criterion also applies when Ito's formula has
first been established at each deterministic time separately. -/
theorem bounded_local_increment_conditional_of_pointwise
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0≤T)] (hT : 0<T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (X N : ClosedTime T → Ω → ℝ) (hN : LocalMProcessWitness P F N)
    (ha : ∀ t,t<⊤ → Measurable[F t] (X t))
    (hc : ∀ w t,t<⊤ → ContinuousAt (fun s => X s w) t)
    (R : ClosedTime T) (hR : R<⊤) (K : ℝ)
    (hb : ∀ᵐ w ∂P,∀ t,t≤R → |X t w|≤K)
    (he : ∀ t,t≤R → X t=ᵐ[P] fun w => X ⊥ w+N t w)
    (s : ClosedTime T) (hs : s≤R) : P[X R | F s]=ᵐ[P] X s := by
  have he' := continuous_process_common_time_equality P
    (fun t w => X (min R t) w) (fun t w => X ⊥ w+N (min R t) w)
    (fun w => continuous_iff_continuousAt.mpr fun t =>
      (hc w _ ((min_le_left _ _).trans_lt hR)).comp (continuous_const.min continuous_id).continuousAt)
    (fun w => continuous_const.add (continuous_iff_continuousAt.mpr fun t =>
      (hN.path P F w _ ((min_le_left _ _).trans_lt hR)).comp (continuous_const.min continuous_id).continuousAt))
    (fun t => he (min R t) (min_le_left _ _))
  apply bounded_local_increment_conditional P hT F hF hle X N hN ha R hR K hb _ s hs
  filter_upwards [he'] with w hw
  intro t ht
  simpa only [min_eq_right ht] using hw t

end Asakura.Chapter4
