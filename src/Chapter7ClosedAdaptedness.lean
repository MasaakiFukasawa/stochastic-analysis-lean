import Chapter2LevelLocalization

open MeasureTheory Set Filter
open scoped Topology
namespace Asakura.Chapter7
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 1500000

/-- Continuity at the endpoint supplies its adaptedness from the open
interval, using a deterministic increasing exhaustion. -/
theorem closed_adapted_of_open_continuous
    {Ω : Type*} {T : EReal} [Fact (0 ≤ T)] (hT : 0 < T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F)
    (X : ClosedTime T → Ω → ℝ)
    (ha : ∀ t,t < ⊤ → Measurable[F t] (X t))
    (hc : ∀ w,Continuous (fun t => X t w)) : ∀ t,Measurable[F t] (X t) := by
  intro t
  by_cases ht : t < ⊤
  · exact ha t ht
  · have he : t = ⊤ := top_le_iff.mp (le_of_not_gt ht)
    subst t
    obtain ⟨u,hu,hut,huc⟩ := deterministic_time_exhaustion hT
    have hlim : Tendsto u atTop (𝓝 ⊤) := by
      apply tendsto_order.mpr
      constructor
      · intro a ha
        obtain ⟨n,hn⟩ := huc a ha
        exact eventually_atTop.mpr ⟨n,fun k hk => hn.trans_le (hu hk)⟩
      · intro a ha
        exact (not_lt_of_ge le_top ha).elim
    letI : MeasurableSpace Ω := F ⊤
    apply measurable_of_tendsto_metrizable (fun n => (ha (u n) (hut n)).mono (hF le_top) le_rfl)
    apply tendsto_pi_nhds.mpr
    intro w
    exact (hc w).continuousAt.tendsto.comp hlim

end Asakura.Chapter7
