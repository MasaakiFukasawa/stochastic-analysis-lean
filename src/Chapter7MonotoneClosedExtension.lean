import Chapter2LevelLocalization

open MeasureTheory Set Filter
open scoped Topology
namespace Asakura.Chapter7
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete

lemma monotone_at_continuous_endpoint {T : EReal} [Fact (0 ≤ T)] (hT : 0 < T)
    (f : ClosedTime T → ℝ) (hc : Continuous f) (hm : MonotoneOn f (Iio ⊤)) : Monotone f := by
  obtain ⟨u,hu,hut,huc⟩ := deterministic_time_exhaustion hT
  have hlim : Tendsto u atTop (𝓝 ⊤) := by
    apply tendsto_order.mpr
    constructor
    · intro a ha
      obtain ⟨n,hn⟩ := huc a ha
      exact eventually_atTop.mpr ⟨n,fun k hk => hn.trans_le (hu hk)⟩
    · intro a ha
      exact (not_lt_of_ge le_top ha).elim
  intro s t hst
  by_cases ht : t < ⊤
  · exact hm (hst.trans_lt ht) ht hst
  · have he : t = ⊤ := top_le_iff.mp (le_of_not_gt ht)
    subst t
    by_cases hs : s < ⊤
    · apply ge_of_tendsto (hc.continuousAt.tendsto.comp hlim)
      obtain ⟨n,hn⟩ := huc s hs
      exact eventually_atTop.mpr ⟨n,fun k hk => hm hs (hut k) (hn.le.trans (hu hk))⟩
    · have he : s = ⊤ := top_le_iff.mp (le_of_not_gt hs)
      rw [he]

end Asakura.Chapter7
