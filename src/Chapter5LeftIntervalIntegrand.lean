import Chapter5BoundedIntervalEnergy

open Set Filter
open scoped Topology
namespace Asakura.Chapter5
set_option maxHeartbeats 2000000

/-- Taking the right endpoint of every interval makes the truncated
continuous integrand left-continuous, including at both joining points. -/
theorem continuous_left_interval_indicator (a b : ℝ) (H : ℝ → ℝ)
    (hH : Continuous H) (t : ℝ) :
    ContinuousWithinAt ((Ioc a b).indicator H) (Iic t) t := by
  classical
  by_cases ha : t≤a
  · have he : (Ioc a b).indicator H =ᶠ[𝓝[Iic t] t] (fun _ => 0) := by
      filter_upwards [self_mem_nhdsWithin] with r hr
      exact indicator_of_notMem (fun hm => not_lt_of_ge (hr.trans ha) hm.1) _
    exact continuousWithinAt_const.congr_of_eventuallyEq he
      (indicator_of_notMem (fun hm => not_lt_of_ge ha hm.1) H)
  · by_cases hb : t≤b
    · have he : (Ioc a b).indicator H =ᶠ[𝓝[Iic t] t] H := by
        filter_upwards [self_mem_nhdsWithin,nhdsWithin_le_nhds (Ioi_mem_nhds (lt_of_not_ge ha))] with r hr hra
        exact indicator_of_mem (show r∈Ioc a b from ⟨hra,hr.trans hb⟩) _
      exact hH.continuousAt.continuousWithinAt.congr_of_eventuallyEq he
        (indicator_of_mem (show t∈Ioc a b from ⟨lt_of_not_ge ha,hb⟩) H)
    · have he : (Ioc a b).indicator H =ᶠ[𝓝[Iic t] t] (fun _ => 0) := by
        filter_upwards [nhdsWithin_le_nhds (Ioi_mem_nhds (lt_of_not_ge hb))] with r hr
        exact indicator_of_notMem (fun hm => not_le_of_gt hr hm.2) _
      exact continuousWithinAt_const.congr_of_eventuallyEq he
        (indicator_of_notMem (fun hm => hb hm.2) H)

/-- Only continuity on the finite interval is needed. Clamping gives a
continuous extension without changing the interval-restricted process. -/
theorem continuous_left_interval_indicator_of_continuousOn
    (a b : ℝ) (ha : 0≤a) (hab : a≤b) (H : ℝ → ℝ)
    (hH : ContinuousOn H (Icc 0 b)) (t : ℝ) :
    ContinuousWithinAt ((Ioc a b).indicator H) (Iic t) t := by
  classical
  let K := H ∘ Asakura.FullAudit.intervalClamp 0 b (ha.trans hab)
  have hK : Continuous K := hH.comp_continuous
    (Asakura.FullAudit.intervalClamp_continuous 0 b (ha.trans hab))
    (Asakura.FullAudit.intervalClamp_mem 0 b (ha.trans hab))
  have he : (Ioc a b).indicator H=(Ioc a b).indicator K := by
    funext r
    by_cases hr : r∈Ioc a b
    · simp only [indicator_of_mem hr,K,Function.comp_apply]
      rw [Asakura.FullAudit.intervalClamp_eq 0 b (ha.trans hab) ⟨ha.trans hr.1.le,hr.2⟩]
    · simp only [indicator_of_notMem hr]
  rw [he]
  exact continuous_left_interval_indicator a b K hK t

end Asakura.Chapter5
