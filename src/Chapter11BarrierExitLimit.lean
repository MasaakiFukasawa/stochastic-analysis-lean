import Chapter11BarrierCompactExhaustion
import Chapter11CappedInfimum

open Set Filter
open scoped Topology
namespace Asakura.Chapter11
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter7
set_option maxHeartbeats 2400000

/-- The actual half-line compact exits, capped at a finite time, converge
 to the capped barrier time. No path limit at infinite time is required. -/
theorem barrier_compact_exit_limit
    (X : HalfClosedTime → ℝ) (hc : ∀ t,t<⊤ → ContinuousAt X t)
    (R : HalfClosedTime) (hR : R<⊤) :
    Tendsto (fun n : ℕ => min
      (sInf {t : HalfClosedTime | t=⊤ ∨ X t≤-(n:ℝ) ∨ -(1/((n:ℝ)+1))≤X t}) R)
      atTop (𝓝 (min (upperBarrierHit X) R)) := by
  let f := fun t => X (min R t)
  have hf : Continuous f := by
    apply continuous_iff_continuousAt.mpr
    intro t
    exact (hc _ ((min_le_left _ _).trans_lt hR)).comp
      (continuous_const.min continuous_id).continuousAt
  have hl := (compact_barrier_exits_tendsto f hf).min (tendsto_const_nhds (x:=R))
  have hn n : min (sInf {t : HalfClosedTime | f t≤-(n:ℝ) ∨ -(1/((n:ℝ)+1))≤f t}) R=
      min (sInf {t : HalfClosedTime | t=⊤ ∨ X t≤-(n:ℝ) ∨ -(1/((n:ℝ)+1))≤X t}) R := by
    apply capped_infimum_congr
    intro t ht
    simp only [mem_setOf_eq,f,min_eq_right ht.le,or_iff_right (ne_of_lt (ht.trans hR))]
  have htarget : min (sInf {t : HalfClosedTime | 0≤f t}) R=min (upperBarrierHit X) R := by
    apply capped_infimum_congr
    intro t ht
    simp only [mem_setOf_eq,f,min_eq_right ht.le,or_iff_right (ne_of_lt (ht.trans hR))]
  simpa only [hn,htarget] using hl

end Asakura.Chapter11
