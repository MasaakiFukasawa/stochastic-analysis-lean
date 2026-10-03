import Chapter11BarrierHitting
import Mathlib.Topology.Order.MonotoneConvergence

open Set Filter
open scoped Topology
namespace Asakura.Chapter11
set_option maxHeartbeats 2200000

/-- Compact interval exits approach the upper barrier hit on a continuous
 path. The lower barriers escape to minus infinity and the upper barriers
 approach zero. Empty hitting sets use the terminal time of the interval. -/
theorem compact_barrier_exits_tendsto
    {D : Type*} [CompleteLinearOrder D] [DenselyOrdered D]
    [TopologicalSpace D] [OrderTopology D] [CompactSpace D]
    (f : D → ℝ) (hf : Continuous f) :
    Tendsto (fun n : ℕ => sInf {t : D | f t≤-(n:ℝ) ∨ -(1/((n:ℝ)+1))≤f t})
      atTop (𝓝 (sInf {t : D | 0≤f t})) := by
  let τ := sInf {t : D | 0≤f t}
  let σ := fun n : ℕ => sInf {t : D | f t≤-(n:ℝ) ∨ -(1/((n:ℝ)+1))≤f t}
  have hle n : σ n≤τ := by
    apply sInf_le_sInf
    intro t ht
    exact Or.inr ((neg_nonpos.mpr (by positivity)).trans ht)
  apply tendsto_order.mpr
  constructor
  · intro a ha
    obtain ⟨b,hab,hbτ⟩ := exists_between ha
    obtain ⟨t,ht,hm⟩ := isClosed_Iic.isCompact.exists_isMaxOn (show (Iic b).Nonempty from ⟨⊥,bot_le⟩) hf.continuousOn
    have hneg : f t<0 := lt_of_not_ge (fun h => (not_le_of_gt hbτ) ((sInf_le (show t∈{s : D | 0≤f s} from h)).trans ht))
    have hlim : Tendsto (fun n : ℕ => -(1/((n:ℝ)+1))) atTop (𝓝 0) := by
      simpa only [neg_zero] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜:=ℝ)).neg
    obtain ⟨K,hK⟩ := isCompact_univ.exists_bound_of_continuousOn hf.continuousOn
    obtain ⟨k,hk⟩ := exists_nat_gt K
    filter_upwards [hlim.eventually (eventually_gt_nhds hneg),eventually_ge_atTop k] with n hn hkn
    apply hab.trans_le
    apply le_sInf
    intro s hs
    by_contra hbs
    have hsb : s≤b := (lt_of_not_ge hbs).le
    have hfs : f s≤f t := hm hsb
    have hlow : -(n:ℝ)<f s := by
      have hbound : |f s|≤K := by simpa only [Real.norm_eq_abs] using hK s (mem_univ _)
      have hkn' : (k:ℝ)≤n := by exact_mod_cast hkn
      have hnegf := neg_abs_le (f s)
      linarith
    rcases hs with hs | hs
    · exact (not_le_of_gt hlow) hs
    · exact (not_le_of_gt hn) (hs.trans hfs)
  · intro b hb
    exact Eventually.of_forall (fun n => (hle n).trans_lt hb)

end Asakura.Chapter11
