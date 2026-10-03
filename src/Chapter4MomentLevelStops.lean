import Chapter2LevelLocalization
import Chapter4PrefixPowerMoment

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter4
open Asakura.Chapter2Complete
set_option maxHeartbeats 1500000

/-- No initial bound is needed: when the path starts above the level,
the first hitting time is zero and the stopped path stays at its initial value. -/
theorem continuous_level_stop_bound_with_initial
    {D : Type*} [CompleteLinearOrder D] [DenselyOrdered D]
    [TopologicalSpace D] [OrderTopology D]
    (f : D → ℝ) (hf : Continuous f) (K : ℝ) :
    ∀ t,|f (min (sInf {s | K≤|f s|}) t)|≤max |f ⊥| K := by
  by_cases h : |f ⊥|≤K
  · intro t
    exact (continuous_level_stop_bound (fun t => |f t|) hf.abs K h _ (min_le_left _ _)).trans (le_max_right _ _)
  · have he : sInf {s | K≤|f s|}=⊥ := le_bot_iff.mp (sInf_le (lt_of_not_ge h).le)
    intro t
    rw [he,min_eq_left bot_le]
    exact le_max_left _ _

/-- On each continuous compact path the level-stopped paths are eventually
identical to the full path, which justifies the final moment-limit step. -/
theorem level_stops_eventually_full
    {D : Type*} [CompleteLinearOrder D] [TopologicalSpace D] [CompactSpace D]
    (f : C(D,ℝ)) : ∀ᶠ n : ℕ in atTop,∀ t,
      f (min (sInf {s | (n:ℝ)≤|f s|}) t)=f t := by
  obtain ⟨k,hk⟩ := exists_nat_gt ‖f‖
  filter_upwards [eventually_ge_atTop k] with n hn
  have hkn : (k:ℝ)≤n := by exact_mod_cast hn
  have he : {s | (n:ℝ)≤|f s|}=∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro t ht
    have hb : |f t|≤‖f‖ := by simpa only [Real.norm_eq_abs] using f.norm_coe_le_norm t
    exact (not_le_of_gt (hk.trans_le hkn)) (ht.trans hb)
  simp only [he,sInf_empty,min_top_left,implies_true]

end Asakura.Chapter4
