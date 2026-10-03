import Chapter4PowerGrowth

open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter4
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

lemma finite_sum_power_moment
    {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
    (P : Measure Ω) {n : ℕ} (X : Fin n → Ω → E) (p : ℝ) (hp : 1≤p)
    (hi : ∀ i,MemLp (X i) (ENNReal.ofReal p) P) :
    MemLp (fun w => ∑ i,X i w) (ENNReal.ofReal p) P ∧
      (∫ w,‖∑ i,X i w‖^p ∂P)≤(n:ℝ)^(p-1)*∑ i,∫ w,‖X i w‖^p ∂P := by
  have hp0 : 0<p := zero_lt_one.trans_le hp
  have hs : MemLp (fun w => ∑ i,X i w) (ENNReal.ofReal p) P := by
    convert memLp_finsetSum' Finset.univ (fun i _ => hi i) using 1
    ext w
    simp
  have hi' (Y : Ω → E) (hY : MemLp Y (ENNReal.ofReal p) P) : Integrable (fun w => ‖Y w‖^p) P := by
    simpa only [ENNReal.toReal_ofReal hp0.le] using hY.integrable_norm_rpow
      (ne_of_gt (ENNReal.ofReal_pos.mpr hp0)) ENNReal.ofReal_ne_top
  refine ⟨hs,?_⟩
  rw [← integral_finsetSum Finset.univ (fun i _ => hi' (X i) (hi i)),← integral_const_mul]
  apply integral_mono (hi' _ hs)
    ((integrable_finsetSum Finset.univ (fun i _ => hi' (X i) (hi i))).const_mul _)
  exact fun w => finite_sum_norm_power (fun i => X i w) p hp

end Asakura.Chapter4
