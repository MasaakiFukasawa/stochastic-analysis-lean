import Chapter4NormEnvelope
import Chapter4FiniteSumPowerMoment

open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter4
set_option maxHeartbeats 1800000

lemma bundle_path_power_le_sum {D : Type*} [TopologicalSpace D] [CompactSpace D] {n : ℕ}
    (Y : Fin n → C(D,ℝ)) (p : ℝ) (hp : 1≤p) :
    ‖bundleRealPaths Y‖^p≤(n:ℝ)^(p-1)*∑ i,‖Y i‖^p := by
  have hh := finite_sum_norm_power (fun i => ‖Y i‖) p hp
  simp only [Real.norm_eq_abs,abs_of_nonneg (Finset.sum_nonneg (fun _ _ => norm_nonneg _)),abs_norm] at hh
  exact (Real.rpow_le_rpow (norm_nonneg _) (bundle_path_norm_le_sum Y) (zero_le_one.trans hp)).trans hh

lemma bundle_path_memLp_power
    {Ω D : Type*} [MeasurableSpace Ω] [MetricSpace D] [CompactSpace D] [SecondCountableTopology D]
    (P : Measure Ω) {n : ℕ} (Y : Fin n → Ω → C(D,ℝ))
    (hm : ∀ i,Measurable (Y i)) (p : ℝ≥0∞) (hi : ∀ i,MemLp (Y i) p P) :
    MemLp (fun w => bundleRealPaths (fun i => Y i w)) p P := by
  have hs : MemLp (fun w => ∑ i,‖Y i w‖) p P := by
    convert memLp_finsetSum' Finset.univ (fun i _ => (hi i).norm) using 1
    ext w
    simp
  apply hs.of_le_mul (c := 1) (bundle_path_measurable Y hm).aestronglyMeasurable
  exact .of_forall (fun w => by
    simpa only [one_mul,Real.norm_eq_abs,abs_of_nonneg (Finset.sum_nonneg (fun _ _ => norm_nonneg _))] using
      bundle_path_norm_le_sum (fun i => Y i w))

lemma bundle_path_power_moment
    {Ω D : Type*} [MeasurableSpace Ω] [MetricSpace D] [CompactSpace D] [SecondCountableTopology D]
    (P : Measure Ω) {n : ℕ} (Y : Fin n → Ω → C(D,ℝ))
    (hm : ∀ i,Measurable (Y i)) (p : ℝ) (hp : 1≤p) (hi : ∀ i,MemLp (Y i) (ENNReal.ofReal p) P) :
    (∫ w,‖bundleRealPaths (fun i => Y i w)‖^p ∂P)≤(n:ℝ)^(p-1)*∑ i,∫ w,‖Y i w‖^p ∂P := by
  have hp0 : 0<p := zero_lt_one.trans_le hp
  have hI i : Integrable (fun w => ‖Y i w‖^p) P := by
    simpa only [ENNReal.toReal_ofReal hp0.le] using (hi i).integrable_norm_rpow
      (ne_of_gt (ENNReal.ofReal_pos.mpr hp0)) ENNReal.ofReal_ne_top
  have hB : Integrable (fun w => ‖bundleRealPaths (fun i => Y i w)‖^p) P := by
    simpa only [ENNReal.toReal_ofReal hp0.le] using (bundle_path_memLp_power P Y hm (ENNReal.ofReal p) hi).integrable_norm_rpow
      (ne_of_gt (ENNReal.ofReal_pos.mpr hp0)) ENNReal.ofReal_ne_top
  rw [← integral_finsetSum Finset.univ (fun i _ => hI i),← integral_const_mul]
  apply integral_mono hB ((integrable_finsetSum Finset.univ (fun i _ => hI i)).const_mul _)
  exact fun w => bundle_path_power_le_sum (fun i => Y i w) p hp

end Asakura.Chapter4
