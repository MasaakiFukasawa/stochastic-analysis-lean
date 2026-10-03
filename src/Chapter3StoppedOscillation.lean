import Chapter3QuadraticApproximationLocalizers
import Mathlib.Topology.MetricSpace.Lipschitz

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter3Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 1200000

/-- Stopping preserves the all-time increment bound for the same partition. -/
theorem stopped_partition_increment_bound
    {ι : Type*} [LinearOrder ι] (X : ι → ℝ) (τ : ℕ → ι) (σ : ι) (δ : ℝ)
    (hb : ∀ j t, |X (min (τ (j+1)) t)-X (min (τ j) t)| ≤ δ) :
    ∀ j t, |X (min σ (min (τ (j+1)) t))-X (min σ (min (τ j) t))| ≤ δ := by
  intro j t
  simpa only [min_left_comm] using hb j (min σ t)

/-- Stopping a continuous weight preserves its interval oscillation. -/
theorem stopped_interval_oscillation
    {ι : Type*} [LinearOrder ι] (H : ι → ℝ) (τ : ℕ → ι) (σ : ι) (δ : ℝ) (hδ : 0 ≤ δ)
    (hb : ∀ j t, τ j ≤ t → t ≤ τ (j+1) → |H (τ j)-H t| ≤ δ) :
    ∀ j t, τ j ≤ t → t ≤ τ (j+1) → |H (min σ (τ j))-H (min σ t)| ≤ δ := by
  intro j t hj ht
  by_cases hs : σ ≤ τ j
  · simpa only [min_eq_left hs,min_eq_left (hs.trans hj),sub_self,abs_zero] using hδ
  · have hjs := le_of_not_ge hs
    rw [min_eq_right hjs]
    exact hb j (min σ t) (le_min hjs hj) ((min_le_right _ _).trans ht)

/-- Scalar clipping is a contraction, so it does not worsen the partition
oscillation rate. -/
theorem interval_clamp_abs_sub_le
    (a b : ℝ) (hab : a ≤ b) (x y : ℝ) :
    |intervalClamp a b hab x-intervalClamp a b hab y| ≤ |x-y| := by
  have h := (LipschitzWith.projIcc hab).dist_le_mul x y
  simpa only [NNReal.coe_one,one_mul,Subtype.dist_eq,Real.dist_eq,intervalClamp] using h

theorem symmetric_clamp_abs_bound (K : ℝ) (hK : 0 ≤ K) (x : ℝ) :
    |intervalClamp (-K) K (by linarith) x| ≤ K := by
  exact abs_le.mpr (intervalClamp_mem (-K) K (by linarith) x)

end Asakura.Chapter3Complete
#print axioms Asakura.Chapter3Complete.stopped_partition_increment_bound
#print axioms Asakura.Chapter3Complete.stopped_interval_oscillation
#print axioms Asakura.Chapter3Complete.interval_clamp_abs_sub_le
#print axioms Asakura.Chapter3Complete.symmetric_clamp_abs_bound
