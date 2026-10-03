import Chapter2PathMetric
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter2Complete
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

noncomputable def countableDistance {E : ℕ → Type*} [∀ j, PseudoMetricSpace (E j)]
    (x y : ∀ j, E j) : ℝ := ∑' j, (1/2:ℝ)^(j+1)*min 1 (dist (x j) (y j))

theorem countable_distance_summable {E : ℕ → Type*} [∀ j, PseudoMetricSpace (E j)]
    (x y : ∀ j, E j) : Summable (fun j => (1/2:ℝ)^(j+1)*min 1 (dist (x j) (y j))) :=
  Summable.of_nonneg_of_le (fun j => mul_nonneg (by positivity) (le_min zero_le_one dist_nonneg))
    (fun j => mul_le_of_le_one_right (by positivity) (min_le_left _ _)) path_weights_summable

theorem countable_distance_controls_coordinate {E : ℕ → Type*} [∀ j, PseudoMetricSpace (E j)]
    (x y : ∀ j, E j) (j : ℕ) :
    (1/2:ℝ)^(j+1)*min 1 (dist (x j) (y j)) ≤ countableDistance x y :=
  (countable_distance_summable x y).le_tsum j (fun k _ =>
    mul_nonneg (by positivity) (le_min zero_le_one dist_nonneg))

theorem countable_distance_coordinate_lt {E : ℕ → Type*} [∀ j, PseudoMetricSpace (E j)]
    (x y : ∀ j, E j) (j : ℕ) (ε : ℝ)
    (h : countableDistance x y < (1/2:ℝ)^(j+1)*min 1 ε) : dist (x j) (y j) < ε := by
  by_contra hn
  have hle := mul_le_mul_of_nonneg_left (min_le_min_left 1 (le_of_not_gt hn))
    (show 0 ≤ (1/2:ℝ)^(j+1) by positivity)
  exact (not_lt_of_ge (hle.trans (countable_distance_controls_coordinate x y j))) h

theorem countable_distance_cauchy_coordinates {E : ℕ → Type*} [∀ j, PseudoMetricSpace (E j)]
    (x : ℕ → ∀ j, E j)
    (hc : ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ m ≥ N, countableDistance (x n) (x m) < ε) :
    ∀ j, CauchySeq (fun n => x n j) := by
  intro j
  apply Metric.cauchySeq_iff.mpr
  intro ε hε
  obtain ⟨N,hN⟩ := hc ((1/2:ℝ)^(j+1)*min 1 ε) (mul_pos (by positivity) (lt_min zero_lt_one hε))
  exact ⟨N,fun n hn m hm => countable_distance_coordinate_lt (x n) (x m) j ε (hN n hn m hm)⟩

theorem countable_distance_of_coordinate_limits {E : ℕ → Type*} [∀ j, PseudoMetricSpace (E j)]
    (x : ℕ → ∀ j, E j) (y : ∀ j, E j)
    (hl : ∀ j, Tendsto (fun n => x n j) atTop (𝓝 (y j))) :
    Tendsto (fun n => countableDistance (x n) y) atTop (𝓝 0) := by
  have hj j : Tendsto (fun n => (1/2:ℝ)^(j+1)*min 1 (dist (x n j) (y j))) atTop (𝓝 0) := by
    have hd := (hl j).dist (tendsto_const_nhds : Tendsto (fun _ : ℕ => y j) atTop (𝓝 (y j)))
    have hmin := (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1:ℝ)) atTop (𝓝 1)).min hd
    simpa using hmin.const_mul ((1/2:ℝ)^(j+1))
  have hi n : Integrable (fun j => (1/2:ℝ)^(j+1)*min 1 (dist (x n j) (y j))) Measure.count :=
    integrable_count_iff.mpr (countable_distance_summable (x n) y).norm
  have hlim := tendsto_integral_of_dominated_convergence (μ := Measure.count)
    (fun j : ℕ => (1/2:ℝ)^(j+1)) (fun n => (hi n).aestronglyMeasurable)
    (integrable_count_iff.mpr path_weights_summable.norm)
    (fun n => ae_of_all _ (fun j => by
      rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (by positivity) (le_min zero_le_one dist_nonneg))]
      exact mul_le_of_le_one_right (by positivity) (min_le_left _ _)))
    (f := fun _ : ℕ => (0:ℝ)) (ae_of_all _ hj)
  have he n : (∫ j, (1/2:ℝ)^(j+1)*min 1 (dist (x n j) (y j)) ∂Measure.count) = countableDistance (x n) y := by
    rw [integral_countable (hi n)]
    simp [Measure.real,Measure.count_singleton,countableDistance]
  simpa only [he,integral_zero] using hlim

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.countable_distance_cauchy_coordinates
#print axioms Asakura.Chapter2Complete.countable_distance_of_coordinate_limits
