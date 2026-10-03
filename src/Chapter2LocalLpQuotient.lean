import Chapter2LocalLpMetric
import Mathlib.Topology.MetricSpace.Cauchy

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter2Complete
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false

theorem countable_distance_self {E : ℕ → Type*} [∀ j, PseudoMetricSpace (E j)]
    (x : ∀ j, E j) : countableDistance x x = 0 := by simp [countableDistance]

theorem countable_distance_comm {E : ℕ → Type*} [∀ j, PseudoMetricSpace (E j)]
    (x y : ∀ j, E j) : countableDistance x y = countableDistance y x := by
  simp only [countableDistance,dist_comm]

theorem countable_distance_triangle {E : ℕ → Type*} [∀ j, MetricSpace (E j)]
    (x y z : ∀ j, E j) : countableDistance x z ≤ countableDistance x y + countableDistance y z := by
  rw [countableDistance,countableDistance,countableDistance,← Summable.tsum_add
    (countable_distance_summable x y) (countable_distance_summable y z)]
  apply (countable_distance_summable x z).tsum_le_tsum _
    ((countable_distance_summable x y).add (countable_distance_summable y z))
  intro j
  rw [← mul_add]
  exact mul_le_mul_of_nonneg_left (truncated_distance_triangle (x j) (y j) (z j)) (by positivity)

theorem countable_distance_convergence_iff {E : ℕ → Type*} [∀ j, PseudoMetricSpace (E j)]
    (x : ℕ → ∀ j, E j) (y : ∀ j, E j) :
    Tendsto (fun n => countableDistance (x n) y) atTop (𝓝 0) ↔
      ∀ j, Tendsto (fun n => x n j) atTop (𝓝 (y j)) := by
  refine ⟨?_,countable_distance_of_coordinate_limits x y⟩
  intro h j
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  have he : 0 < (1/2:ℝ)^(j+1)*min 1 ε := mul_pos (by positivity) (lt_min zero_lt_one hε)
  obtain ⟨N,hN⟩ := eventually_atTop.1 (h.eventually (gt_mem_nhds he))
  exact ⟨N,fun n hn => countable_distance_coordinate_lt (x n) y j ε (hN n hn)⟩

theorem countable_distance_zero_iff {E : ℕ → Type*} [∀ j, MetricSpace (E j)]
    (x y : ∀ j, E j) : countableDistance x y = 0 ↔ x = y := by
  refine ⟨?_,fun h => h ▸ countable_distance_self x⟩
  intro h
  funext j
  apply dist_eq_zero.mp
  have he := countable_distance_controls_coordinate x y j
  rw [h] at he
  have hw : 0 < (1/2:ℝ)^(j+1) := by positivity
  have hmin : min 1 (dist (x j) (y j)) ≤ 0 := by nlinarith
  have hd : dist (x j) (y j) ≤ 0 := (min_le_iff.mp hmin).resolve_left (by norm_num)
  exact le_antisymm hd dist_nonneg

/-- Raw locally Lp functions, before the manuscript's distance-zero identification. -/
def LocalLpFunctions {S : Type*} [MeasurableSpace S]
    (μ : Measure S) (p : ℝ≥0∞) (K : ℕ → Set S) :=
  { f : S → ℝ // ∀ j, MemLp f p (μ.restrict (K j)) }

noncomputable instance localLpPseudoMetric {S : Type*} [MeasurableSpace S]
    (μ : Measure S) (p : ℝ≥0∞) [Fact (1 ≤ p)] (K : ℕ → Set S) :
    PseudoMetricSpace (LocalLpFunctions μ p K) where
  dist f g := localLpDistance μ p K f.val g.val f.property g.property
  dist_self f := countable_distance_self _
  dist_comm f g := countable_distance_comm _ _
  dist_triangle f g h := countable_distance_triangle _ _ _

theorem local_lp_complete_space {S : Type*} [MeasurableSpace S]
    (μ : Measure S) (p : ℝ≥0∞) [Fact (1 ≤ p)] (K : ℕ → Set S)
    (hK : ∀ j, MeasurableSet (K j)) : CompleteSpace (LocalLpFunctions μ p K) := by
  apply Metric.complete_of_cauchySeq_tendsto
  intro u hu
  obtain ⟨g,hgm,hg,hlim⟩ := local_lp_series_cauchy_complete μ p K hK
    (fun n => (u n).val) (fun n => (u n).property) (Metric.cauchySeq_iff.mp hu)
  exact ⟨⟨g,hg⟩,tendsto_iff_dist_tendsto_zero.mpr hlim⟩

/-- The manuscript's actual quotient by zero series distance is complete. -/
theorem local_lp_quotient_complete {S : Type*} [MeasurableSpace S]
    (μ : Measure S) (p : ℝ≥0∞) [Fact (1 ≤ p)] (K : ℕ → Set S)
    (hK : ∀ j, MeasurableSet (K j)) :
    CompleteSpace (SeparationQuotient (LocalLpFunctions μ p K)) := by
  letI := local_lp_complete_space μ p K hK
  infer_instance

theorem local_lp_convergence_iff {S : Type*} [MeasurableSpace S]
    (μ : Measure S) (p : ℝ≥0∞) [Fact (1 ≤ p)] (K : ℕ → Set S)
    (u : ℕ → LocalLpFunctions μ p K) (v : LocalLpFunctions μ p K) :
    Tendsto u atTop (𝓝 v) ↔ ∀ j,
      Tendsto (fun n => ((u n).property j).toLp (u n).val) atTop
        (𝓝 ((v.property j).toLp v.val)) := by
  rw [tendsto_iff_dist_tendsto_zero]
  exact countable_distance_convergence_iff _ _

/-- Under a countable cover, the manuscript's zero-distance convention is
exactly equality almost everywhere for the original measure. -/
theorem local_lp_distance_zero_iff_ae {S : Type*} [MeasurableSpace S]
    (μ : Measure S) (p : ℝ≥0∞) [Fact (1 ≤ p)] (K : ℕ → Set S)
    (hcover : ⋃ j, K j = univ) (f g : LocalLpFunctions μ p K) :
    dist f g = 0 ↔ f.val =ᵐ[μ] g.val := by
  change countableDistance _ _ = 0 ↔ _
  rw [countable_distance_zero_iff]
  constructor
  · intro h
    have hj j : f.val =ᵐ[μ.restrict (K j)] g.val :=
      ((f.property j).toLp_eq_toLp_iff (g.property j)).mp (congrFun h j)
    have hh := (ae_restrict_iUnion_iff K (fun x => f.val x = g.val x)).mpr hj
    rw [hcover,Measure.restrict_univ] at hh
    exact hh
  · intro h
    funext j
    exact ((f.property j).toLp_eq_toLp_iff (g.property j)).mpr
      (ae_mono Measure.restrict_le_self h)

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.local_lp_quotient_complete
#print axioms Asakura.Chapter2Complete.local_lp_convergence_iff
