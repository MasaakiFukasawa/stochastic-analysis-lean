import Chapter2LocalLpCompleteness
import Chapter2CountableMetric

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter2Complete
open Asakura.FullAudit
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false

noncomputable def localLpDistance {S : Type*} [MeasurableSpace S]
    (μ : Measure S) (p : ℝ≥0∞) [Fact (1 ≤ p)] (K : ℕ → Set S)
    (f g : S → ℝ) (hf : ∀ j, MemLp f p (μ.restrict (K j)))
    (hg : ∀ j, MemLp g p (μ.restrict (K j))) : ℝ :=
  countableDistance (fun j => (hf j).toLp f) (fun j => (hg j).toLp g)

/-- This is the geometric-series distance of the manuscript, expressed
through the actual Lp norms of restricted functions. -/
theorem local_lp_distance_formula {S : Type*} [MeasurableSpace S]
    (μ : Measure S) (p : ℝ≥0∞) [Fact (1 ≤ p)] (K : ℕ → Set S)
    (f g : S → ℝ) (hf : ∀ j, MemLp f p (μ.restrict (K j)))
    (hg : ∀ j, MemLp g p (μ.restrict (K j))) :
    localLpDistance μ p K f g hf hg =
      ∑' j, (1/2:ℝ)^(j+1)*min 1 (eLpNorm (f-g) p (μ.restrict (K j))).toReal := by
  apply tsum_congr
  intro j
  rw [dist_edist,Lp.edist_toLp_toLp]

/-- Completeness is proved for the printed series distance itself, not
merely for a chosen increasing coordinate family. The measurable sets K_j
are arbitrary and may have infinite measure. -/
theorem local_lp_series_cauchy_complete
    {S : Type*} [MeasurableSpace S] (μ : Measure S) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (K : ℕ → Set S) (hK : ∀ j, MeasurableSet (K j))
    (f : ℕ → S → ℝ) (hf : ∀ n j, MemLp (f n) p (μ.restrict (K j)))
    (hC : ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ m ≥ N,
      localLpDistance μ p K (f n) (f m) (hf n) (hf m) < ε) :
    ∃ g : S → ℝ, Measurable g ∧ ∃ hg : ∀ j, MemLp g p (μ.restrict (K j)),
      Tendsto (fun n => localLpDistance μ p K (f n) g (hf n) hg) atTop (𝓝 0) := by
  have hcoords := countable_distance_cauchy_coordinates (fun n j => (hf n j).toLp (f n)) hC
  obtain ⟨g,hgm,hg⟩ := local_lp_cauchy_limit μ p K hK f hf hcoords
  choose hgi hlim using hg
  exact ⟨g,hgm,hgi,countable_distance_of_coordinate_limits
    (fun n j => (hf n j).toLp (f n)) (fun j => (hgi j).toLp g) hlim⟩

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.local_lp_series_cauchy_complete
