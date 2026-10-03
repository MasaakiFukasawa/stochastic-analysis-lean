import Chapter2IntegrandMetricLimit
import Chapter2PathMetricSeparation

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter2Complete
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

/-- Probability convergence uniformly on each compact stage gives
convergence for the manuscript's local-uniform expectation metric. -/
theorem path_metric_limit_of_probability
    {Ω D : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    [TopologicalSpace D] [T2Space D] [LocallyCompactSpace D] [SecondCountableTopology D]
    (K : CompactExhaustion D) (X Y : ℕ → Ω → C(D,ℝ))
    (hX : ∀ n, Measurable (X n)) (hY : ∀ n, Measurable (Y n))
    (hp : ∀ j (ε : ℝ), 0 < ε →
      Tendsto (fun n => P {ω | ε ≤ compactStageDist K j (X n ω) (Y n ω)}) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ ω, pathDistance K (X n ω) (Y n ω) ∂P) atTop (𝓝 0) := by
  have h := expected_integrand_metric_limit P (fun n j ω => compactStageDist K j (X n ω) (Y n ω))
    (fun n j => compact_stage_distance_measurable K (X n) (Y n) (hX n) (hY n) j)
    (fun n j ω => compact_stage_distance_nonneg K j (X n ω) (Y n ω)) 1 zero_lt_one hp
  simpa only [div_one,Real.rpow_one,pathDistance] using h

/-- Failure of the Cauchy condition selects two tail subsequences with
errors uniformly bounded away from zero. This criterion avoids silently
assuming uniformity in the two approximation indices. -/
theorem cauchy_bound_of_all_tail_sequences
    (R : ℕ → ℕ → ℝ)
    (h : ∀ a b : ℕ → ℕ, (∀ n, n ≤ a n) → (∀ n, n ≤ b n) →
      Tendsto (fun n => R (a n) (b n)) atTop (𝓝 0)) :
    ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ m ≥ N, R n m < ε := by
  classical
  intro ε hε
  by_contra hh
  push_neg at hh
  choose a ha b hb hbad using hh
  have hl := h a b ha hb
  obtain ⟨n,hn⟩ := (hl.eventually (gt_mem_nhds hε)).exists
  exact (not_lt_of_ge (hbad n)) hn

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.path_metric_limit_of_probability
#print axioms Asakura.Chapter2Complete.cauchy_bound_of_all_tail_sequences
