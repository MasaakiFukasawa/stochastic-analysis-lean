import AppendixWrittenBorelCantelli
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Topology.Algebra.InfiniteSum.Real

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter2Complete
set_option maxHeartbeats 700000

/-- The Borel-Cantelli step of the completeness argument: summable
exception probabilities and summable increment bounds give pathwise limits
in each complete space of continuous functions on a compact interval. -/
theorem random_summable_increment_limit
    {Ω E : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [MetricSpace E] [CompleteSpace E] (X : ℕ → Ω → E)
    (d : ℕ → ℝ) (hd : Summable d)
    (hm : ∀ n, MeasurableSet {ω | d n < dist (X n ω) (X (n+1) ω)})
    (hs : (∑' n, P {ω | d n < dist (X n ω) (X (n+1) ω)}) < ∞) :
    ∀ᵐ ω ∂P, ∃ y : E, Tendsto (fun n => X n ω) atTop (𝓝 y) := by
  filter_upwards [Asakura.written_borel_cantelli P
    (fun n => {ω | d n < dist (X n ω) (X (n+1) ω)}) hm hs] with ω hω
  obtain ⟨N,hN⟩ := hω.bddAbove
  have he : ∀ᶠ n in atTop, ‖dist (X n ω) (X (n+1) ω)‖ ≤ d n := by
    filter_upwards [eventually_gt_atTop N] with n hn
    rw [Real.norm_eq_abs,abs_of_nonneg dist_nonneg]
    by_contra h
    exact not_le_of_gt hn (hN (not_le.1 h))
  have hsum : Summable (fun n => dist (X n ω) (X (n+1) ω)) := hd.of_norm_bounded_eventually_nat he
  exact cauchySeq_tendsto_of_complete (cauchySeq_of_summable_dist hsum)

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.random_summable_increment_limit
