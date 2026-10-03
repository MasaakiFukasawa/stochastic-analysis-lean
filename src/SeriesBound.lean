import Appendix
import Mathlib.MeasureTheory.Function.LpSpace.InfiniteSum
import Mathlib.MeasureTheory.Constructions.Polish.Basic
open MeasureTheory Filter Set
open scoped Topology ENNReal BigOperators
namespace Asakura

/-- The good event used in Kolmogorov's construction is measurable. -/
theorem measurable_summability_event {Ω : Type*} [MeasurableSpace Ω]
    (f : ℕ → Ω → ℝ) (hf : ∀ n, Measurable (f n)) :
    MeasurableSet {ω | Summable (fun n => f n ω)} := by
  exact measurableSet_exists_tendsto (fun s : Finset ℕ =>
    Finset.measurable_sum s (fun i _ => hf i))

/-- C.2: the infinite Minkowski step and almost-sure finiteness.
This proves both claims from summability of the Lp norms. -/
theorem nonnegative_series_lp_bound {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (p : ℝ≥0∞) (hp : 1 ≤ p)
    (f : ℕ → Ω → ℝ) (hf : ∀ n, Measurable (f n))
    (hpos : ∀ n ω, 0 ≤ f n ω)
    (hfinite : ∑' n, eLpNorm (f n) p μ ≠ ∞) :
    (∀ᵐ ω ∂μ, Summable (fun n => f n ω)) ∧
    Measurable (fun ω => ∑' n, f n ω) ∧
    eLpNorm (fun ω => ∑' n, f n ω) p μ ≤ ∑' n, eLpNorm (f n) p μ := by
  have hae : ∀ᵐ ω ∂μ, Summable (fun n => f n ω) := by
    have h := summable_norm_of_tsum_eLpNorm_ne_top hp hfinite
    filter_upwards [h] with ω hω
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hpos _ _)] using hω
  have hm : Measurable (fun ω => ∑' n, f n ω) := Measurable.tsum hf
  refine ⟨hae, hm, ?_⟩
  apply Lp.eLpNorm_le_of_ae_tendsto (u := atTop) (f := fun N ω => ∑ n ∈ Finset.range N, f n ω)
  · apply Filter.Eventually.of_forall
    intro N
    have h := (eLpNorm_sum_le (μ := μ) (f := f) (s := Finset.range N) hp).trans
      (ENNReal.sum_le_tsum (Finset.range N))
    have heq : (fun ω => ∑ n ∈ Finset.range N, f n ω) = ∑ n ∈ Finset.range N, f n := by
      funext ω
      simp only [Finset.sum_apply]
    rw [heq]
    exact h
  · intro N
    exact (Finset.measurable_sum _ (fun n _ => hf n)).aestronglyMeasurable
  · exact hm.aestronglyMeasurable
  · filter_upwards [hae] with ω hω
    exact hω.hasSum.tendsto_sum_nat
end Asakura
