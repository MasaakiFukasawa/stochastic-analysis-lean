import Chapter6WeightedStepIntegral
import Mathlib.MeasureTheory.Integral.DominatedConvergence

open MeasureTheory Set Filter Finset
open scoped Topology BigOperators
namespace Asakura.Chapter8
open Asakura.Chapter6
set_option maxHeartbeats 1000000

/-- Ordinary weighted left sums converge pathwise on a compact interval.
Neither function needs a deterministic global bound. -/
theorem continuous_weighted_riemann (R : ℝ) (hR : 0<R) (f g : ℝ → ℝ)
    (hf : Continuous f) (hg : Continuous g) :
    Tendsto (fun n : ℕ => ∑ k∈range (n+1),f ((k:ℝ)*(R/((n:ℝ)+1)))*
      ∫ r in (k:ℝ)*(R/((n:ℝ)+1))..((k:ℝ)+1)*(R/((n:ℝ)+1)),g r)
      atTop (𝓝 (∫ r in 0..R,f r*g r)) := by
  obtain ⟨K,hK⟩ := (isCompact_Icc (a := (0:ℝ)) (b := R)).exists_bound_of_continuousOn hf.continuousOn
  obtain ⟨L,hL⟩ := (isCompact_Icc (a := (0:ℝ)) (b := R)).exists_bound_of_continuousOn hg.continuousOn
  let ν := volume.restrict (Ioc (0:ℝ) R)
  have hm n : Measurable (fun r => uniformLeftStep R n f r*g r) := by
    apply Measurable.mul _ hg.measurable
    apply Finset.measurable_sum
    intro k _
    exact measurable_const.indicator measurableSet_Ioc
  have hb n : ∀ᵐ r ∂ν,‖uniformLeftStep R n f r*g r‖≤|K| *|L| := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    have hs := uniform_left_step_abs_le R hR n f |K|
      (fun s hs => (hK s hs).trans (le_abs_self K)) r hr
    rw [norm_mul,Real.norm_eq_abs (uniformLeftStep R n f r)]
    exact mul_le_mul hs ((hL r ⟨hr.1.le,hr.2⟩).trans (le_abs_self L)) (norm_nonneg _) (abs_nonneg _)
  have hl : ∀ᵐ r ∂ν,Tendsto (fun n => uniformLeftStep R n f r*g r) atTop (𝓝 (f r*g r)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    exact (uniform_left_step_pointwise R hR f hf.continuousOn r hr).mul_const _
  have hh := tendsto_integral_of_dominated_convergence (μ := ν) (fun _ => |K| *|L|)
    (fun n => (hm n).aestronglyMeasurable) (integrable_const _) hb hl
  dsimp only [ν] at hh
  simp_rw [uniform_weighted_step_integral R hR _ f g (hg.intervalIntegrable _ _)] at hh
  simpa only [intervalIntegral.integral_of_le hR.le] using hh
end Asakura.Chapter8
