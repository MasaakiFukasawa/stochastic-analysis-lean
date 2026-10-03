import Chapter5GaussianApproximation
import Chapter5ParameterizedHeat

open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal
namespace Asakura.Chapter5
open Asakura.FullAudit

/-- The joint endpoint limit for unbounded Lipschitz terminal data. -/
theorem heatAverage_lipschitz_endpoint_limit {ι : Type*} (l : Filter ι)
    (f : ℝ → ℝ) (K : ℝ≥0) (hf : LipschitzWith K f)
    (x : ℝ) (xs ts : ι → ℝ)
    (hx : Tendsto xs l (𝓝 x)) (ht : Tendsto ts l (𝓝 0)) :
    Tendsto (fun n => heatAverage f (xs n) (ts n)) l (𝓝 (f x)) := by
  have h1 : Tendsto (fun n => |xs n-x|) l (𝓝 0) := by
    simpa using (hx.sub_const x).abs
  have h2 : Tendsto (fun n => Real.sqrt (ts n)) l (𝓝 0) := by
    simpa only [Function.comp_def,Real.sqrt_zero] using Real.continuous_sqrt.continuousAt.tendsto.comp ht
  have hb : Tendsto (fun n => (K:ℝ)*(|xs n-x|+
      Real.sqrt (ts n)*(∫ z : ℝ, |z| ∂gaussianReal 0 1))) l (𝓝 0) := by
    simpa using (h1.add (h2.mul_const (∫ z : ℝ, |z| ∂gaussianReal 0 1))).const_mul (K:ℝ)
  have h := squeeze_zero (fun n => abs_nonneg (heatAverage f (xs n) (ts n)-f x))
    (fun n => heatAverage_endpoint_bound f K hf (xs n) x (ts n)) hb
  apply tendsto_iff_dist_tendsto_zero.mpr
  simpa only [Real.dist_eq] using h

/-- Space differentiation requires a bounded derivative, not a bounded
payoff. This is the form needed by the printed representation lemma. -/
theorem heatAverage_space_derivative_lipschitz (f df : ℝ → ℝ) (K : ℝ≥0)
    (hl : LipschitzWith K f) (hd : ∀ x, HasDerivAt f (df x) x)
    (hdf : Continuous df) (D : ℝ) (hb : ∀ x, ‖df x‖ ≤ D) (x t : ℝ) :
    HasDerivAt (fun y => heatAverage f y t) (heatAverage df x t) x := by
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := gaussianReal 0 1) (s := Set.univ) (bound := fun _ => D)
    (F' := fun y z => df (y+Real.sqrt t*z))
    (Filter.univ_mem) ?_ ?_ ?_ ?_ (integrable_const D) ?_).2
  · exact Eventually.of_forall fun y => (hl.continuous.comp (by fun_prop)).aestronglyMeasurable
  · exact heatAverage_integrable_lipschitz f K hl x t
  · exact (hdf.comp (by fun_prop)).aestronglyMeasurable
  · exact ae_of_all _ fun z y _ => hb _
  · exact ae_of_all _ fun z y _ => by
      simpa only [mul_one,Function.comp_def,id_eq] using
        (hd (y+Real.sqrt t*z)).comp y ((hasDerivAt_id y).add_const (Real.sqrt t*z))

end Asakura.Chapter5
