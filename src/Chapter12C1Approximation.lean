import Chapter12SmoothPrimitive
import Mathlib.MeasureTheory.Integral.DominatedConvergence

open MeasureTheory Set Filter
open scoped ContDiff Topology
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

/-- Smooth polynomial-growth approximations to a C1 function with bounded
derivative. Both the values and derivatives converge, and the derivative
bound is uniform in the approximation index. -/
theorem bounded_C1_smooth_approximation (f df : ℝ → ℝ)
    (hd : ∀ x, HasDerivAt f (df x) x) (hdc : Continuous df)
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ x, |df x| ≤ C) :
    ∃ g dg : ℕ → ℝ → ℝ,
      (∀ n, ContDiff ℝ ∞ (g n)) ∧
      (∀ n x, HasDerivAt (g n) (dg n x) x) ∧
      (∀ n x, |dg n x| ≤ 3*C) ∧
      (∀ n x, |g n x| ≤ |f 0|+3*C*|x|) ∧
      (∀ n k, ∃ K : ℝ, 0 ≤ K ∧ ∃ a : ℕ, ∀ x,
        ‖iteratedFDeriv ℝ k (g n) x‖ ≤ K*(1+‖x‖)^a) ∧
      (∀ x, Tendsto (fun n => g n x) atTop (𝓝 (f x))) ∧
      (∀ x, Tendsto (fun n => dg n x) atTop (𝓝 (df x))) := by
  obtain ⟨dg,hdg,hbound,ht⟩ := bounded_continuous_compact_smooth_approximation df hdc C hC hb
  let g := fun n => smoothPrimitive (f 0) (dg n)
  refine ⟨g,dg,fun n => smoothPrimitive_smooth _ _ (hdg n).1,
    fun n x => smoothPrimitive_hasDerivAt _ _ (hdg n).1.continuous x,hbound,
    fun n x => smoothPrimitive_linear_bound _ _ _ (hbound n) x,
    fun n k => smoothPrimitive_all_derivatives_growth _ _ (hdg n).1 (hdg n).2 k,?_,ht⟩
  intro x
  have htI (a b : ℝ) : Tendsto (fun n => ∫ t in Ioc a b,dg n t) atTop (𝓝 (∫ t in Ioc a b,df t)) :=
    tendsto_integral_of_dominated_convergence (fun _ => 3*C)
      (fun n => (hdg n).1.continuous.aestronglyMeasurable)
      (integrable_const _) (fun n => ae_of_all _ (hbound n)) (ae_of_all _ ht)
  have htint : Tendsto (fun n => ∫ t in 0..x,dg n t) atTop (𝓝 (∫ t in 0..x,df t)) := by
    unfold intervalIntegral
    exact (htI 0 x).sub (htI x 0)
  have he : f 0+(∫ t in 0..x,df t)=f x := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t) (hdc.intervalIntegrable _ _)]
    ring
  simpa only [g,smoothPrimitive,he] using (tendsto_const_nhds (x := f 0)).add htint

end Asakura.Chapter12
