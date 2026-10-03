import Chapter12SquaredGaussianKernel
import Mathlib.Topology.Algebra.Order.Field

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

theorem squared_gaussian_density_unbounded_at_zero (T : ℝ≥0) (hT : 0<T) :
    Tendsto (squaredGaussianDensity T) (𝓝[>] (0:ℝ)) atTop := by
  have hC : 0<2*Real.pi*(T:ℝ) := by positivity
  have hcont : ContinuousAt (fun x : ℝ => Real.sqrt (2*Real.pi*(T:ℝ)*x)) 0 := by fun_prop
  have hs0 : Tendsto (fun x : ℝ => Real.sqrt (2*Real.pi*(T:ℝ)*x))
      (𝓝[>] (0:ℝ)) (𝓝 (0:ℝ)) := by
    simpa only [mul_zero,Real.sqrt_zero] using hcont.tendsto.mono_left nhdsWithin_le_nhds
  have hs : Tendsto (fun x : ℝ => Real.sqrt (2*Real.pi*(T:ℝ)*x))
      (𝓝[>] (0:ℝ)) (𝓝[>] (0:ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨hs0,?_⟩
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact Real.sqrt_pos.mpr (mul_pos hC hx)
  have hi := tendsto_inv_nhdsGT_zero.comp hs
  have hec : ContinuousAt (fun x : ℝ => Real.exp (-x/(2*(T:ℝ)))) 0 := by fun_prop
  have he : Tendsto (fun x : ℝ => Real.exp (-x/(2*(T:ℝ)))) (𝓝[>] (0:ℝ)) (𝓝 (1:ℝ)) := by
    simpa only [neg_zero,zero_div,Real.exp_zero] using hec.tendsto.mono_left nhdsWithin_le_nhds
  apply (hi.atTop_mul_pos zero_lt_one he).congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  exact (if_pos hx).symm

theorem squared_gaussian_density_not_continuous_at_zero (T : ℝ≥0) (hT : 0<T) :
    ¬ContinuousAt (squaredGaussianDensity T) 0 := by
  intro hc
  exact not_tendsto_nhds_of_tendsto_atTop (squared_gaussian_density_unbounded_at_zero T hT) _
    (hc.tendsto.mono_left nhdsWithin_le_nhds)

end Asakura.Chapter12
