import Mathlib.Analysis.Calculus.LHopital
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.Analysis.Calculus.ContDiff.Operations

open Set Filter
open scoped Topology
namespace Asakura.Chapter5
set_option maxHeartbeats 2400000

/-- Continuous matching of the first derivative across a single time
boundary gives a derivative there. No differentiability at the boundary
is assumed. -/
theorem derivative_across_zero (f d : ℝ → ℝ)
    (hc : ContinuousAt f 0) (hdc : ContinuousAt d 0)
    (hd : ∀ t, t≠0 → HasDerivAt f (d t) t) : HasDerivAt f (d 0) 0 := by
  have hdf : ∀ᶠ t in 𝓝[≠] (0:ℝ), HasDerivAt (fun s => f s-f 0) (d t) t := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact (hd t ht).sub_const _
  have hh := HasDerivAt.lhopital_zero_nhdsNE hdf
    (Eventually.of_forall fun t => hasDerivAt_id t)
    (Eventually.of_forall fun _ => one_ne_zero)
    (by simpa using (hc.tendsto.mono_left nhdsWithin_le_nhds).sub_const (f 0))
    (by simpa using (tendsto_id : Tendsto (fun t : ℝ => t) (𝓝[≠] 0) (𝓝[≠] 0)).mono_right nhdsWithin_le_nhds)
    (by simpa only [div_one] using hdc.tendsto.mono_left nhdsWithin_le_nhds)
  rw [hasDerivAt_iff_tendsto_slope]
  change Tendsto (fun x => slope f 0 x) (𝓝[≠] (0:ℝ)) (𝓝 (d 0))
  simpa only [slope_def_field,sub_zero,id_eq] using hh

/-- Matching continuous partial derivatives give the actual total
Fréchet derivative used in the Ito formula. -/
theorem two_variable_derivative (f dt dx : ℝ × ℝ → ℝ)
    (ht : ∀ t x,HasDerivAt (fun s => f (s,x)) (dt (t,x)) t)
    (hx : ∀ t x,HasDerivAt (fun y => f (t,y)) (dx (t,x)) x)
    (hdt : Continuous dt) (hdx : Continuous dx) (p : ℝ × ℝ) :
    HasFDerivAt f
      (((ContinuousLinearMap.id ℝ ℝ).smulRight (dt p)).coprod
        ((ContinuousLinearMap.id ℝ ℝ).smulRight (dx p))) p := by
  exact (hasStrictFDerivAt_uncurry_coprod
    (f := fun t x => f (t,x))
    (f₁ := fun t x => ContinuousLinearMap.toSpanSingleton ℝ (dt (t,x)))
    (f₂ := fun t x => ContinuousLinearMap.toSpanSingleton ℝ (dx (t,x)))
    (Eventually.of_forall fun q => (ht q.1 q.2).hasFDerivAt)
    (Eventually.of_forall fun q => (hx q.1 q.2).hasFDerivAt)
    (((ContinuousLinearMap.toSpanSingletonLIE ℝ ℝ).continuous.comp hdt).continuousAt)
    (((ContinuousLinearMap.toSpanSingletonLIE ℝ ℝ).continuous.comp hdx).continuousAt)).hasFDerivAt

end Asakura.Chapter5
