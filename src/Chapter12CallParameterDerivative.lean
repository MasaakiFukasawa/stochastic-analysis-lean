import Chapter12MalliavinC1Chain
import Mathlib.Analysis.Calculus.ParametricIntegral

open MeasureTheory Set Filter
open scoped Topology NNReal
namespace Asakura.Chapter12
set_option maxHeartbeats 1400000

theorem call_parameter_derivative (F : ℝ → ℝ) (d θ K : ℝ)
    (hF : HasDerivAt F d θ) (hK : F θ ≠ K) :
    HasDerivAt (fun a => max (F a-K) 0) ((if K < F θ then 1 else 0)*d) θ := by
  rcases lt_or_gt_of_ne hK with hlt | hgt
  · have he : (fun a => max (F a-K) 0) =ᶠ[𝓝 θ] fun _ => (0:ℝ) := by
      have h := hF.continuousAt (gt_mem_nhds hlt)
      filter_upwards [h] with a ha
      exact max_eq_right (sub_nonpos.mpr ha.le)
    simpa only [not_lt.mpr hlt.le,ite_false,zero_mul] using (hasDerivAt_const θ (0:ℝ)).congr_of_eventuallyEq he
  · have he : (fun a => max (F a-K) 0) =ᶠ[𝓝 θ] fun a => F a-K := by
      have h := hF.continuousAt (lt_mem_nhds hgt)
      filter_upwards [h] with a ha
      exact max_eq_left (sub_nonneg.mpr ha.le)
    simpa only [hgt,ite_true,one_mul] using (hF.sub_const K).congr_of_eventuallyEq he

theorem call_payoff_lipschitz (K : ℝ) : LipschitzWith 1 (fun x : ℝ => max (x-K) 0) := by
  have h : LipschitzWith 1 (fun x : ℝ => x-K) := by
    apply lipschitzWith_iff_dist_le_mul.mpr
    intro x y
    have he : (x-K)-(y-K) = x-y := by ring
    simp [Real.dist_eq,he]
  exact h.max_const 0

end Asakura.Chapter12
