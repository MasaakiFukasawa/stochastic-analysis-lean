import Chapter4VectorVolterraLimit

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter4.Vector
variable {dim : ℕ}
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

lemma prefix_integral_le_full_moment
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (R : ℝ) (hR : 0≤R) (Y : Ω → C(Icc (0:ℝ) R,Fin dim → ℝ))
    (hm : Measurable Y) (hi : MemLp Y 2 P) :
    (∫ r in 0..R,(∫ w,‖prefixPath hR (Y w) r‖^2 ∂P))≤R*(∫ w,‖Y w‖^2 ∂P) := by
  have hn := hi.integrable_norm_pow (by norm_num : (2:ℕ)≠0)
  have hc := prefix_square_moment_continuous P hR Y hm hi
  have hb r : (∫ w,‖prefixPath hR (Y w) r‖^2 ∂P)≤∫ w,‖Y w‖^2 ∂P := by
    have hi' : Integrable (fun w => ‖prefixPath hR (Y w) r‖^2) P := by
      apply hn.mono' ((prefix_path_measurable hR Y hm r).norm.pow_const 2).aestronglyMeasurable
      apply Filter.Eventually.of_forall
      intro w
      simpa only [Real.norm_eq_abs,abs_sq] using
        (pow_le_pow_left₀ (norm_nonneg _) (prefix_path_norm_le hR (Y w) r) 2)
    exact integral_mono hi' hn (fun w => pow_le_pow_left₀ (norm_nonneg _) (prefix_path_norm_le hR (Y w) r) 2)
  have h := intervalIntegral.integral_mono_on (μ := volume) hR (hc.intervalIntegrable 0 R)
    (intervalIntegrable_const) (fun r _ => hb r)
  simpa only [intervalIntegral.integral_const,sub_zero,smul_eq_mul] using h


end Asakura.Chapter4.Vector
