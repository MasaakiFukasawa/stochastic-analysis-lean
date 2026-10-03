import Chapter12HigherDerivativeLipschitz

open Set
open scoped ContDiff
namespace Asakura.Chapter12
set_option maxHeartbeats 1800000

theorem polynomial_derivative_difference {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E → F) (hf : ContDiff ℝ ∞ f) (k a : ℕ) (C : ℝ) (hC : 0≤C)
    (hb : ∀z,‖iteratedFDeriv ℝ (k+1) f z‖≤C*(1+‖z‖)^a) (x y : E) :
    ‖iteratedFDeriv ℝ k f x-iteratedFDeriv ℝ k f y‖≤
      C*(1+‖x‖+‖y‖)^a*‖x-y‖ := by
  let R := ‖x‖+‖y‖
  have hx : x∈Metric.closedBall (0:E) R := by
    simpa only [Metric.mem_closedBall,dist_zero_right,R] using le_add_of_nonneg_right (norm_nonneg y)
  have hy : y∈Metric.closedBall (0:E) R := by
    simpa only [Metric.mem_closedBall,dist_zero_right,R] using le_add_of_nonneg_left (norm_nonneg x)
  have hd z : DifferentiableAt ℝ (iteratedFDeriv ℝ k f) z :=
    hf.contDiffAt.differentiableAt_iteratedFDeriv (m:=k) (by exact_mod_cast ENat.natCast_lt_top k)
  have hder z (hz : z∈Metric.closedBall (0:E) R) :
      ‖fderiv ℝ (iteratedFDeriv ℝ k f) z‖≤C*(1+R)^a := by
    rw [norm_fderiv_iteratedFDeriv]
    apply (hb z).trans
    apply mul_le_mul_of_nonneg_left _ hC
    apply pow_le_pow_left₀ (by positivity)
    have hz' : ‖z‖≤R := by simpa only [Metric.mem_closedBall,dist_zero_right] using hz
    linarith
  have he := (convex_closedBall (0:E) R).norm_image_sub_le_of_norm_fderiv_le
    (fun z _ => hd z) hder hy hx
  simpa only [R,←add_assoc] using he
end Asakura.Chapter12
#print axioms Asakura.Chapter12.polynomial_derivative_difference
