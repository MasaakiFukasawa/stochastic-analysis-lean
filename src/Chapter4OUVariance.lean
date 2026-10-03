import FullAuditOUKernel

open MeasureTheory Set
open scoped NNReal
namespace Asakura.Chapter4
open Asakura.FullAudit
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

lemma ou_scaled_integral_variance (κ σ R : ℝ) (hκ : 0<κ) :
    (Real.exp (-κ*R))^2*(∫ r in 0..R,(σ*Real.exp (κ*r))^2)=
      σ^2*(1-Real.exp (-2*κ*R))/(2*κ) := by
  rw [←intervalIntegral.integral_const_mul]
  calc
    (∫ r in 0..R,Real.exp (-κ*R)^2*(σ*Real.exp (κ*r))^2)=
        ∫ r in 0..R,σ^2*Real.exp (-2*κ*(R-r)) := by
      apply intervalIntegral.integral_congr
      intro r _
      dsimp only
      rw [mul_pow,mul_left_comm,pow_two (Real.exp _),pow_two (Real.exp _),mul_assoc,
        ←Real.exp_add,←Real.exp_add,←Real.exp_add]
      congr 2
      ring
    _ = _ := ou_kernel_variance_integral κ σ R hκ

end Asakura.Chapter4
