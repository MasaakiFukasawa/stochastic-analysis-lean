import Chapter12BanachArrayNorm
import Mathlib.Analysis.Normed.Operator.Basic

namespace Asakura.Chapter12
set_option maxHeartbeats 1400000

theorem array_linear_bound {I E F : Type*} [Fintype I]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (A : E →L[ℝ] F) (U : I → E) :
    Real.sqrt (∑i,‖A (U i)‖^2) ≤ ‖A‖*Real.sqrt (∑i,‖U i‖^2) := by
  have hh : (∑i,‖A (U i)‖^2)≤‖A‖^2*∑i,‖U i‖^2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _) (A.le_opNorm (U i)) 2
  apply (Real.sqrt_le_sqrt hh).trans_eq
  rw [Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq (norm_nonneg _)]

theorem array_add_norm_bound {I E : Type*} [Fintype I] [NormedAddCommGroup E]
    (U V : I → E) :
    Real.sqrt (∑i,‖U i+V i‖^2)≤Real.sqrt (∑i,‖U i‖^2)+Real.sqrt (∑i,‖V i‖^2) := by
  let u : PiLp 2 (fun _ : I => E) := WithLp.toLp 2 U
  let v : PiLp 2 (fun _ : I => E) := WithLp.toLp 2 V
  have he : WithLp.toLp 2 (fun i => U i+V i)=u+v := rfl
  rw [←banach_array_norm,he]
  simpa only [u,v,banach_array_norm] using norm_add_le u v
end Asakura.Chapter12
#print axioms Asakura.Chapter12.array_linear_bound
