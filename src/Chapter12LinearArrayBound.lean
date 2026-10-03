import Chapter12BanachArrayNorm
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Tactic.Positivity

open scoped BigOperators
namespace Asakura.Chapter12

theorem linear_array_bound {I E F : Type*} [Fintype I]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : E →L[ℝ] F) (u : I → E) :
    Real.sqrt (∑i,‖L (u i)‖^2)≤‖L‖*Real.sqrt (∑i,‖u i‖^2) := by
  have hh : (∑i,‖L (u i)‖^2)≤‖L‖^2*(∑i,‖u i‖^2) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    calc
      ‖L (u i)‖^2 ≤ (‖L‖*‖u i‖)^2 := pow_le_pow_left₀ (norm_nonneg _) (L.le_opNorm _) 2
      _ = ‖L‖^2*‖u i‖^2 := mul_pow _ _ _
  calc
    _ ≤ Real.sqrt (‖L‖^2*(∑i,‖u i‖^2)) := Real.sqrt_le_sqrt hh
    _ = _ := by rw [Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq (norm_nonneg _)]
end Asakura.Chapter12
#print axioms Asakura.Chapter12.linear_array_bound
