import Chapter12BanachArrayNorm
import Mathlib.Analysis.InnerProductSpace.Orthonormal

open scoped BigOperators RealInnerProductSpace
namespace Asakura.Chapter12
set_option maxHeartbeats 1800000

theorem orthonormal_kernel_array_bound {I H E : Type*} [Fintype I]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (e : I → H) (he : Orthonormal ℝ e) (h : H) (v : E) :
    Real.sqrt (∑i,‖inner ℝ (e i) h • v‖^2)≤‖v‖*‖h‖ := by
  have hb : Real.sqrt (∑i,‖inner ℝ (e i) h‖^2)≤‖h‖ := by
    simpa only [Real.sqrt_sq (norm_nonneg h)] using Real.sqrt_le_sqrt (he.sum_inner_products_le (s:=Finset.univ) h)
  calc
    _ = Real.sqrt (‖v‖^2*(∑i,‖inner ℝ (e i) h‖^2)) := by
      congr 1
      simp only [norm_smul,mul_pow,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      exact mul_comm _ _
    _ = ‖v‖*Real.sqrt (∑i,‖inner ℝ (e i) h‖^2) := by
      rw [Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq (norm_nonneg _)]
    _ ≤ ‖v‖*‖h‖ := mul_le_mul_of_nonneg_left hb (norm_nonneg _)

theorem hilbert_kernel_array_bound {I J H E : Type*} [Fintype I] [Fintype J]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (e : I → H) (he : Orthonormal ℝ e) (h : J → H) (v : J → E) :
    Real.sqrt (∑i,‖∑j,inner ℝ (e i) (h j) • v j‖^2)≤∑j,‖v j‖*‖h j‖ := by
  apply (banach_array_norm_sum (fun j i => inner ℝ (e i) (h j) • v j)).trans
  exact Finset.sum_le_sum (fun j _ => orthonormal_kernel_array_bound e he (h j) (v j))
end Asakura.Chapter12
#print axioms Asakura.Chapter12.hilbert_kernel_array_bound
