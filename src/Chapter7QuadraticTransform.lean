import Chapter7CovarianceMatrixAlgebra

open Matrix Finset
open scoped BigOperators
namespace Asakura.Chapter7
set_option maxHeartbeats 1000000

lemma quadratic_sum_dot {d : ℕ} (H : Matrix (Fin d) (Fin d) ℝ) (x : Fin d → ℝ) :
    (∑ i,∑ j,H i j*x i*x j)=dotProduct x (H.mulVec x) := by
  simp only [dotProduct,Matrix.mulVec,Finset.mul_sum]
  apply sum_congr rfl
  intro i _
  apply sum_congr rfl
  intro j _
  ring

lemma quadratic_transform {d : ℕ} (H S : Matrix (Fin d) (Fin d) ℝ) (x : Fin d → ℝ) :
    (∑ i,∑ j,H i j*(S.mulVec x) i*(S.mulVec x) j)=
      ∑ i,∑ j,(S.transpose*H*S) i j*x i*x j := by
  rw [quadratic_sum_dot,quadratic_sum_dot]
  calc
    _ = dotProduct x (S.transpose.mulVec (H.mulVec (S.mulVec x))) := by
      rw [Matrix.dotProduct_mulVec x S.transpose (H.mulVec (S.mulVec x)),Matrix.vecMul_transpose]
    _ = _ := by simp only [Matrix.mulVec_mulVec,Matrix.mul_assoc]

lemma covariance_trace_transform {d : ℕ} (H S : Matrix (Fin d) (Fin d) ℝ) :
    Matrix.trace (H*(S*S.transpose))=Matrix.trace (S.transpose*H*S) := by
  rw [← Matrix.mul_assoc,Matrix.trace_mul_comm (H*S) S.transpose,Matrix.mul_assoc]

lemma quadratic_transform_symmetric {d : ℕ} (H S : Matrix (Fin d) (Fin d) ℝ)
    (hH : H.transpose=H) : (S.transpose*H*S).transpose=S.transpose*H*S := by
  rw [Matrix.transpose_mul,Matrix.transpose_mul,Matrix.transpose_transpose,hH]
  exact (Matrix.mul_assoc S.transpose H S).symm

end Asakura.Chapter7
