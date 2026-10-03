import Mathlib.LinearAlgebra.Matrix.Trace
import Chapter7GaussianFourthMoment
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

open Matrix
open scoped BigOperators
namespace Asakura.Chapter7

/-- The variance parameter in the matrix estimator CLT is nonnegative,
including singular diffusion matrices. -/
theorem covariance_trace_square {d : ℕ} (H S : Matrix (Fin d) (Fin d) ℝ)
    (hH : H.transpose=H) :
    Matrix.trace (H*(S*S.transpose)*H*(S*S.transpose)) =
      ∑ i,∑ j,(S.transpose*H*S) i j^2 := by
  let K := S.transpose*H*S
  have hk : K.transpose=K := by
    dsimp [K]
    rw [Matrix.transpose_mul,Matrix.transpose_mul,Matrix.transpose_transpose,hH]
    exact (Matrix.mul_assoc S.transpose H S).symm
  have he : Matrix.trace (H*(S*S.transpose)*H*(S*S.transpose))=Matrix.trace (K*K) := by
    dsimp [K]
    calc
      _ = Matrix.trace ((H*S*S.transpose*H*S)*S.transpose) := by simp only [Matrix.mul_assoc]
      _ = Matrix.trace (S.transpose*(H*S*S.transpose*H*S)) := Matrix.trace_mul_comm _ _
      _ = _ := by simp only [Matrix.mul_assoc]
  rw [he]
  simp only [Matrix.trace,Matrix.diag,Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  have hs : K j i=K i j := congrFun (congrFun hk i) j
  rw [hs,pow_two]
  rfl

theorem covariance_trace_nonnegative {d : ℕ} (H S : Matrix (Fin d) (Fin d) ℝ)
    (hH : H.transpose=H) : 0 ≤ Matrix.trace (H*(S*S.transpose)*H*(S*S.transpose)) := by
  rw [covariance_trace_square H S hH]
  exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem covariance_trace_zero {d : ℕ} (H S : Matrix (Fin d) (Fin d) ℝ)
    (hH : H.transpose=H)
    (hz : Matrix.trace (H*(S*S.transpose)*H*(S*S.transpose))=0) :
    S.transpose*H*S=0 := by
  rw [covariance_trace_square H S hH] at hz
  have hi := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ =>
    Finset.sum_nonneg (fun j _ => sq_nonneg ((S.transpose*H*S) i j)))).mp hz
  ext i j
  have hj := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg ((S.transpose*H*S) i j))).mp (hi i (Finset.mem_univ i)) j (Finset.mem_univ j)
  exact sq_eq_zero_iff.mp hj

end Asakura.Chapter7
