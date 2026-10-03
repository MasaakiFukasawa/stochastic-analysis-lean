import FullAuditGaussianIndependence
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.DotProduct

open Matrix
namespace Asakura.FullAudit

/-- The spectral pseudoinverse used in the manuscript; zero eigenvalues stay zero. -/
noncomputable def spectralPseudoInverse {n : Type*} [Fintype n] [DecidableEq n]
    (U : Matrix n n ℝ) (eigen : n → ℝ) : Matrix n n ℝ :=
  U * diagonal (fun i => if 0 < eigen i then (eigen i)⁻¹ else 0) * U.transpose

/-- The printed spectral definition has M Q M = M, including singular M. -/
theorem spectral_pseudoinverse_identity {n : Type*} [Fintype n] [DecidableEq n]
    (U : Matrix n n ℝ) (eigen : n → ℝ) (heigen : ∀ i, 0 ≤ eigen i)
    (hU : U.transpose * U = 1) :
    (U * diagonal eigen * U.transpose) * spectralPseudoInverse U eigen *
      (U * diagonal eigen * U.transpose) = U * diagonal eigen * U.transpose := by
  have hd : diagonal eigen * diagonal (fun i => if 0 < eigen i then (eigen i)⁻¹ else 0) * diagonal eigen = diagonal eigen := by
    rw [diagonal_mul_diagonal, diagonal_mul_diagonal]
    congr 1
    funext i
    by_cases hi : 0 < eigen i
    · simp [hi, ne_of_gt hi]
    · have hz : eigen i = 0 := le_antisymm (le_of_not_gt hi) (heigen i)
      simp [hz]
  unfold spectralPseudoInverse
  calc
    _ = U * (diagonal eigen * diagonal (fun i => if 0 < eigen i then (eigen i)⁻¹ else 0) * diagonal eigen) * U.transpose := by
      simp only [Matrix.mul_assoc, ← Matrix.mul_assoc U.transpose U, hU, one_mul]
    _ = _ := by rw [hd]

/-- The square-norm argument: ker(B^T B) is contained in ker B. -/
theorem gram_kernel_written {d n : Type*} [Fintype d] [Fintype n]
    (B : Matrix d n ℝ) (v : n → ℝ) (hv : (B.transpose * B) *ᵥ v = 0) :
    B *ᵥ v = 0 := by
  apply dotProduct_self_eq_zero.mp
  have h := congrArg (fun w => dotProduct v w) hv
  simpa only [← Matrix.mulVec_mulVec, dotProduct_transpose_mulVec, dotProduct_zero] using h

/-- Sigma A kills ker(A^T Sigma A), using exactly the Gram/square-root factorization. -/
theorem covariance_kernel_written {d n : Type*} [Fintype d] [Fintype n]
    (S : Matrix d d ℝ) (A : Matrix d n ℝ) (v : n → ℝ)
    (hv : (A.transpose * (S.transpose * S) * A) *ᵥ v = 0) :
    ((S.transpose * S) * A) *ᵥ v = 0 := by
  have hgram : ((S*A).transpose * (S*A)) *ᵥ v = 0 := by
    simpa only [transpose_mul, Matrix.mul_assoc] using hv
  have hzero := gram_kernel_written (S*A) v hgram
  rw [Matrix.mul_assoc, ← Matrix.mulVec_mulVec, hzero, mulVec_zero]

/-- The displayed Sigma A (I-QM)=0 follows from the spectral identity. -/
theorem regression_covariance_cancellation {d n : Type*} [Fintype d] [Fintype n]
    [DecidableEq n] (S : Matrix d d ℝ) (A : Matrix d n ℝ) (Q : Matrix n n ℝ)
    (hQ : (A.transpose * (S.transpose * S) * A) * Q *
      (A.transpose * (S.transpose * S) * A) = A.transpose * (S.transpose * S) * A) :
    ((S.transpose * S) * A) * (1 - Q * (A.transpose * (S.transpose * S) * A)) = 0 := by
  apply Matrix.ext_of_mulVec_single
  intro i
  rw [← Matrix.mulVec_mulVec, zero_mulVec]
  apply covariance_kernel_written
  have hQ' : (A.transpose * (S.transpose * S) * A) *
      (Q * (A.transpose * (S.transpose * S) * A)) = A.transpose * (S.transpose * S) * A := by
    simpa only [Matrix.mul_assoc] using hQ
  rw [Matrix.mulVec_mulVec, mul_sub, mul_one, hQ', sub_self, zero_mulVec]

end Asakura.FullAudit
