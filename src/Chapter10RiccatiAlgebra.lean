import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Tactic.NoncommRing

open Matrix
namespace Asakura.Chapter10
set_option backward.isDefEq.respectTransparency false

/-- Substitute the gain identities into the covariance equation. This is the
matrix computation in the printed proof, independent of any ODE uniqueness. -/
theorem riccati_covariance_identity {n r : Type*} [Fintype n] [Fintype r]
    [DecidableEq n] [DecidableEq r]
    (A S Q : Matrix n n ℝ) (K : Matrix n r ℝ) (C : Matrix r n ℝ)
    (R : Matrix r r ℝ)
    (hK : K * R = S * C.transpose) :
    (A-K*C)*S+S*(A-K*C).transpose+Q+K*R*K.transpose =
      A*S+S*A.transpose+Q-K*C*S := by
  rw [transpose_sub, transpose_mul]
  rw [sub_mul, mul_sub, ← Matrix.mul_assoc S C.transpose K.transpose, ← hK]
  abel

/-- Gain-times-observation-noise cancellation, using the actual inverse
identities rather than treating the cancelling terms as equal by assumption. -/
theorem gain_noise_identity {n r : Type*} [Fintype n] [Fintype r]
    [DecidableEq n] [DecidableEq r]
    (S : Matrix n n ℝ) (C : Matrix r n ℝ) (D J : Matrix r r ℝ)
    (hJD : J*D=1) :
    (S*C.transpose*(J.transpose*J))*D=S*C.transpose*J.transpose := by
  simp only [Matrix.mul_assoc, hJD, Matrix.mul_one]

end Asakura.Chapter10
