import Chapter10KalmanGainAlgebra
import Mathlib.Data.Matrix.Block

open Matrix
namespace Asakura.Chapter10
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

lemma kalman_gain_times_diffusion {d r : ℕ}
    (S : Matrix (Fin d) (Fin d) ℝ) (C : Matrix (Fin r) (Fin d) ℝ)
    (D J : Matrix (Fin r) (Fin r) ℝ) (hJD : J*D=1) :
    (S*C.transpose*(J.transpose*J))*D=S*C.transpose*J.transpose := by
  calc
    _ = S*C.transpose*J.transpose*(J*D) := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [hJD,Matrix.mul_one]

/-- In the joint error/innovation equation, the off-diagonal covariance
terms cancel and the innovation covariance has derivative equal to the identity. -/
theorem innovation_block_covariance_identity {d q r : ℕ}
    (F S : Matrix (Fin d) (Fin d) ℝ) (G : Matrix (Fin d) (Fin q) ℝ)
    (K : Matrix (Fin d) (Fin r) ℝ) (D : Matrix (Fin r) (Fin r) ℝ)
    (L : Matrix (Fin r) (Fin d) ℝ) (U : Matrix (Fin r) (Fin r) ℝ)
    (hS : S.transpose=S) (hcancel : S*L.transpose=K*D) :
    let A := fromBlocks F 0 L (0 : Matrix (Fin r) (Fin r) ℝ)
    let V := fromBlocks S 0 0 U
    let E := fromBlocks G (-(K*D)) (0 : Matrix (Fin r) (Fin q) ℝ) (1 : Matrix (Fin r) (Fin r) ℝ)
    A*V+V*A.transpose+E*E.transpose=
      fromBlocks (F*S+S*F.transpose+G*G.transpose+(K*D)*(K*D).transpose) 0 0
        (1 : Matrix (Fin r) (Fin r) ℝ) := by
  have hc : L*S=(K*D).transpose := by
    simpa only [transpose_mul,transpose_transpose,hS] using congrArg Matrix.transpose hcancel
  dsimp only
  simp only [fromBlocks_transpose,fromBlocks_multiply,transpose_zero,transpose_one,
    transpose_neg,Matrix.mul_zero,Matrix.zero_mul,Matrix.mul_one,Matrix.one_mul,
    Matrix.neg_mul,Matrix.mul_neg,neg_neg,add_zero,zero_add,fromBlocks_add,hcancel,hc,
    add_neg_cancel]
  congr 1
  abel

end Asakura.Chapter10
