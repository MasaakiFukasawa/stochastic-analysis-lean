import Chapter10RiccatiAlgebra
import Mathlib.Algebra.BigOperators.Fin

open Matrix
open scoped BigOperators
namespace Asakura.Chapter10
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

/-- Concatenate the state and observation Brownian coefficients, including
the minus sign in the filtering error equation. -/
def errorNoise {d q r : ℕ} (G : Matrix (Fin d) (Fin q) ℝ)
    (K : Matrix (Fin d) (Fin r) ℝ) (D : Matrix (Fin r) (Fin r) ℝ) :
    Matrix (Fin d) (Fin (q+r)) ℝ := fun i => Fin.addCases (G i) (fun j => -(K*D) i j)

theorem errorNoise_gram {d q r : ℕ} (G : Matrix (Fin d) (Fin q) ℝ)
    (K : Matrix (Fin d) (Fin r) ℝ) (D : Matrix (Fin r) (Fin r) ℝ) :
    errorNoise G K D*(errorNoise G K D).transpose=G*G.transpose+K*(D*D.transpose)*K.transpose := by
  have he : errorNoise G K D*(errorNoise G K D).transpose=
      G*G.transpose+(K*D)*(K*D).transpose := by
    ext i j
    simp only [Matrix.mul_apply,Matrix.transpose_apply,Matrix.add_apply]
    rw [Fin.sum_univ_add]
    simp only [errorNoise,Fin.addCases_left,Fin.addCases_right,neg_mul_neg,Matrix.mul_apply]
  rw [he,transpose_mul]
  simp only [Matrix.mul_assoc]

end Asakura.Chapter10
