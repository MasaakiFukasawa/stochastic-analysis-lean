import Chapter10KalmanErrorTransformation

open Matrix MeasureTheory Set
open scoped BigOperators Matrix.Norms.Elementwise
namespace Asakura.Chapter10
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false

def stackRows {a b c : ℕ} (A : Matrix (Fin a) (Fin c) ℝ) (B : Matrix (Fin b) (Fin c) ℝ) :
    Matrix (Fin (a+b)) (Fin c) ℝ := (Matrix.fromRows A B).submatrix finSumFinEquiv.symm id

lemma difference_stacked_rows {d n : ℕ} (A B : Matrix (Fin d) (Fin n) ℝ) :
    differenceMatrix d*stackRows A B=A-B := by
  ext i j
  have hh := congrFun (differenceMatrix_action (fun k => stackRows A B k j)) i
  change (∑ k,differenceMatrix d i k*stackRows A B k j)=_ at hh
  rw [Matrix.mul_apply,hh]
  simp only [stackRows,headIndex,tailIndex,Matrix.submatrix_apply,Equiv.symm_apply_apply,
    id_eq,Matrix.fromRows_apply_inl,Matrix.fromRows_apply_inr,Matrix.sub_apply]

lemma kalman_error_drift_matrix {d r : ℕ}
    (A : Matrix (Fin d) (Fin d) ℝ) (K : Matrix (Fin d) (Fin r) ℝ)
    (C : Matrix (Fin r) (Fin d) ℝ) :
    (A-K*C)*differenceMatrix d=differenceMatrix d*finiteBlocks A 0 (K*C) (A-K*C) := by
  classical
  ext i j
  have hh := kalman_error_drift_transformation A K C (Pi.single j 1)
  rw [matrixOperatorMap_apply,Matrix.mulVec_mulVec,Matrix.mulVec_mulVec] at hh
  simpa [Matrix.mulVec,dotProduct,Pi.single_apply] using congrFun hh i

/-- Include the innovation coordinate in the original state/filter system.
Subtracting state and filter closes the full error/innovation equation. -/
theorem kalman_augmented_drift_transformation {d r : ℕ}
    (A : Matrix (Fin d) (Fin d) ℝ) (K : Matrix (Fin d) (Fin r) ℝ)
    (C : Matrix (Fin r) (Fin d) ℝ) (J : Matrix (Fin r) (Fin r) ℝ) :
    finiteBlocks (A-K*C) (0 : Matrix (Fin d) (Fin r) ℝ) (J*C) (0 : Matrix (Fin r) (Fin r) ℝ)*
      finiteBlocks (differenceMatrix d) (0 : Matrix (Fin d) (Fin r) ℝ)
        (0 : Matrix (Fin r) (Fin (d+d)) ℝ) (1 : Matrix (Fin r) (Fin r) ℝ)=
      finiteBlocks (differenceMatrix d) (0 : Matrix (Fin d) (Fin r) ℝ)
        (0 : Matrix (Fin r) (Fin (d+d)) ℝ) (1 : Matrix (Fin r) (Fin r) ℝ)*
      finiteBlocks (finiteBlocks A 0 (K*C) (A-K*C)) (0 : Matrix (Fin (d+d)) (Fin r) ℝ)
        ((J*C)*differenceMatrix d) (0 : Matrix (Fin r) (Fin r) ℝ) := by
  simp only [finiteBlocks_mul,Matrix.mul_zero,Matrix.zero_mul,zero_add,add_zero,Matrix.mul_one,Matrix.one_mul]
  rw [kalman_error_drift_matrix]

theorem kalman_augmented_noise_transformation {d q r : ℕ}
    (G : Matrix (Fin d) (Fin q) ℝ) (K : Matrix (Fin d) (Fin r) ℝ)
    (D : Matrix (Fin r) (Fin r) ℝ) :
    finiteBlocks (differenceMatrix d) (0 : Matrix (Fin d) (Fin r) ℝ)
        (0 : Matrix (Fin r) (Fin (d+d)) ℝ) (1 : Matrix (Fin r) (Fin r) ℝ)*
      finiteBlocks (stackRows G (0 : Matrix (Fin d) (Fin q) ℝ))
        (stackRows (0 : Matrix (Fin d) (Fin r) ℝ) (K*D))
        (0 : Matrix (Fin r) (Fin q) ℝ) (1 : Matrix (Fin r) (Fin r) ℝ)=
      finiteBlocks G (-(K*D)) (0 : Matrix (Fin r) (Fin q) ℝ) (1 : Matrix (Fin r) (Fin r) ℝ) := by
  simp only [finiteBlocks_mul,difference_stacked_rows,Matrix.mul_zero,Matrix.zero_mul,
    Matrix.mul_one,Matrix.one_mul,zero_add,add_zero,sub_zero,zero_sub]

end Asakura.Chapter10
