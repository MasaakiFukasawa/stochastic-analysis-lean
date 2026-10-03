import Chapter10StateMatrixMap
import Chapter10ErrorNoiseGram
import Chapter10FiniteBlockProjection
import Mathlib.Data.Matrix.ColumnRowPartitioned

open Matrix MeasureTheory Set
open scoped BigOperators Matrix.Norms.Elementwise
namespace Asakura.Chapter10
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false

noncomputable def differenceMatrix (d : ℕ) : Matrix (Fin d) (Fin (d+d)) ℝ :=
  (Matrix.fromCols (1 : Matrix (Fin d) (Fin d) ℝ) (-1)).submatrix id finSumFinEquiv.symm

lemma differenceMatrix_action {d : ℕ} (x : Fin (d+d) → ℝ) :
    differenceMatrix d*ᵥx=(fun i => x (headIndex i)-x (tailIndex i)) := by
  simp only [differenceMatrix,submatrix_mulVec_equiv,fromCols_mulVec,one_mulVec,
    neg_mulVec,Function.comp_def,headIndex,tailIndex]
  rfl

/-- Subtracting the proposed estimate from the state produces exactly the
closed error drift A-KC appearing in the manuscript. -/
theorem kalman_error_drift_transformation {d r : ℕ}
    (A : Matrix (Fin d) (Fin d) ℝ) (K : Matrix (Fin d) (Fin r) ℝ)
    (C : Matrix (Fin r) (Fin d) ℝ) (x : Fin (d+d) → ℝ) :
    (A-K*C)*ᵥ(differenceMatrix d*ᵥx)=
      differenceMatrix d*ᵥ(matrixOperatorMap (finiteBlocks A 0 (K*C) (A-K*C)) x) := by
  rw [differenceMatrix_action,differenceMatrix_action,matrixOperatorMap_apply]
  simp only [finiteBlocks,submatrix_mulVec_equiv,fromBlocks_mulVec,zero_mulVec,add_zero,
    headIndex,tailIndex,Function.comp_apply,Equiv.symm_apply_apply,Sum.elim_inl,Sum.elim_inr]
  change (A-K*C)*ᵥ((fun i => x (headIndex i))-(fun i => x (tailIndex i)))=_
  rw [mulVec_sub,sub_mulVec]
  ext i
  simp only [Pi.sub_apply,Pi.add_apply]
  simp only [headIndex,tailIndex,Function.comp_def,Equiv.symm_symm]
  ring

lemma kalman_error_noise_transformation {d q r : ℕ}
    (G : Matrix (Fin d) (Fin q) ℝ) (K : Matrix (Fin d) (Fin r) ℝ)
    (D : Matrix (Fin r) (Fin r) ℝ) (i : Fin d) (j : Fin (q+r)) :
    (∑ k,differenceMatrix d i k*finiteBlocks G (0 : Matrix (Fin d) (Fin r) ℝ)
      (0 : Matrix (Fin d) (Fin q) ℝ) (K*D) k j)=errorNoise G K D i j := by
  have hh := congrFun (differenceMatrix_action
    (fun k => finiteBlocks G (0 : Matrix (Fin d) (Fin r) ℝ)
      (0 : Matrix (Fin d) (Fin q) ℝ) (K*D) k j)) i
  change (∑ k,differenceMatrix d i k*finiteBlocks G 0 0 (K*D) k j)=_ at hh
  rw [hh]
  obtain ⟨j,rfl⟩ := finSumFinEquiv.surjective j
  cases j with
  | inl j =>
    simp only [finiteBlocks,headIndex,tailIndex,Matrix.submatrix_apply,Equiv.symm_apply_apply]
    simp [errorNoise]
  | inr j =>
    simp only [finiteBlocks,headIndex,tailIndex,Matrix.submatrix_apply,Equiv.symm_apply_apply]
    simp [errorNoise]

end Asakura.Chapter10
