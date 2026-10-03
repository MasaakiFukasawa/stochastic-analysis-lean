import Chapter10FiniteBlocks
import Chapter10StateProjection

open Matrix
open scoped Matrix.Norms.Elementwise
namespace Asakura.Chapter10
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

def headIndex {d r : ℕ} (i : Fin d) : Fin (d+r) := finSumFinEquiv (Sum.inl i)
def tailIndex {d r : ℕ} (j : Fin r) : Fin (d+r) := finSumFinEquiv (Sum.inr j)

lemma finiteBlocks_head_tail {d r : ℕ} (S : Matrix (Fin d) (Fin d) ℝ)
    (U : Matrix (Fin r) (Fin r) ℝ) (i : Fin d) (j : Fin r) :
    finiteBlocks S 0 0 U (headIndex i) (tailIndex j)=0 := by
  simp [finiteBlocks,headIndex,tailIndex]

lemma finiteBlocks_head_action {d r : ℕ} (F : Matrix (Fin d) (Fin d) ℝ)
    (L : Matrix (Fin r) (Fin d) ℝ) (x : Fin (d+r) → ℝ) (i : Fin d) :
    matrixOperatorMap (finiteBlocks F 0 L (0 : Matrix (Fin r) (Fin r) ℝ)) x (headIndex i)=
      matrixOperatorMap F (coordinateProjection (headIndex (d := d) (r := r)) x) i := by
  rw [matrixOperatorMap_apply,matrixOperatorMap_apply]
  simp only [finiteBlocks,submatrix_mulVec_equiv,fromBlocks_mulVec,Matrix.zero_mulVec,
    add_zero,headIndex,Function.comp_apply,Equiv.symm_apply_apply,Sum.elim_inl]
  rfl

end Asakura.Chapter10
