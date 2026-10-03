import Chapter10FiniteBlockProjection

open Matrix
open scoped BigOperators
namespace Asakura.Chapter10
set_option backward.isDefEq.respectTransparency false

lemma innovation_noise_gram {d q r : ℕ}
    (G : Matrix (Fin d) (Fin q) ℝ) (H : Matrix (Fin d) (Fin r) ℝ)
    (i j : Fin r) :
    (∑ k,finiteBlocks G H (0 : Matrix (Fin r) (Fin q) ℝ) 1 (tailIndex i) k*
      finiteBlocks G H (0 : Matrix (Fin r) (Fin q) ℝ) 1 (tailIndex j) k)=if i=j then 1 else 0 := by
  change ((finiteBlocks G H (0 : Matrix (Fin r) (Fin q) ℝ) 1)*
    (finiteBlocks G H (0 : Matrix (Fin r) (Fin q) ℝ) 1).transpose) (tailIndex i) (tailIndex j)=_
  rw [finiteBlocks_transpose,finiteBlocks_mul]
  simp only [Matrix.transpose_zero,Matrix.transpose_one,Matrix.zero_mul,Matrix.one_mul,
    zero_add,finiteBlocks,tailIndex,Matrix.submatrix_apply,Equiv.symm_apply_apply,
    Matrix.fromBlocks_apply₂₂,Matrix.one_apply]

end Asakura.Chapter10
