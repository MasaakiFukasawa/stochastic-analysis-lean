import Chapter10FiniteBlocks

open Matrix Set
open scoped Matrix.Norms.Elementwise
namespace Asakura.Chapter10
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

lemma finiteBlocks_continuous {a b c d : ℕ}
    (A : ℝ → Matrix (Fin a) (Fin c) ℝ) (B : ℝ → Matrix (Fin a) (Fin d) ℝ)
    (C : ℝ → Matrix (Fin b) (Fin c) ℝ) (D : ℝ → Matrix (Fin b) (Fin d) ℝ)
    (hA : Continuous A) (hB : Continuous B) (hC : Continuous C) (hD : Continuous D) :
    Continuous (fun t => finiteBlocks (A t) (B t) (C t) (D t)) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  rcases hi : finSumFinEquiv.symm i with a|a <;>
    rcases hj : finSumFinEquiv.symm j with b|b
  · simpa only [finiteBlocks,submatrix_apply,hi,hj,fromBlocks_apply₁₁,Function.comp_def] using!
      (continuous_apply b).comp ((continuous_apply a).comp hA)
  · simpa only [finiteBlocks,submatrix_apply,hi,hj,fromBlocks_apply₁₂,Function.comp_def] using!
      (continuous_apply b).comp ((continuous_apply a).comp hB)
  · simpa only [finiteBlocks,submatrix_apply,hi,hj,fromBlocks_apply₂₁,Function.comp_def] using!
      (continuous_apply b).comp ((continuous_apply a).comp hC)
  · simpa only [finiteBlocks,submatrix_apply,hi,hj,fromBlocks_apply₂₂,Function.comp_def] using!
      (continuous_apply b).comp ((continuous_apply a).comp hD)

lemma innovation_finite_covariance_identity {d q r : ℕ}
    (F S : Matrix (Fin d) (Fin d) ℝ) (G : Matrix (Fin d) (Fin q) ℝ)
    (K : Matrix (Fin d) (Fin r) ℝ) (D : Matrix (Fin r) (Fin r) ℝ)
    (L : Matrix (Fin r) (Fin d) ℝ) (U : Matrix (Fin r) (Fin r) ℝ)
    (hS : S.transpose=S) (hcancel : S*L.transpose=K*D) :
    let A := finiteBlocks F 0 L (0 : Matrix (Fin r) (Fin r) ℝ)
    let V := finiteBlocks S 0 0 U
    let E := finiteBlocks G (-(K*D)) (0 : Matrix (Fin r) (Fin q) ℝ) (1 : Matrix (Fin r) (Fin r) ℝ)
    A*V+V*A.transpose+E*E.transpose=
      finiteBlocks (F*S+S*F.transpose+G*G.transpose+(K*D)*(K*D).transpose) 0 0
        (1 : Matrix (Fin r) (Fin r) ℝ) := by
  have hh := congrArg (fun M : Matrix (Fin d ⊕ Fin r) (Fin d ⊕ Fin r) ℝ =>
    M.submatrix finSumFinEquiv.symm finSumFinEquiv.symm)
    (innovation_block_covariance_identity F S G K D L U hS hcancel)
  simpa only [finiteBlocks,submatrix_add,transpose_submatrix,submatrix_mul_equiv,Pi.add_apply] using! hh

end Asakura.Chapter10
