import Chapter10InnovationBlockAlgebra
import Chapter10MatrixOperator
import Mathlib.Analysis.Calculus.Deriv.Prod

open Matrix Set
open scoped Matrix.Norms.Elementwise
namespace Asakura.Chapter10
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

/-- Block matrices indexed by the manuscript's concatenated finite vectors. -/
def finiteBlocks {a b c d : ℕ}
    (A : Matrix (Fin a) (Fin c) ℝ) (B : Matrix (Fin a) (Fin d) ℝ)
    (C : Matrix (Fin b) (Fin c) ℝ) (D : Matrix (Fin b) (Fin d) ℝ) :
    Matrix (Fin (a+b)) (Fin (c+d)) ℝ :=
  (fromBlocks A B C D).submatrix finSumFinEquiv.symm finSumFinEquiv.symm

lemma finiteBlocks_mul {a b c d e f : ℕ}
    (A : Matrix (Fin a) (Fin c) ℝ) (B : Matrix (Fin a) (Fin d) ℝ)
    (C : Matrix (Fin b) (Fin c) ℝ) (D : Matrix (Fin b) (Fin d) ℝ)
    (E : Matrix (Fin c) (Fin e) ℝ) (F : Matrix (Fin c) (Fin f) ℝ)
    (G : Matrix (Fin d) (Fin e) ℝ) (H : Matrix (Fin d) (Fin f) ℝ) :
    finiteBlocks A B C D*finiteBlocks E F G H=
      finiteBlocks (A*E+B*G) (A*F+B*H) (C*E+D*G) (C*F+D*H) := by
  simp only [finiteBlocks,submatrix_mul_equiv,fromBlocks_multiply]

lemma finiteBlocks_transpose {a b c d : ℕ}
    (A : Matrix (Fin a) (Fin c) ℝ) (B : Matrix (Fin a) (Fin d) ℝ)
    (C : Matrix (Fin b) (Fin c) ℝ) (D : Matrix (Fin b) (Fin d) ℝ) :
    (finiteBlocks A B C D).transpose=finiteBlocks A.transpose C.transpose B.transpose D.transpose := by
  simp only [finiteBlocks,transpose_submatrix,fromBlocks_transpose]

lemma finiteBlocks_add {a b c d : ℕ}
    (A A' : Matrix (Fin a) (Fin c) ℝ) (B B' : Matrix (Fin a) (Fin d) ℝ)
    (C C' : Matrix (Fin b) (Fin c) ℝ) (D D' : Matrix (Fin b) (Fin d) ℝ) :
    finiteBlocks A B C D+finiteBlocks A' B' C' D'=
      finiteBlocks (A+A') (B+B') (C+C') (D+D') := by
  have hh := congrArg (fun M : Matrix (Fin a ⊕ Fin b) (Fin c ⊕ Fin d) ℝ =>
    M.submatrix finSumFinEquiv.symm finSumFinEquiv.symm) (fromBlocks_add A B C D A' B' C' D')
  exact hh

lemma finiteBlocks_deriv {d r : ℕ} (S : ℝ → Matrix (Fin d) (Fin d) ℝ)
    (S' : Matrix (Fin d) (Fin d) ℝ) (t : ℝ) (hS : HasDerivWithinAt S S' (Ici t) t) :
    HasDerivWithinAt (fun s => finiteBlocks (S s) 0 0 (s • (1 : Matrix (Fin r) (Fin r) ℝ)))
      (finiteBlocks S' 0 0 (1 : Matrix (Fin r) (Fin r) ℝ)) (Ici t) t := by
  apply hasDerivWithinAt_pi.mpr
  intro i
  apply hasDerivWithinAt_pi.mpr
  intro j
  rcases hi : finSumFinEquiv.symm i with a|a <;>
    rcases hj : finSumFinEquiv.symm j with b|b
  · simpa only [finiteBlocks,submatrix_apply,hi,hj,fromBlocks_apply₁₁] using
      (hasDerivWithinAt_pi.mp (hasDerivWithinAt_pi.mp hS a) b)
  · simpa only [finiteBlocks,submatrix_apply,hi,hj,fromBlocks_apply₁₂,Pi.zero_apply,Matrix.zero_apply] using!
      (hasDerivWithinAt_const t (Ici t) (0:ℝ))
  · simpa only [finiteBlocks,submatrix_apply,hi,hj,fromBlocks_apply₂₁,Pi.zero_apply,Matrix.zero_apply] using!
      (hasDerivWithinAt_const t (Ici t) (0:ℝ))
  · simpa only [finiteBlocks,submatrix_apply,hi,hj,fromBlocks_apply₂₂,Matrix.smul_apply,smul_eq_mul,one_mul,id_eq] using!
      (hasDerivWithinAt_id t (Ici t)).mul_const ((1 : Matrix (Fin r) (Fin r) ℝ) a b)

end Asakura.Chapter10
