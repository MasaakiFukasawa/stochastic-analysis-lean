import Chapter7BrownianMatrixScalarCLT

open Matrix Finset
open scoped BigOperators
namespace Asakura.Chapter7
set_option maxHeartbeats 1000000

noncomputable def symmetrizedMatrix {d : ℕ} (V : Matrix (Fin d) (Fin d) ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  fun i j => (V i j+V j i)/2

lemma symmetrized_matrix_symmetric {d : ℕ} (V : Matrix (Fin d) (Fin d) ℝ) :
    (symmetrizedMatrix V).transpose=symmetrizedMatrix V := by
  ext i j
  simp only [Matrix.transpose_apply,symmetrizedMatrix]
  ring

lemma symmetrized_contraction {d : ℕ} (V A : Matrix (Fin d) (Fin d) ℝ)
    (hA : ∀ i j,A i j=A j i) :
    (∑ i,∑ j,(symmetrizedMatrix V) i j*A i j)=∑ i,∑ j,V i j*A i j := by
  have he : (∑ i,∑ j,V j i*A i j)=∑ i,∑ j,V i j*A i j := by
    rw [sum_comm]
    apply sum_congr rfl
    intro i _
    apply sum_congr rfl
    intro j _
    rw [hA j i]
  have ha i j : (symmetrizedMatrix V) i j*A i j=(V i j*A i j+V j i*A i j)/2 := by
    dsimp [symmetrizedMatrix]
    ring
  simp only [ha,← sum_div,sum_add_distrib,he]
  ring

end Asakura.Chapter7
