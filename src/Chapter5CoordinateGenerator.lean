import Chapter5AffineRestrictionHessian
import Mathlib.Algebra.BigOperators.Pi

open Set
open scoped BigOperators
namespace Asakura.Chapter5
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

theorem bilinear_coordinate_expansion {d : ℕ}
    (L : (Fin d → ℝ) →L[ℝ] (Fin d → ℝ) →L[ℝ] ℝ) (x y : Fin d → ℝ) :
    L x y=∑ i,∑ j,x i*y j*L (Pi.single i 1) (Pi.single j 1) := by
  conv_lhs => rw [pi_eq_sum_univ' x,pi_eq_sum_univ' y]
  simp only [map_sum,map_smul,sum_apply,smul_apply,smul_eq_mul]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Contraction with the covariance matrix equals the sum of Hessians
in the actual noise directions; repeated observation coordinates are allowed. -/
theorem covariance_matrix_hessian_trace {d n : ℕ}
    (L : (Fin d → ℝ) →L[ℝ] (Fin d → ℝ) →L[ℝ] ℝ)
    (Q : Fin n → Fin d → ℝ) :
    (∑ i,∑ j,L (Pi.single i 1) (Pi.single j 1)*(∑ k,Q k i*Q k j))=
      ∑ k,L (Q k) (Q k) := by
  have hr : (∑ k,L (Q k) (Q k))=∑ k,∑ i,∑ j,Q k i*Q k j*L (Pi.single i 1) (Pi.single j 1) :=
    Finset.sum_congr rfl (fun k _ => bilinear_coordinate_expansion L (Q k) (Q k))
  rw [hr]
  simp_rw [Finset.mul_sum]
  calc
    _ = ∑ i,∑ k,∑ j,L (Pi.single i 1) (Pi.single j 1)*(Q k i*Q k j) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
    _ = ∑ k,∑ i,∑ j,L (Pi.single i 1) (Pi.single j 1)*(Q k i*Q k j) := by
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring

end Asakura.Chapter5
