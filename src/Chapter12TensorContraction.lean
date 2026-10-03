import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Sqrt

open Finset
namespace Asakura.Chapter12

/-- Contracting all common indices at once does not introduce a dimension
factor. I and K encode the uncontracted indices and J all shared indices. -/
theorem tensor_contraction_square_bound {I J K : Type*} [Fintype I] [Fintype J] [Fintype K]
    (A : I → J → ℝ) (B : J → K → ℝ) :
    (∑ i, ∑ k, (∑ j, A i j*B j k)^2) ≤
      (∑ i, ∑ j, (A i j)^2)*(∑ j, ∑ k, (B j k)^2) := by
  calc
    _ ≤ ∑ i, ∑ k, (∑ j, (A i j)^2)*(∑ j, (B j k)^2) := by
      apply sum_le_sum
      intro i _
      apply sum_le_sum
      intro k _
      exact sum_mul_sq_le_sq_mul_sq univ (A i) (fun j => B j k)
    _ = _ := by
      simp_rw [← mul_sum]
      rw [← sum_mul]
      congr 1
      exact sum_comm

/-- The Hilbert tensor norm estimate follows by taking square roots. -/
theorem tensor_contraction_norm_bound {I J K : Type*} [Fintype I] [Fintype J] [Fintype K]
    (A : I → J → ℝ) (B : J → K → ℝ) :
    Real.sqrt (∑ i, ∑ k, (∑ j, A i j*B j k)^2) ≤
      Real.sqrt (∑ i, ∑ j, (A i j)^2)*Real.sqrt (∑ j, ∑ k, (B j k)^2) := by
  calc
    _ ≤ Real.sqrt ((∑ i, ∑ j, (A i j)^2)*(∑ j, ∑ k, (B j k)^2)) :=
      Real.sqrt_le_sqrt (tensor_contraction_square_bound A B)
    _ = _ := Real.sqrt_mul (sum_nonneg fun i _ => sum_nonneg fun j _ => sq_nonneg (A i j)) _

end Asakura.Chapter12
