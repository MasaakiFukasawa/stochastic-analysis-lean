import Chapter12HigherChainPartitions
import Mathlib.Analysis.SpecialFunctions.Sqrt

open scoped BigOperators
namespace Asakura.Chapter12
set_option maxHeartbeats 1800000

theorem multilinear_array_square_bound {I : Type*} [Fintype I] [DecidableEq I]
    {J : I → Type*} [∀i,Fintype (J i)]
    {E : I → Type*} [∀i,NormedAddCommGroup (E i)] [∀i,NormedSpace ℝ (E i)]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (A : ContinuousMultilinearMap ℝ E F) (U : ∀i,J i → E i) :
    (∑j : ∀i,J i,‖A (fun i => U i (j i))‖^2) ≤
      ‖A‖^2 * ∏i,∑j,‖U i j‖^2 := by
  classical
  calc
    _ ≤ ∑j : ∀i,J i,(‖A‖*∏i,‖U i (j i)‖)^2 := by
      apply Finset.sum_le_sum
      intro j _
      exact pow_le_pow_left₀ (norm_nonneg _) (A.le_opNorm _) 2
    _ = ‖A‖^2 * ∏i,∑j,‖U i j‖^2 := by
      simp_rw [mul_pow,←Finset.prod_pow]
      rw [←Finset.mul_sum,Fintype.prod_sum (fun i j => ‖U i j‖^2)]

theorem multilinear_array_norm_bound {I : Type*} [Fintype I] [DecidableEq I]
    {J : I → Type*} [∀i,Fintype (J i)]
    {E : I → Type*} [∀i,NormedAddCommGroup (E i)] [∀i,NormedSpace ℝ (E i)]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (A : ContinuousMultilinearMap ℝ E F) (U : ∀i,J i → E i) :
    Real.sqrt (∑j : ∀i,J i,‖A (fun i => U i (j i))‖^2) ≤
      ‖A‖ * ∏i,Real.sqrt (∑j,‖U i j‖^2) := by
  classical
  apply (Real.sqrt_le_sqrt (multilinear_array_square_bound A U)).trans_eq
  rw [Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq (norm_nonneg _)]
  congr 1
  exact Real.sqrt_prod _ (fun i _ => Finset.sum_nonneg (fun j _ => sq_nonneg _))
end Asakura.Chapter12
#print axioms Asakura.Chapter12.multilinear_array_norm_bound
