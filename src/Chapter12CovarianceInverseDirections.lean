import Chapter12TensorContraction
import Chapter12DivergenceDuality
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

open Matrix
open scoped RealInnerProductSpace
namespace Asakura.Chapter12
set_option maxHeartbeats 1200000

noncomputable def derivativeGram {ι H : Type*} [Fintype ι]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] (v : ι → H) : Matrix ι ι ℝ :=
  fun i j => ⟪v i,v j⟫

/-- The inverse Malliavin covariance selects one coordinate derivative.
This is the algebraic step before applying divergence duality. -/
theorem inverse_covariance_direction {ι H : Type*} [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (v : ι → H) (hdet : (derivativeGram v).det ≠ 0) (i j : ι) :
    inner ℝ (v j) (∑ k,(derivativeGram v)⁻¹ i k • v k) = if i=j then 1 else 0 := by
  have hm := Matrix.nonsing_inv_mul (derivativeGram v) (isUnit_iff_ne_zero.mpr hdet)
  have he := congrArg (fun A : Matrix ι ι ℝ => A i j) hm
  rw [Matrix.mul_apply,Matrix.one_apply] at he
  rw [inner_sum]
  simp only [inner_smul_right]
  convert he using 1
  apply Finset.sum_congr rfl
  intro k hk
  rw [derivativeGram,real_inner_comm (v j) (v k)]

theorem chain_inverse_covariance_direction {ι H : Type*} [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (v : ι → H) (hdet : (derivativeGram v).det ≠ 0) (a : ι → ℝ) (i : ι) :
    inner ℝ (∑ j,a j • v j) (∑ k,(derivativeGram v)⁻¹ i k • v k) = a i := by
  rw [sum_inner]
  simp only [inner_smul_left,inverse_covariance_direction v hdet]
  simp

end Asakura.Chapter12
