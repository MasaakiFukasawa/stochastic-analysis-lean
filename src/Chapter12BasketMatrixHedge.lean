import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

open Matrix
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

/-- Invertibility of the volatility matrix and positivity of stock prices
solve the Clark matching equation uniquely, in the order printed in the book. -/
theorem basket_matrix_hedge_unique {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (hA : A.det≠0) (S ψ : ι → ℝ) (hS : ∀ i,S i≠0) :
    let H := fun i => ((A.transpose)⁻¹.mulVec ψ) i/S i
    A.transpose.mulVec (fun i => S i*H i)=ψ ∧
      ∀ G : ι → ℝ,A.transpose.mulVec (fun i => S i*G i)=ψ → G=H := by
  dsimp only
  have hdet : IsUnit A.transpose.det := isUnit_iff_ne_zero.mpr (by simpa only [Matrix.det_transpose] using hA)
  have he (v : ι → ℝ) : (fun i => S i*(v i/S i))=v := by
    funext i
    field_simp [hS i]
  constructor
  · rw [he,Matrix.mulVec_mulVec,Matrix.mul_nonsing_inv _ hdet,Matrix.one_mulVec]
  · intro G hG
    have hh := congrArg (fun v => (A.transpose)⁻¹.mulVec v) hG
    rw [Matrix.mulVec_mulVec,Matrix.nonsing_inv_mul _ hdet,Matrix.one_mulVec] at hh
    funext i
    have hi := congrFun hh i
    apply (eq_div_iff (hS i)).mpr
    simpa only [mul_comm] using hi

end Asakura.Chapter12
