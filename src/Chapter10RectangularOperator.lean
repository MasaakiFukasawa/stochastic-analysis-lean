import Chapter10MatrixOperator

open Matrix
open scoped Matrix.Norms.Elementwise
namespace Asakura.Chapter10

/-- Continuous dependence of a rectangular matrix's linear action on its entries. -/
noncomputable def rectangularOperatorMap {d r : ℕ} :
    Matrix (Fin r) (Fin d) ℝ →L[ℝ] ((Fin d → ℝ) →L[ℝ] (Fin r → ℝ)) :=
  ((LinearMap.toContinuousLinearMap :
    ((Fin d → ℝ) →ₗ[ℝ] (Fin r → ℝ)) ≃ₗ[ℝ] ((Fin d → ℝ) →L[ℝ] (Fin r → ℝ))).toLinearMap.comp
      (Matrix.toLin' : Matrix (Fin r) (Fin d) ℝ ≃ₗ[ℝ] ((Fin d → ℝ) →ₗ[ℝ] (Fin r → ℝ))).toLinearMap).toContinuousLinearMap

theorem rectangularOperatorMap_apply {d r : ℕ} (A : Matrix (Fin r) (Fin d) ℝ) (x : Fin d → ℝ) :
    rectangularOperatorMap A x=A*ᵥx := Matrix.toLin'_apply A x

end Asakura.Chapter10
