import Chapter10ContinuousCovarianceIdentification
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.LinearAlgebra.Matrix.ToLin

open Matrix
open scoped Matrix.Norms.Elementwise BigOperators
namespace Asakura.Chapter10
set_option backward.isDefEq.respectTransparency false

/-- Matrix action as a continuous linear map, continuously in the matrix. -/
noncomputable def matrixOperatorMap {d : ℕ} :
    Matrix (Fin d) (Fin d) ℝ →L[ℝ] ((Fin d → ℝ) →L[ℝ] (Fin d → ℝ)) :=
  ((LinearMap.toContinuousLinearMap :
    ((Fin d → ℝ) →ₗ[ℝ] (Fin d → ℝ)) ≃ₗ[ℝ] ((Fin d → ℝ) →L[ℝ] (Fin d → ℝ))).toLinearMap.comp
      (Matrix.toLin' : Matrix (Fin d) (Fin d) ℝ ≃ₗ[ℝ] ((Fin d → ℝ) →ₗ[ℝ] (Fin d → ℝ))).toLinearMap).toContinuousLinearMap

theorem matrixOperatorMap_apply {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ) (x : Fin d → ℝ) :
    matrixOperatorMap A x=A*ᵥx := Matrix.toLin'_apply A x

theorem matrixOperatorMap_entries {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ) :
    (fun i j => matrixOperatorMap A (Pi.single j 1) i)=A := by
  classical
  ext i j
  rw [matrixOperatorMap_apply]
  simp [Matrix.mulVec,dotProduct,Pi.single_apply]

end Asakura.Chapter10
