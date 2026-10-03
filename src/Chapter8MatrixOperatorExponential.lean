import Chapter8DampedSemigroup
import Chapter8EuclideanOperatorMatrix
import Chapter4MatrixFlowConvolution
import Mathlib.Analysis.Matrix.Normed

open Matrix
open scoped Matrix.Norms.L2Operator
namespace Asakura.Chapter8
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

/-- Matrix and Euclidean-operator exponentials agree, so the stochastic
convolution formula and the resistance norm bound use the same kernel. -/
theorem matrix_operator_exponential {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ) :
    Matrix.toEuclideanCLM (𝕜 := ℝ) (NormedSpace.exp A)=
      NormedSpace.exp (Matrix.toEuclideanCLM (𝕜 := ℝ) A) := by
  apply NormedSpace.map_exp_of_mem_ball (𝕂 := ℝ) (Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ))
  · exact (Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ)).toAlgEquiv.toLinearEquiv.toLinearMap.continuous_of_finiteDimensional
  · simp [NormedSpace.expSeries_radius_eq_top]

end Asakura.Chapter8
