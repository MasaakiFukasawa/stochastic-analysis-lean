import Chapter8InverseSlutsky

open MeasureTheory ProbabilityTheory Matrix
open scoped RealInnerProductSpace
namespace Asakura.Chapter8
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false

/-- Transforming N(0,S) by S⁻¹ gives N(0,S⁻¹), as used in the
asymptotic covariance of the maximum-likelihood estimator. -/
theorem inverse_gaussian_law {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Matrix ι ι ℝ) (hS : S.PosDef) :
    (multivariateGaussian (0 : EuclideanSpace ℝ ι) S).map
      (Matrix.toEuclideanCLM (𝕜 := ℝ) S⁻¹) = multivariateGaussian 0 S⁻¹ := by
  let A := Matrix.toEuclideanCLM (𝕜 := ℝ) S⁻¹
  have hself : IsSelfAdjoint A := hS.inv.isHermitian.isSelfAdjoint.map (Matrix.toEuclideanCLM (𝕜 := ℝ))
  have hadj : A.adjoint=A := hself.adjoint_eq
  have hcancel : (Matrix.toEuclideanCLM (𝕜 := ℝ) S)*A=1 := by
    rw [← map_mul]
    simp [A,Matrix.mul_nonsing_inv S (isUnit_iff_ne_zero.mpr hS.det_pos.ne')]
  apply IsGaussian.ext
  · simp only [id_eq]
    rw [ContinuousLinearMap.integral_id_map IsGaussian.integrable_id]
    simp
  · apply ContinuousLinearMap.ext
    intro u
    apply ContinuousLinearMap.ext
    intro v
    change covarianceBilin ((multivariateGaussian (0 : EuclideanSpace ℝ ι) S).map A) u v =
      covarianceBilin (multivariateGaussian (0 : EuclideanSpace ℝ ι) S⁻¹) u v
    rw [covarianceBilin_map IsGaussian.memLp_two_id A,hadj,
      covarianceBilin_multivariateGaussian hS.posSemidef,
      covarianceBilin_multivariateGaussian hS.inv.posSemidef,
      ← inner_toEuclideanCLM,← inner_toEuclideanCLM]
    have hv : Matrix.toEuclideanCLM (𝕜 := ℝ) S (A v) = v := by
      change ((Matrix.toEuclideanCLM (𝕜 := ℝ) S)*A) v=v
      rw [hcancel]
      rfl
    rw [hv]
    change ⟪A u,v⟫ = ⟪u,A v⟫
    simpa only [hadj] using A.adjoint_inner_left v u

end Asakura.Chapter8
