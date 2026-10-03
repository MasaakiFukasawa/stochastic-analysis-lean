import Chapter8InformationSquareRoot
import Chapter8InverseGaussian

open MeasureTheory ProbabilityTheory Matrix
open scoped RealInnerProductSpace MatrixOrder
namespace Asakura.Chapter8
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false

/-- Exact covariance cancellation for the information square root. -/
theorem information_sqrt_sandwich {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Matrix ι ι ℝ) (hS : S.PosDef) :
    CFC.sqrt S * S⁻¹ * CFC.sqrt S = 1 := by
  let A := CFC.sqrt S
  have hs : A*A=S := CFC.sqrt_mul_sqrt_self S hS.posSemidef.nonneg
  have hu : IsUnit (A*A) := hs ▸ (S.isUnit_iff_isUnit_det.mpr (isUnit_iff_ne_zero.mpr hS.det_pos.ne'))
  have hd : IsUnit A.det := A.isUnit_iff_isUnit_det.mp (isUnit_of_mul_isUnit_left hu)
  calc
    A*S⁻¹*A = A*(A⁻¹*A⁻¹)*A := by rw [← hs,Matrix.mul_inv_rev]
    _ = (A*A⁻¹)*(A⁻¹*A) := by noncomm_ring
    _ = 1 := by rw [Matrix.mul_nonsing_inv A hd,Matrix.nonsing_inv_mul A hd,one_mul]

/-- The self-normalised MLE limit is standard Gaussian: S^{1/2}
transforms N(0,S^{-1}) to N(0,Id). -/
theorem whitening_gaussian_law {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Matrix ι ι ℝ) (hS : S.PosDef) :
    (multivariateGaussian (0 : EuclideanSpace ℝ ι) S⁻¹).map
      (Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S)) = multivariateGaussian 0 1 := by
  let A := Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S)
  let B := Matrix.toEuclideanCLM (𝕜 := ℝ) S⁻¹
  have hself : IsSelfAdjoint A := (CFC.sqrt_nonneg S).isSelfAdjoint.map (Matrix.toEuclideanCLM (𝕜 := ℝ))
  have hadj : A.adjoint=A := hself.adjoint_eq
  have hcancel : A*B*A=1 := by
    dsimp only [A,B]
    rw [← map_mul,← map_mul,information_sqrt_sandwich S hS,map_one]
  apply IsGaussian.ext
  · simp only [id_eq]
    rw [ContinuousLinearMap.integral_id_map IsGaussian.integrable_id]
    simp
  · apply ContinuousLinearMap.ext
    intro u
    apply ContinuousLinearMap.ext
    intro v
    change covarianceBilin ((multivariateGaussian (0 : EuclideanSpace ℝ ι) S⁻¹).map A) u v =
      covarianceBilin (multivariateGaussian (0 : EuclideanSpace ℝ ι) 1) u v
    rw [covarianceBilin_map IsGaussian.memLp_two_id A,hadj,
      covarianceBilin_multivariateGaussian hS.inv.posSemidef,
      covarianceBilin_multivariateGaussian Matrix.PosSemidef.one,
      ← inner_toEuclideanCLM,← inner_toEuclideanCLM]
    change ⟪A u,B (A v)⟫ = ⟪u,Matrix.toEuclideanCLM (𝕜 := ℝ) 1 v⟫
    have he : ⟪A u,B (A v)⟫ = ⟪u,A (B (A v))⟫ := by
      simpa only [hadj] using A.adjoint_inner_left (B (A v)) u
    rw [he]
    have hv : A (B (A v))=v := by
      change (A*B*A) v=v
      rw [hcancel]
      rfl
    rw [hv,map_one]
    rfl

end Asakura.Chapter8
