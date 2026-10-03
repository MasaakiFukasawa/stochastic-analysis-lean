import FullAuditGaussianCovariance

open MeasureTheory ProbabilityTheory Matrix ContinuousLinearMap
namespace Asakura.FullAudit

noncomputable def matrixPredictor {d n : ℕ} (A : Matrix (Fin d) (Fin n) ℝ) :
    (Fin d → ℝ) →L[ℝ] (Fin n → ℝ) :=
  ContinuousLinearMap.pi fun j => linearPredictor (fun i => A i j)

theorem matrixPredictor_apply {d n : ℕ} (A : Matrix (Fin d) (Fin n) ℝ) (x : Fin d → ℝ) :
    matrixPredictor A x = A.transpose *ᵥ x := by
  ext j
  exact linearPredictor_apply _ _

theorem gaussian_matrix_cross_covariance {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {d n : ℕ} {X : Ω → Fin d → ℝ} (hX : HasGaussianLaw X P)
    (A : Matrix (Fin d) (Fin n) ℝ) (b : Fin d → ℝ) (j : Fin n) :
    cov[(fun ω => linearPredictor b (X ω)),(fun ω => matrixPredictor A (X ω) j); P] =
      (b ᵥ* ((Matrix.of fun i k => cov[(fun ω => X ω i),(fun ω => X ω k); P]) * A)) j := by
  change cov[(fun ω => linearPredictor b (X ω)),(fun ω => linearPredictor (fun i => A i j) (X ω)); P] = _
  rw [gaussian_linear_covariance P hX]
  simp only [vecMul,dotProduct,mulVec,Matrix.mul_apply,Matrix.of_apply]

theorem gaussian_matrix_covariance {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {d n : ℕ} {X : Ω → Fin d → ℝ} (hX : HasGaussianLaw X P)
    (A : Matrix (Fin d) (Fin n) ℝ) (i j : Fin n) :
    cov[(fun ω => matrixPredictor A (X ω) i),(fun ω => matrixPredictor A (X ω) j); P] =
      (A.transpose * (Matrix.of fun i k => cov[(fun ω => X ω i),(fun ω => X ω k); P]) * A) i j := by
  change cov[(fun ω => linearPredictor (fun k => A k i) (X ω)),(fun ω => matrixPredictor A (X ω) j); P] = _
  rw [gaussian_matrix_cross_covariance P hX A (fun k => A k i) j]
  simp only [vecMul,dotProduct,Matrix.mul_apply,transpose_apply,Finset.sum_mul,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  ring

/-- The complete singular-Gaussian regression proof in the manuscript.
The covariance matrix is the actual covariance of X; Q is defined from the
printed nonnegative spectral data. The residual proof and kernel argument are
both connected here, without an invertibility assumption. -/
theorem gaussian_regression_written {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) {d n : ℕ} {X : Ω → Fin d → ℝ}
    (hX : HasGaussianLaw X P) (hmX : Measurable X)
    (hmean : ∀ i, ∫ ω, X ω i ∂P = 0)
    (A : Matrix (Fin d) (Fin n) ℝ) (b : Fin d → ℝ)
    (C : Matrix (Fin d) (Fin d) ℝ)
    (hC : C = Matrix.of (fun i k => cov[(fun ω => X ω i),(fun ω => X ω k); P]))
    (U : Matrix (Fin n) (Fin n) ℝ) (e : Fin n → ℝ)
    (hU : U.transpose * U = 1) (he : ∀ i, 0 ≤ e i)
    (hdiag : A.transpose * C * A = U * diagonal e * U.transpose) :
    P[(fun ω => dotProduct b (X ω)) | MeasurableSpace.comap (fun ω => A.transpose *ᵥ X ω) inferInstance] =ᵐ[P]
      (fun ω => dotProduct (b ᵥ* (C * A * spectralPseudoInverse U e)) (A.transpose *ᵥ X ω)) := by
  have := hX.isProbabilityMeasure
  let Q := spectralPseudoInverse U e
  let M := A.transpose * C * A
  have hQ : M * Q * M = M := by
    dsimp [M,Q]
    rw [hdiag]
    exact spectral_pseudoinverse_identity U e he hU
  have hpsd : C.PosSemidef := hC ▸ gaussian_covariance_posSemidef P hX
  obtain ⟨S,hS⟩ := real_posSemidef_gram_factor hpsd
  have hcancel : C*A*(1-Q*M) = 0 := by
    dsimp only [M] at hQ ⊢
    rw [hS] at hQ ⊢
    exact regression_covariance_cancellation S A Q hQ
  have heq : C*A = C*A*Q*M := by
    rw [Matrix.mul_sub,Matrix.mul_one,← Matrix.mul_assoc] at hcancel
    exact sub_eq_zero.mp hcancel
  let a := b ᵥ* (C*A*Q)
  have hrow : b ᵥ* (C*A) = a ᵥ* M := by
    dsimp [a]
    rw [vecMul_vecMul,← heq]
  have hcross : ∀ j, cov[(fun ω => linearPredictor b (X ω)),(fun ω => matrixPredictor A (X ω) j); P] =
      ∑ i, a i * cov[(fun ω => matrixPredictor A (X ω) i),(fun ω => matrixPredictor A (X ω) j); P] := by
    intro j
    rw [gaussian_matrix_cross_covariance P hX]
    simp_rw [gaussian_matrix_covariance P hX,← hC]
    exact congrFun hrow j
  have hlinmean (c : Fin d → ℝ) : ∫ ω, linearPredictor c (X ω) ∂P = 0 := by
    simp_rw [linearPredictor_apply]
    rw [integral_finsetSum _ (fun i _ => (hX.eval i).integrable.const_mul (c i))]
    simp [integral_const_mul,hmean]
  have h := gaussian_regression_residual_written P
    (show HasGaussianLaw (fun ω => (linearPredictor b (X ω),matrixPredictor A (X ω))) P from
      hX.map ((linearPredictor b).prod (matrixPredictor A)))
    ((linearPredictor b).continuous.measurable.comp hmX)
    ((matrixPredictor A).continuous.measurable.comp hmX) a (hlinmean b)
    (fun j => hlinmean (fun i => A i j)) hcross
  simpa only [linearPredictor_apply,matrixPredictor_apply,dotProduct,a,Q] using h

/-- Such spectral data exist for every observation matrix A, including rank
zero. This discharges the linear-algebra existence premise of the main proof. -/
theorem gaussian_regression_spectral_data {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) {d n : ℕ} {X : Ω → Fin d → ℝ} (hX : HasGaussianLaw X P)
    (A : Matrix (Fin d) (Fin n) ℝ) :
    ∃ (U : Matrix (Fin n) (Fin n) ℝ) (e : Fin n → ℝ),
      U.transpose * U = 1 ∧ (∀ i, 0 ≤ e i) ∧
      A.transpose * (Matrix.of fun i k => cov[(fun ω => X ω i),(fun ω => X ω k); P]) * A =
        U * diagonal e * U.transpose := by
  apply real_posSemidef_spectral
  simpa only [conjTranspose_eq_transpose_of_trivial] using
    (gaussian_covariance_posSemidef P hX).conjTranspose_mul_mul_same A

end Asakura.FullAudit
