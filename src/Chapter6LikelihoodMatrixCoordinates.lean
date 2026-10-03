import Chapter6GaussianDensityFormula

open Matrix Finset
open scoped Matrix BigOperators
namespace Asakura.Chapter6
set_option maxHeartbeats 1800000

lemma covariance_matrix_cross {d : ℕ} (S : Matrix (Fin d) (Fin d) ℝ) (u v : Fin d → ℝ) :
    (S⁻¹ *ᵥ u) ⬝ᵥ (S⁻¹ *ᵥ v)=u ⬝ᵥ ((S*Sᵀ)⁻¹ *ᵥ v) := by
  conv_rhs => rw [Matrix.mul_inv_rev,←Matrix.transpose_nonsing_inv,←Matrix.mulVec_mulVec,
    dotProduct_mulVec,←mulVec_transpose,Matrix.transpose_transpose]


lemma likelihood_information_coordinates {d n : ℕ} (S : Matrix (Fin d) (Fin d) ℝ)
    (Φ : Matrix (Fin d) (Fin n) ℝ) :
    (S⁻¹*Φ)ᵀ*(S⁻¹*Φ)=Φᵀ*(S*Sᵀ)⁻¹*Φ := by
  rw [Matrix.transpose_mul,Matrix.mul_inv_rev,←Matrix.transpose_nonsing_inv]
  simp only [Matrix.mul_assoc]

lemma likelihood_score_noise_coordinates {d n : ℕ} (S : Matrix (Fin d) (Fin d) ℝ)
    (hS : IsUnit S.det) (Φ : Matrix (Fin d) (Fin n) ℝ) :
    Φᵀ*(S*Sᵀ)⁻¹*S=(S⁻¹*Φ)ᵀ := by
  rw [Matrix.mul_inv_rev,←Matrix.transpose_nonsing_inv,Matrix.transpose_mul]
  rw [Matrix.mul_assoc,Matrix.mul_assoc,S.nonsing_inv_mul hS,Matrix.mul_one]

end Asakura.Chapter6
