import Chapter8InformationPositive
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

open Matrix
namespace Asakura.Chapter8
set_option maxHeartbeats 1000000

/-- The bracket integrand of Phi^T a^{-1} Sigma dW is exactly the
information integrand Phi^T a^{-1} Phi. -/
theorem score_matrix_information_identity {d p : ℕ}
    (Φ : Matrix (Fin d) (Fin p) ℝ) (σ a : Matrix (Fin d) (Fin d) ℝ)
    (ha : a=σ*σᵀ) (haInv : IsUnit a.det) :
    (Φᵀ*a⁻¹*σ)*(Φᵀ*a⁻¹*σ)ᵀ=Φᵀ*a⁻¹*Φ := by
  have hs : aᵀ=a := by rw [ha,transpose_mul,transpose_transpose]
  calc
    _ = Φᵀ*(a⁻¹*(σ*σᵀ)*a⁻¹ᵀ)*Φ := by
      simp only [transpose_mul,transpose_transpose,Matrix.mul_assoc]
    _ = Φᵀ*(a⁻¹*a*a⁻¹)*Φ := by rw [←ha,transpose_nonsing_inv,hs]
    _ = _ := by rw [a.nonsing_inv_mul haInv,one_mul]

/-- The inverse-diffusion score coefficients used in the regularity lemma
are the same coefficients as Phi^T a^{-1} Sigma. -/
theorem score_inverse_diffusion_identity {d p : ℕ}
    (Φ : Matrix (Fin d) (Fin p) ℝ) (σ : Matrix (Fin d) (Fin d) ℝ)
    (hσ : IsUnit σ.det) :
    Φᵀ*(σ*σᵀ)⁻¹*σ=(σ⁻¹*Φ)ᵀ := by
  rw [Matrix.mul_inv_rev,transpose_mul,transpose_nonsing_inv]
  simp only [Matrix.mul_assoc]
  rw [σ.nonsing_inv_mul hσ,mul_one]

end Asakura.Chapter8
