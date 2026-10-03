import Chapter10MatrixOperator

open Matrix
open scoped Matrix.Norms.Elementwise
namespace Asakura.Chapter10
set_option backward.isDefEq.respectTransparency false

/-- A continuous invertible observation coefficient has a continuous inverse. -/
theorem continuous_observation_inverse {r : ℕ}
    (D : ℝ → Matrix (Fin r) (Fin r) ℝ) (hD : Continuous D) (hdet : ∀ t,(D t).det≠0) :
    Continuous (fun t => (D t)⁻¹) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  apply (continuousAt_matrix_inv (D t) ?_).comp hD.continuousAt
  simpa only [Ring.inverse_eq_inv'] using (continuousAt_inv₀ (hdet t))

theorem observation_inverse_identities {r : ℕ} (D : Matrix (Fin r) (Fin r) ℝ) (hdet : D.det≠0) :
    D⁻¹*D=1 ∧ D*D⁻¹=1 :=
  ⟨Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hdet),
    Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hdet)⟩

theorem observation_covariance_inverse {r : ℕ} (D : Matrix (Fin r) (Fin r) ℝ) :
    (D*D.transpose)⁻¹=(D⁻¹).transpose*D⁻¹ := by
  rw [Matrix.mul_inv_rev,←Matrix.transpose_nonsing_inv]

end Asakura.Chapter10
