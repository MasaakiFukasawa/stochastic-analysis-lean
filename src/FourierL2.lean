import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.NumberTheory.ZetaValues

namespace Asakura
noncomputable def fourierCoefficient (t : ℝ) (n : ℕ) : ℝ :=
  Real.sqrt 2 * Real.sin (Real.pi * n * t) / (Real.pi * n)

lemma fourier_coefficients_square_summable (t : ℝ) :
    Summable (fun n => ‖fourierCoefficient t n‖ ^ 2) := by
  apply Summable.of_nonneg_of_le (fun _ => sq_nonneg _) _
    (hasSum_zeta_two.summable.mul_left (2 / Real.pi ^ 2))
  intro n
  rw [Real.norm_eq_abs, sq_abs]
  have hsin : Real.sin (Real.pi * n * t) ^ 2 ≤ 1 := Real.sin_sq_le_one _
  have he : fourierCoefficient t n ^ 2 =
      (2 / Real.pi ^ 2 * (1 / (n : ℝ) ^ 2)) * Real.sin (Real.pi * n * t) ^ 2 := by
    unfold fourierCoefficient
    rw [div_pow, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), mul_pow]
    ring
  rw [he]
  exact mul_le_of_le_one_right (by positivity) hsin

/-- Deterministic Hilbert-space form of the Fourier L2 convergence exercise. -/
theorem orthonormal_fourier_series_converges
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (v : ℕ → E) (hv : Orthonormal ℝ v) (t : ℝ) :
    Summable (fun n => fourierCoefficient t n • v n) := by
  have h := (hv.orthogonalFamily.summable_iff_norm_sq_summable
    (fourierCoefficient t)).mpr (fourier_coefficients_square_summable t)
  simpa using h
end Asakura
