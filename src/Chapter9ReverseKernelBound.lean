import Chapter9ReverseKernelEndpoint

open MeasureTheory ProbabilityTheory Set
namespace Asakura.Chapter9
set_option maxHeartbeats 800000

/-- A uniform bound for reverse Gaussian integration, retaining its
Jacobian factor. No transition normalization is assumed. -/
theorem reverse_gaussian_integral_bound {d : ℕ} (h b : ℝ) (hh : 0<h) (hb : h≤b)
    (x : Fin d → ℝ) (q : (Fin d → ℝ) → ℝ) (hq : Continuous q)
    (C : ℝ) (hC : 0≤C) (hbound : ∀ y,‖q y‖≤C) :
    ‖∫ y,q y*gaussianKernel (Real.exp (-h)) (1-Real.exp (-2*h)) y x‖≤Real.exp ((d:ℝ)*b)*C := by
  rw [reverse_gaussian_change_variables_coordinates h hh x q hq,norm_mul,
    Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  have hi : ‖∫ ξ : Fin d → ℝ,
      q (Real.exp h • (x-Real.sqrt (1-Real.exp (-2*h)) • ξ))
      ∂Measure.pi (fun _ => gaussianReal 0 1)‖≤C := by
    simpa using norm_integral_le_of_norm_le_const (μ := Measure.pi (fun _ : Fin d => gaussianReal 0 1))
      (ae_of_all _ (fun ξ => hbound (Real.exp h • (x-Real.sqrt (1-Real.exp (-2*h)) • ξ))))
  exact mul_le_mul (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg d)))
    hi (norm_nonneg _) (Real.exp_pos _).le
end Asakura.Chapter9
