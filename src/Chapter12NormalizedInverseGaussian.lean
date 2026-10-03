import Chapter12GaussianNormalization

open MeasureTheory Real
open scoped RealInnerProductSpace
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000

theorem normalized_inverse_gaussian {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (b : ℝ) (hb : 0<b) (x : E) :
    (normalizedGaussianKernel (1/(4*b)) x:ℂ)=
      ((2*π)^Module.finrank ℝ E:ℂ)⁻¹*
        ∫ ξ,Complex.exp (-Complex.I*(inner ℝ ξ x:ℂ))*(Real.exp (-b*‖ξ‖^2):ℂ) := by
  rw [inverse_gaussian_kernel b hb x]
  have hc : π/(1/(4*b))=4*π*b := by field_simp <;> ring
  have hexp : -(1/(4*b))*‖x‖^2= -‖x‖^2/(4*b) := by ring
  have hA : (π/b)^(Module.finrank ℝ E/2:ℝ)≠0 :=
    (Real.rpow_pos_of_pos (div_pos pi_pos hb) _).ne'
  have hn := gaussian_fourier_normalization (Module.finrank ℝ E) b hb
  unfold normalizedGaussianKernel
  rw [hc,hexp]
  have hreal : Real.exp (-‖x‖^2/(4*b))/(4*π*b)^(Module.finrank ℝ E/2:ℝ)=
      ((2*π)^Module.finrank ℝ E)⁻¹*
        ((π/b)^(Module.finrank ℝ E/2:ℝ)*Real.exp (-‖x‖^2/(4*b))) := by
    rw [← hn,mul_inv_rev]
    field_simp
  exact_mod_cast hreal

end Asakura.Chapter12
