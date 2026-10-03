import Chapter9BoundedTests
import Chapter9GaussianMixture

open MeasureTheory ProbabilityTheory
open scoped NNReal
namespace Asakura.Chapter9
set_option maxHeartbeats 1300000
set_option backward.isDefEq.respectTransparency false

/-- The actual Gaussian transition maps bounded Borel tests to bounded
Borel tests with no increase in their uniform bound. -/
theorem gaussian_transition_bounded_borel {d : ℕ} (a : ℝ) (v : ℝ≥0) (hv : v≠0)
    (f : (Fin d → ℝ) → ℝ) (hf : IsBoundedBorel f) :
    IsBoundedBorel (fun x => ∫ y,gaussianKernel a v x y*f y) := by
  obtain ⟨C,hC,hfC⟩ := hf.2
  have hm : Measurable (fun z : (Fin d → ℝ) × (Fin d → ℝ) => gaussianKernel a v z.1 z.2*f z.2) := by
    apply Measurable.mul
    · unfold gaussianKernel
      fun_prop
    · exact hf.1.comp measurable_snd
  refine ⟨hm.stronglyMeasurable.integral_prod_right'.measurable,C,hC,?_⟩
  intro x
  have hk := gaussian_kernel_integral a v hv x
  have hbound y : ‖gaussianKernel a v x y*f y‖≤C*gaussianKernel a v x y := by
    rw [norm_mul,Real.norm_eq_abs,abs_of_pos (gaussian_kernel_positive a v x y)]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hfC y) (gaussian_kernel_positive a v x y).le
  have he := norm_integral_le_of_norm_le (hk.1.const_mul C) (ae_of_all _ hbound)
  simpa only [integral_const_mul,hk.2,mul_one] using he
end Asakura.Chapter9
