import Chapter12GaussianLp
import Mathlib.Probability.Distributions.Gaussian.Real

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false

/-- Gaussian exponential functions have every finite Lp moment, including
the domination needed to extend D from polynomial cylinders to stock prices. -/
theorem gaussian_exponential_memLp {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (Z : Ω → ℝ) (m : ℝ) (v : ℝ≥0)
    (hZ : HasLaw Z (gaussianReal m v) P) (a : ℝ)
    (p : ℝ≥0∞) (hp : p ≠ ⊤) : MemLp (fun w => Real.exp (a*Z w)) p P := by
  have hm : AEStronglyMeasurable (fun w => Real.exp (a*Z w)) P :=
    (Real.measurable_exp.comp_aemeasurable (hZ.aemeasurable.const_mul a)).aestronglyMeasurable
  by_cases hp0 : p = 0
  · subst p
    exact memLp_zero_iff_aestronglyMeasurable.mpr hm
  apply (integrable_norm_rpow_iff hm hp0 hp).mp
  have hi : Integrable (fun w => Real.exp ((a*p.toReal)*Z w)) P :=
    hZ.integrable_comp (integrable_exp_mul_gaussianReal (a*p.toReal))
  convert hi using 1
  funext w
  rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),← Real.exp_mul]
  congr 1
  ring

end Asakura.Chapter12
