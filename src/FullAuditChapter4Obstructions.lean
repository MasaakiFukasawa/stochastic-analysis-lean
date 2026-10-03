import Chapter3WrittenLimits
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

namespace Asakura.FullAudit

/-- The affine coefficient used below satisfies the printed squared Lipschitz bound L=1. -/
theorem ch4_affine_sigma_lipschitz (x y : ℝ) :
    |(x - 1) - (y - 1)| ^ 2 = |x-y| ^ 2 := by congr 2 <;> ring

/-- chap3.tex, existence proof: sigma(0) must be replaced by |sigma(0)|. -/
theorem ch4_missing_absolute_value_counterexample :
    ¬ (((-1 : ℝ)-1)^2 ≤ ((0-1) + Real.sqrt 1 * |(-1:ℝ)|)^2) := by norm_num

/-- The corrected bound follows from the Lipschitz estimate by the triangle inequality. -/
theorem ch4_corrected_growth_bound (σ : ℝ → ℝ) (x c : ℝ)
    (hc : 0 ≤ c) (h : |σ x - σ 0| ≤ c * |x|) :
    (σ x)^2 ≤ (|σ 0| + c * |x|)^2 := by
  have hx : |σ x| ≤ |σ 0| + c * |x| := by
    calc
      |σ x| = |σ 0 + (σ x - σ 0)| := by congr 1; ring
      _ ≤ |σ 0| + |σ x - σ 0| := abs_add_le _ _
      _ ≤ |σ 0| + c * |x| := by linarith
  have ha := abs_nonneg (σ x)
  have hb : 0 ≤ |σ 0| + c * |x| := by positivity
  nlinarith [sq_abs (σ x)]

/-- A squared contraction estimate with factor cT gives sqrt(cT), not cT. -/
theorem ch4_picard_unsquared_factor_counterexample :
    (1/2:ℝ)^2 ≤ (1/4:ℝ) * 1^2 ∧ ¬ ((1/2:ℝ) ≤ (1/4:ℝ)*1) := by norm_num

/-- Hyperbolic example: at a=2 and theta=0 the diffusion coefficients disagree. -/
theorem ch4_hyperbolic_scale_counterexample :
    (1:ℝ) * (2 * Real.cosh 0) ≠ 1 * Real.sqrt (1 + |2 * Real.sinh 0|^2) := by
  norm_num

/-- The valid scaled identity uses a², not 1. The sign of a is relevant. -/
theorem ch4_hyperbolic_scaled_square (a x : ℝ) :
    (a * Real.cosh x)^2 = a^2 + (a * Real.sinh x)^2 := by
  have h := Real.cosh_sq_sub_sinh_sq x
  have hh := congrArg (fun z : ℝ => a^2*z) h
  nlinarith [hh]

/-- Critical damping m=kappa=1,gamma=2 makes the displayed eigenvalue denominator zero. -/
theorem ch4_critical_damping_denominator_zero :
    ((-(2:ℝ)/1 + Real.sqrt (2^2/1^2 - 4*1/1))/2) -
      ((-2/1 - Real.sqrt (2^2/1^2 - 4*1/1))/2) = 0 := by norm_num

/-- For m=gamma=kappa=1 the displayed discriminant is negative. -/
theorem ch4_underdamped_discriminant_negative :
    (1:ℝ)^2/1^2-4*1/1 < 0 := by norm_num

end Asakura.FullAudit
