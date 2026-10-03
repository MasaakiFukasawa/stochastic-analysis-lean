import FullAuditChapter4Gronwall

namespace Asakura.FullAudit

/-- The generator bound is squared before the contraction estimate. -/
theorem ch5_lipschitz_square (f y z C : ℝ) (hC : 0 ≤ C)
    (hf : |f| ≤ C * (|y|+|z|)) :
    f^2 ≤ 2*C^2*(y^2+z^2) := by
  have ha : 0 ≤ C * (|y|+|z|) := by positivity
  have hs : f^2 ≤ (C * (|y|+|z|))^2 := by
    nlinarith [sq_abs f, abs_nonneg f]
  have h : (|y|+|z|)^2 ≤ 2*(y^2+z^2) := by
    nlinarith [sq_nonneg (|y|-|z|),sq_abs y,sq_abs z]
  have hh := mul_le_mul_of_nonneg_left h (sq_nonneg C)
  nlinarith [hh]

/-- C=2, f(y,z)=2(y+z) attains the Lipschitz bound, but the printed C fails. -/
theorem ch5_unsquared_lipschitz_constant :
    |(2:ℝ)*(1+1)| ≤ 2*(|1|+|1|) ∧
    ¬ ((2:ℝ)*(1+1))^2 ≤ 2*2*(1^2+1^2) := by norm_num

/-- The bracket bound needs the square of the supremum. -/
theorem ch5_bracket_missing_square :
    ¬ ((2:ℝ)^2*1^2 ≤ 2*1^2) := by norm_num

/-- Ito drift after time reversal, using the PDE exactly as written with a. -/
theorem ch5_burgers_drift (vt vxx a y z : ℝ)
    (hpde : vt = vxx/2 + a*y*z) :
    -vt+vxx/2 = -a*y*z := by linarith

theorem ch5_burgers_missing_parameter :
    -(2:ℝ)*1*1 ≠ -1*1 := by norm_num

/-- Changing the heat-time from 2 to 1 changes its cosine multiplier. -/
theorem ch5_heat_times_distinct :
    Real.exp (-(2:ℝ)/2) ≠ Real.exp (-1/2) := by
  intro h
  have := Real.exp_injective h
  norm_num at this

/-- A negative perturbation parameter cannot bound a positive norm linearly. -/
theorem ch5_perturbation_abs_needed : ¬ (1:ℝ) ≤ -1 := by norm_num

/-- Degenerate observation coefficient makes the entire scalar likelihood constant. -/
theorem ch6_zero_information_likelihood (θ : ℝ) :
    θ*0 - (1/2:ℝ)*θ^2*0 = 0 := by ring

theorem ch7_bounded_difference_counterexample :
    |(1:ℝ)-(-1)| > max |(1:ℝ)| |(-1:ℝ)| := by norm_num

/-- The correct bounded-difference estimate. -/
theorem ch7_bounded_difference (x y M : ℝ) (hx : |x| ≤ M) (hy : |y| ≤ M) :
    |x-y| ≤ 2*M := by
  calc
    |x-y| ≤ |x|+|y| := by simpa [sub_eq_add_neg] using abs_add_le x (-y)
    _ ≤ 2*M := by linarith

end Asakura.FullAudit
