import Chapter5LogHeat

open MeasureTheory ProbabilityTheory
namespace Asakura.Chapter5
open Asakura.FullAudit

/-- Bounded terminal payoffs give a uniform strictly positive lower bound,
not just pointwise positivity; this justifies dividing the martingale by X. -/
theorem exponential_payoff_bounds (f : ℝ → ℝ) (B a : ℝ)
    (hf : ∀ x, |f x| ≤ B) (x : ℝ) :
    Real.exp (-|a| * B) ≤ Real.exp (a*f x) ∧
      Real.exp (a*f x) ≤ Real.exp (|a| * B) := by
  have h : |a*f x| ≤ |a| * B := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hf x) (abs_nonneg a)
  constructor <;> apply Real.exp_le_exp.mpr
  · have := neg_abs_le (a*f x); nlinarith
  · exact (le_abs_self _).trans h

/-- The lower bound survives the Gaussian convolution, uniformly in x,t. -/
theorem exponential_heat_positive (f : ℝ → ℝ) (hc : Continuous f)
    (B a : ℝ) (hf : ∀ x, |f x| ≤ B) (x t : ℝ) :
    0 < Real.exp (-|a| * B) ∧
    Real.exp (-|a| * B) ≤ heatAverage (fun y => Real.exp (a*f y)) x t := by
  refine ⟨Real.exp_pos _,?_⟩
  apply heatAverage_lower_bound _ (by fun_prop) (Real.exp (|a| * B)) _
  · intro y
    simpa only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using
      (exponential_payoff_bounds f B a hf y).2
  · intro y
    exact (exponential_payoff_bounds f B a hf y).1

/-- The first two derivatives of the actual transformed payoff. -/
theorem exponential_payoff_derivatives (f df ddf : ℝ → ℝ) (a : ℝ)
    (hd : ∀ x, HasDerivAt f (df x) x)
    (hdd : ∀ x, HasDerivAt df (ddf x) x) (x : ℝ) :
    HasDerivAt (fun y => Real.exp (a*f y)) (a*df x*Real.exp (a*f x)) x ∧
    HasDerivAt (fun y => a*df y*Real.exp (a*f y))
      ((a*ddf x+a^2*(df x)^2)*Real.exp (a*f x)) x := by
  have h0 := ((hd x).const_mul a).exp
  constructor
  · convert h0 using 1 <;> ring
  · convert ((hdd x).const_mul a).mul h0 using 1 <;> ring

/-- Initial data of the explicit nonlinear heat solution. -/
theorem exponential_logHeat_initial (f : ℝ → ℝ) (a x : ℝ) (ha : a ≠ 0) :
    logHeat a (fun y => Real.exp (a*f y)) x 0 = f x := by
  rw [logHeat,heatAverage_zero]
  exact coleHopf_terminal a (f x) ha

end Asakura.Chapter5
