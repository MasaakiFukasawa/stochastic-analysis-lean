import Chapter5ExponentialPayoff

namespace Asakura.Chapter5

/-- Derivative bounds needed for the actual exponential payoff; no extra
boundedness assumption on the transformed derivatives is imposed. -/
theorem exponential_payoff_derivative_bounds (f df ddf : ℝ → ℝ)
    (B D E a : ℝ) (hf : ∀ x, |f x| ≤ B)
    (hdf : ∀ x, |df x| ≤ D) (hddf : ∀ x, |ddf x| ≤ E) (x : ℝ) :
    ‖a*df x*Real.exp (a*f x)‖ ≤ |a| * D*Real.exp (|a| * B) ∧
    ‖(a*ddf x+a^2*(df x)^2)*Real.exp (a*f x)‖ ≤
      (|a| * E+a^2*D^2)*Real.exp (|a| * B) := by
  have hD : 0 ≤ D := (abs_nonneg (df x)).trans (hdf x)
  have hE : 0 ≤ E := (abs_nonneg (ddf x)).trans (hddf x)
  have hex := (exponential_payoff_bounds f B a hf x).2
  constructor
  · simp only [norm_mul,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul (mul_le_mul_of_nonneg_left (hdf x) (abs_nonneg a)) hex
      (Real.exp_pos _).le (mul_nonneg (abs_nonneg a) hD)
  · have hd2 : (df x)^2 ≤ D^2 := by nlinarith [sq_abs (df x),hdf x,abs_nonneg (df x)]
    have hb : |a*ddf x+a^2*(df x)^2| ≤ |a| * E+a^2*D^2 := by
      calc
        _ ≤ |a*ddf x|+|a^2*(df x)^2| := abs_add_le _ _
        _ = |a| * |ddf x|+a^2*(df x)^2 := by
          rw [abs_mul,abs_of_nonneg (mul_nonneg (sq_nonneg a) (sq_nonneg (df x)))]
        _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left (hddf x) (abs_nonneg a))
          (mul_le_mul_of_nonneg_left hd2 (sq_nonneg a))
    simp only [norm_mul,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul hb hex (Real.exp_pos _).le (by positivity)

/-- Nonlinear heat equation for the exact formula in the manuscript,
from bounded f,f',f''. There is no assigned PDE or derivative in the input. -/
theorem bounded_coleHopf_pde (f df ddf : ℝ → ℝ)
    (hd : ∀ x, HasDerivAt f (df x) x)
    (hdd : ∀ x, HasDerivAt df (ddf x) x) (hcdd : Continuous ddf)
    (B D E a : ℝ) (hf : ∀ x, |f x| ≤ B)
    (hdf : ∀ x, |df x| ≤ D) (hddf : ∀ x, |ddf x| ≤ E)
    (ha : a ≠ 0) (x t : ℝ) (ht : 0 < t) :
    deriv (logHeat a (fun y => Real.exp (a*f y)) x) t =
      deriv (fun y => deriv (fun z => logHeat a (fun u => Real.exp (a*f u)) z t) y) x/2 +
        a/2*(deriv (fun y => logHeat a (fun u => Real.exp (a*f u)) y t) x)^2 := by
  have hcf : Continuous f := continuous_iff_continuousAt.2 (fun y => (hd y).continuousAt)
  have hcdf : Continuous df := continuous_iff_continuousAt.2 (fun y => (hdd y).continuousAt)
  apply logHeat_pde (fun y => Real.exp (a*f y))
    (fun y => a*df y*Real.exp (a*f y))
    (fun y => (a*ddf y+a^2*(df y)^2)*Real.exp (a*f y))
    (fun y => (exponential_payoff_derivatives f df ddf a hd hdd y).1)
    (fun y => (exponential_payoff_derivatives f df ddf a hd hdd y).2)
    (by fun_prop) (Real.exp (|a| * B)) (|a| * D*Real.exp (|a| * B))
    ((|a| * E+a^2*D^2)*Real.exp (|a| * B)) (Real.exp (-|a| * B)) a
  · intro y
    simpa only [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)] using
      (exponential_payoff_bounds f B a hf y).2
  · intro y;exact (exponential_payoff_derivative_bounds f df ddf B D E a hf hdf hddf y).1
  · intro y;exact (exponential_payoff_derivative_bounds f df ddf B D E a hf hdf hddf y).2
  · exact Real.exp_pos _
  · intro y;exact (exponential_payoff_bounds f B a hf y).1
  · exact ha
  · exact ht

end Asakura.Chapter5
