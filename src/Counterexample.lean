import Appendix
import Mathlib.Analysis.SpecialFunctions.Complex.Log
open Complex
namespace Asakura
/-- C.1: the printed characteristic-function identity fails for principal log,
even for the deterministic Gaussian X=1, at u=2*pi. -/
theorem principal_log_gaussian_counterexample :
    Complex.log (Complex.exp (2 * (Real.pi : ℂ) * Complex.I)) ≠
      2 * (Real.pi : ℂ) * Complex.I := by
  rw [Complex.exp_two_pi_mul_I, Complex.log_one]
  have h : 2 * (Real.pi : ℂ) * Complex.I ≠ 0 := by
    apply mul_ne_zero
    · exact mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)
    · exact Complex.I_ne_zero
  exact Ne.symm h
end Asakura
