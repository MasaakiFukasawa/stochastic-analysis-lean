import Chapter12ReciprocalRegularizer

namespace Asakura.Chapter12
set_option maxHeartbeats 1800000

theorem reciprocal_square_regularizer_hasDerivAt (ε:ℝ) (hε:0<ε) (x:ℝ) :
    HasDerivAt (reciprocalSquareRegularizer ε)
      (((-2*x)*reciprocalSquareRegularizer ε x)*reciprocalSquareRegularizer ε x) x := by
  have hh := (reciprocal_square_regularizer_smooth ε hε).differentiable (by simp) x |>.hasDerivAt
  rw [reciprocal_square_regularizer_deriv ε hε] at hh
  exact hh

theorem reciprocal_square_regularizer_derivative_bound (ε:ℝ) (hε:0<ε) (x:ℝ) :
    |((-2*x)*reciprocalSquareRegularizer ε x)*reciprocalSquareRegularizer ε x|≤
      2*(1+ε⁻¹)*ε⁻¹ := by
  have hd:0<x^2+ε := by positivity
  have hi:0<ε⁻¹ := inv_pos.mpr hε
  have hxe:|x|≤1+x^2 := by
    have hh := sq_nonneg (|x|-1)
    nlinarith [sq_abs x]
  have hden : ε≤x^2+ε := by nlinarith [sq_nonneg x]
  have hbound : |x|≤(1+ε⁻¹)*(x^2+ε) := by
    have he:ε⁻¹*ε=1 := inv_mul_cancel₀ hε.ne'
    nlinarith [mul_nonneg hi.le (sq_nonneg x)]
  have h1 : |x| *(x^2+ε)⁻¹≤1+ε⁻¹ := by
    exact (mul_inv_le_iff₀ hd).mpr hbound
  have h2 : (x^2+ε)⁻¹≤ε⁻¹ := inv_anti₀ hε hden
  calc
    _ = 2*(|x| *(x^2+ε)⁻¹)*(x^2+ε)⁻¹ := by
      simp only [reciprocalSquareRegularizer,abs_mul,abs_neg,abs_of_pos (by norm_num : (0:ℝ)<2),
        abs_of_pos (inv_pos.mpr hd)]
      ring
    _ ≤ 2*(1+ε⁻¹)*ε⁻¹ :=
      mul_le_mul (mul_le_mul_of_nonneg_left h1 (by norm_num)) h2
        (by positivity) (by positivity)
end Asakura.Chapter12
#print axioms Asakura.Chapter12.reciprocal_square_regularizer_derivative_bound
