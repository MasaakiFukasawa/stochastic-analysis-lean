import Chapter12Representation
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

open MeasureTheory ProbabilityTheory
namespace Asakura.Chapter12
set_option maxHeartbeats 600000

/-- The precise Gaussian cosine moment used in the manuscript's example. -/
theorem gaussian_cos_moment (a : ℝ) :
    (∫ z, Real.cos (a*z) ∂gaussianReal 0 1) = Real.exp (-a^2/2) := by
  have hi : Integrable (fun z : ℝ => Complex.exp ((a : ℂ)*(z : ℂ)*Complex.I))
      (gaussianReal 0 1) := by
    apply Integrable.of_bound (by fun_prop) 1
    filter_upwards [] with z
    simp [Complex.norm_exp]
  have he := congrArg Complex.re (charFun_gaussianReal (μ := 0) (v := 1) a)
  rw [charFun_apply_real] at he
  have hint : (∫ z : ℝ, Complex.exp ((a : ℂ)*(z : ℂ)*Complex.I) ∂gaussianReal 0 1).re =
      ∫ z : ℝ, (Complex.exp ((a : ℂ)*(z : ℂ)*Complex.I)).re ∂gaussianReal 0 1 :=
    (integral_re hi).symm
  rw [hint] at he
  simpa [Complex.exp_re, ← Complex.ofReal_pow,neg_div,mul_comm] using he

theorem gaussian_cos_square (a : ℝ) :
    (∫ z, (Real.cos (a*z))^2 ∂gaussianReal 0 1) =
      (1+Real.exp (-2*a^2))/2 := by
  have hi : Integrable (fun z : ℝ => Real.cos ((2*a)*z)) (gaussianReal 0 1) := by
    apply Integrable.of_bound (by fun_prop) 1
    exact ae_of_all _ fun z => Real.abs_cos_le_one _
  have hpoint : (fun z : ℝ => (Real.cos (a*z))^2) =
      fun z => (1+Real.cos ((2*a)*z))/2 := by
    funext z
    rw [mul_assoc,Real.cos_two_mul]
    ring
  rw [hpoint,integral_div,integral_add (integrable_const 1) hi,gaussian_cos_moment]
  simp only [integral_const,probReal_univ,smul_eq_mul,one_mul]
  congr 2
  congr 1
  ring

/-- Squared L2 norms of the derivative stay above one half for every n. -/
theorem gaussian_derivative_lower_bound (a : ℝ) :
    (1:ℝ)/2 ≤ ∫ z, (Real.cos (a*z))^2 ∂gaussianReal 0 1 := by
  rw [gaussian_cos_square]
  linarith [Real.exp_pos (-2*a^2)]

/-- The values of the same cylindrical functions have squared L2 norm at
most 1/n². Together these bounds rule out a bounded derivative extension. -/
theorem gaussian_sine_scaled_bound (n : ℝ) :
    (∫ z, (Real.sin (n*z)/n)^2 ∂gaussianReal 0 1) ≤ 1/n^2 := by
  have hi : Integrable (fun z : ℝ => (Real.sin (n*z)/n)^2) (gaussianReal 0 1) := by
    apply Integrable.of_bound (by fun_prop) (1/n^2)
    filter_upwards [] with z
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _),div_pow]
    exact div_le_div_of_nonneg_right (by nlinarith [Real.sin_sq_le_one (n*z)]) (sq_nonneg n)
  calc
    _ ≤ ∫ _ : ℝ, 1/n^2 ∂gaussianReal 0 1 := by
      apply integral_mono hi (integrable_const _)
      intro z
      dsimp only
      rw [div_pow]
      exact div_le_div_of_nonneg_right (Real.sin_sq_le_one _) (sq_nonneg n)
    _ = _ := by simp

theorem sine_scaled_derivative (a z : ℝ) (ha : a ≠ 0) :
    HasDerivAt (fun x => Real.sin (a*x)/a) (Real.cos (a*z)) z := by
  have h := ((hasDerivAt_id z).const_mul a).sin.div_const a
  simpa only [id_eq,mul_one,mul_div_cancel_right₀ _ ha] using h

/-- No constant controls the derivative L2 norm by the function L2 norm,
even on the one-coordinate smooth cylindrical functions used in the text. -/
theorem gaussian_derivative_not_bounded :
    ¬∃ C : ℝ, ∀ a : ℝ, 0 < a →
      (∫ z, (Real.cos (a*z))^2 ∂gaussianReal 0 1) ≤
        C^2 * (∫ z, (Real.sin (a*z)/a)^2 ∂gaussianReal 0 1) := by
  rintro ⟨C,hC⟩
  let a := 2*(|C|+1)
  have ha : 0 < a := by dsimp [a]; positivity
  have hs : 2*C^2 < a^2 := by
    dsimp [a]
    nlinarith [sq_abs C,abs_nonneg C,sq_nonneg C]
  have hquot : C^2*(1/a^2) < (1:ℝ)/2 := by
    rw [mul_one_div]
    apply (div_lt_iff₀ (sq_pos_of_pos ha)).mpr
    linarith
  have hu := (hC a ha).trans
    (mul_le_mul_of_nonneg_left (gaussian_sine_scaled_bound a) (sq_nonneg C))
  have hl := gaussian_derivative_lower_bound a
  linarith

end Asakura.Chapter12
