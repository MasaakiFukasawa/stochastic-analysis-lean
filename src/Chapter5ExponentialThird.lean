import Chapter5BurgersHeat

namespace Asakura.Chapter5
set_option maxHeartbeats 800000

theorem exponential_payoff_third_derivative (f df ddf dddf : ℝ → ℝ) (a : ℝ)
    (hd : ∀ x, HasDerivAt f (df x) x)
    (hdd : ∀ x, HasDerivAt df (ddf x) x)
    (hddd : ∀ x, HasDerivAt ddf (dddf x) x) (x : ℝ) :
    HasDerivAt (fun y => (a*ddf y+a^2*(df y)^2)*Real.exp (a*f y))
      ((a*dddf x+3*a^2*df x*ddf x+a^3*(df x)^3)*Real.exp (a*f x)) x := by
  have hc := ((hddd x).const_mul a).add (((hdd x).pow 2).const_mul (a^2))
  convert hc.mul (((hd x).const_mul a).exp) using 1 <;> simp only [Pi.add_apply,Pi.pow_apply] <;> ring

theorem exponential_payoff_third_bound (f df ddf dddf : ℝ → ℝ)
    (B D E G a : ℝ) (hf : ∀ x, |f x| ≤ B)
    (hdf : ∀ x, |df x| ≤ D) (hddf : ∀ x, |ddf x| ≤ E)
    (hdddf : ∀ x, |dddf x| ≤ G) (x : ℝ) :
    ‖(a*dddf x+3*a^2*df x*ddf x+a^3*(df x)^3)*Real.exp (a*f x)‖ ≤
      (|a| * G+3*a^2*D*E+|a|^3*D^3)*Real.exp (|a| * B) := by
  have hD : 0 ≤ D := (abs_nonneg (df x)).trans (hdf x)
  have hE : 0 ≤ E := (abs_nonneg (ddf x)).trans (hddf x)
  have hG : 0 ≤ G := (abs_nonneg (dddf x)).trans (hdddf x)
  have hc : |a*dddf x+3*a^2*df x*ddf x+a^3*(df x)^3| ≤
      |a| * G+3*a^2*D*E+|a|^3*D^3 := by
    calc
      _ ≤ |a*dddf x|+|3*a^2*df x*ddf x|+|a^3*(df x)^3| :=
        (abs_add_le _ _).trans (add_le_add_left (abs_add_le _ _) _)
      _ = |a| * |dddf x|+3*a^2*|df x| * |ddf x|+|a|^3*|df x|^3 := by
        norm_num [abs_mul,abs_pow,sq_abs]
      _ ≤ _ := by gcongr <;> first | exact hdf x | exact hddf x | exact hdddf x
  simp only [norm_mul,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  exact mul_le_mul hc (exponential_payoff_bounds f B a hf x).2
    (Real.exp_pos _).le (by positivity)

end Asakura.Chapter5
