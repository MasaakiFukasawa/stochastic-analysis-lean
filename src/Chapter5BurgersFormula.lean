import Chapter5ExponentialThird

namespace Asakura.Chapter5
open Asakura.FullAudit

/-- Explicit Burgers solution built from the manuscript's bounded smooth
primitive. This verifies the PDE and the initial condition of the actual
Gaussian integral formula (separately from its stochastic representation). -/
theorem bounded_burgers_formula (f df ddf dddf : ℝ → ℝ)
    (hd : ∀ x, HasDerivAt f (df x) x)
    (hdd : ∀ x, HasDerivAt df (ddf x) x)
    (hddd : ∀ x, HasDerivAt ddf (dddf x) x) (hcddd : Continuous dddf)
    (B D E G a : ℝ) (hf : ∀ x, |f x| ≤ B)
    (hdf : ∀ x, |df x| ≤ D) (hddf : ∀ x, |ddf x| ≤ E)
    (hdddf : ∀ x, |dddf x| ≤ G) (ha : a ≠ 0) :
    let v := heatRatio a (fun y => Real.exp (a*f y))
      (fun y => a*df y*Real.exp (a*f y))
    (∀ x, v x 0 = df x) ∧
    (∀ x t, 0 < t → deriv (v x) t =
      deriv (fun y => deriv (fun z => v z t) y) x/2 +
      a*v x t*deriv (fun y => v y t) x) := by
  dsimp only
  constructor
  · intro x
    simp only [heatRatio,heatAverage_zero]
    have he := (Real.exp_pos (a*f x)).ne'
    field_simp
  · intro x t ht
    have hcf : Continuous f := continuous_iff_continuousAt.2 (fun y => (hd y).continuousAt)
    have hcdf : Continuous df := continuous_iff_continuousAt.2 (fun y => (hdd y).continuousAt)
    have hcddf : Continuous ddf := continuous_iff_continuousAt.2 (fun y => (hddd y).continuousAt)
    apply heatRatio_burgers (fun y => Real.exp (a*f y))
      (fun y => a*df y*Real.exp (a*f y))
      (fun y => (a*ddf y+a^2*(df y)^2)*Real.exp (a*f y))
      (fun y => (a*dddf y+3*a^2*df y*ddf y+a^3*(df y)^3)*Real.exp (a*f y))
      (fun y => (exponential_payoff_derivatives f df ddf a hd hdd y).1)
      (fun y => (exponential_payoff_derivatives f df ddf a hd hdd y).2)
      (exponential_payoff_third_derivative f df ddf dddf a hd hdd hddd)
      (by fun_prop) (Real.exp (|a| * B)) (|a| * D*Real.exp (|a| * B))
      ((|a| * E+a^2*D^2)*Real.exp (|a| * B))
      ((|a| * G+3*a^2*D*E+|a|^3*D^3)*Real.exp (|a| * B)) (Real.exp (-|a| * B)) a
    · intro y
      simpa only [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)] using
        (exponential_payoff_bounds f B a hf y).2
    · intro y;exact (exponential_payoff_derivative_bounds f df ddf B D E a hf hdf hddf y).1
    · intro y;exact (exponential_payoff_derivative_bounds f df ddf B D E a hf hdf hddf y).2
    · intro y;exact exponential_payoff_third_bound f df ddf dddf B D E G a hf hdf hddf hdddf y
    · exact Real.exp_pos _
    · intro y;exact (exponential_payoff_bounds f B a hf y).1
    · exact ha
    · exact ht

end Asakura.Chapter5
