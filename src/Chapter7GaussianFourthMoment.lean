import GaussianMoments
import Mathlib.Analysis.Calculus.Deriv.Polynomial

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
namespace Asakura.Chapter7

/-- The fourth moment used in the covariance estimator proof, derived from the
Gaussian moment generating function, including zero variance. -/
theorem gaussian_fourth_moment (v : ℝ≥0) :
    ∫ x : ℝ, x^4 ∂gaussianReal 0 v = 3*(v:ℝ)^2 := by
  have d0 (t : ℝ) : HasDerivAt (fun t : ℝ => Real.exp ((v:ℝ)*t^2/2))
      ((v:ℝ)*t*Real.exp ((v:ℝ)*t^2/2)) t := by
    convert (((hasDerivAt_id t).pow 2).const_mul (v:ℝ) |>.div_const 2).exp using 1
    · funext x; rfl
    · dsimp; ring
  have d1 (t : ℝ) : HasDerivAt (fun t : ℝ => (v:ℝ)*t*Real.exp ((v:ℝ)*t^2/2))
      (((v:ℝ)+(v:ℝ)^2*t^2)*Real.exp ((v:ℝ)*t^2/2)) t := by
    convert ((hasDerivAt_id t).const_mul (v:ℝ)).mul (d0 t) using 1
    · funext x; rfl
    · dsimp; ring
  have d2 (t : ℝ) : HasDerivAt
      (fun t : ℝ => ((v:ℝ)+(v:ℝ)^2*t^2)*Real.exp ((v:ℝ)*t^2/2))
      ((3*(v:ℝ)^2*t+(v:ℝ)^3*t^3)*Real.exp ((v:ℝ)*t^2/2)) t := by
    convert ((hasDerivAt_const t (v:ℝ)).add (((hasDerivAt_id t).pow 2).const_mul ((v:ℝ)^2))).mul (d0 t) using 1
    · funext x; rfl
    · dsimp; ring
  have d3 (t : ℝ) : HasDerivAt
      (fun t : ℝ => (3*(v:ℝ)^2*t+(v:ℝ)^3*t^3)*Real.exp ((v:ℝ)*t^2/2))
      ((3*(v:ℝ)^2+6*(v:ℝ)^3*t^2+(v:ℝ)^4*t^4)*Real.exp ((v:ℝ)*t^2/2)) t := by
    convert (((hasDerivAt_id t).const_mul (3*(v:ℝ)^2)).add
      (((hasDerivAt_id t).pow 3).const_mul ((v:ℝ)^3))).mul (d0 t) using 1
    · funext x; rfl
    · dsimp; ring
  have e0 := funext (fun t => (d0 t).deriv)
  have e1 := funext (fun t => (d1 t).deriv)
  have e2 := funext (fun t => (d2 t).deriv)
  have e3 := funext (fun t => (d3 t).deriv)
  calc
    _ = iteratedDeriv 4 (mgf (fun x : ℝ => x) (gaussianReal 0 v)) 0 := by
      rw [iteratedDeriv_mgf_zero] <;> simp
    _ = _ := by
      rw [mgf_fun_id_gaussianReal]
      simp only [zero_mul, zero_add]
      rw [iteratedDeriv_succ', e0, iteratedDeriv_succ', e1,
        iteratedDeriv_succ', e2, iteratedDeriv_one, e3]
      simp

end Asakura.Chapter7
