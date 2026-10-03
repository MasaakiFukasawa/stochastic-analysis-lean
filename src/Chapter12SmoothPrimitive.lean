import Chapter12BoundedSmoothApproximation
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

open MeasureTheory Set
open scoped ContDiff
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000

noncomputable def smoothPrimitive (c : ℝ) (g : ℝ → ℝ) (x : ℝ) : ℝ :=
  c+∫ t in 0..x,g t

theorem smoothPrimitive_hasDerivAt (c : ℝ) (g : ℝ → ℝ) (hg : Continuous g) (x : ℝ) :
    HasDerivAt (smoothPrimitive c g) (g x) x := by
  exact (intervalIntegral.integral_hasDerivAt_right (hg.intervalIntegrable _ _)
    hg.aestronglyMeasurable.stronglyMeasurableAtFilter hg.continuousAt).const_add c

theorem smoothPrimitive_smooth (c : ℝ) (g : ℝ → ℝ) (hg : ContDiff ℝ ∞ g) :
    ContDiff ℝ ∞ (smoothPrimitive c g) := by
  apply contDiff_infty_iff_deriv.mpr
  refine ⟨fun x => (smoothPrimitive_hasDerivAt c g hg.continuous x).differentiableAt,?_⟩
  have he : deriv (smoothPrimitive c g) = g := funext fun x =>
    (smoothPrimitive_hasDerivAt c g hg.continuous x).deriv
  rw [he]
  exact hg

theorem smoothPrimitive_linear_bound (c : ℝ) (g : ℝ → ℝ)
    (C : ℝ) (hb : ∀ x, |g x| ≤ C) (x : ℝ) :
    |smoothPrimitive c g x| ≤ |c|+C*|x| := by
  apply (abs_add_le c _).trans
  apply add_le_add le_rfl
  simpa only [Real.norm_eq_abs,sub_zero] using
    (intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := x)
      (fun t _ => (show ‖g t‖ ≤ C from hb t)))

/-- A primitive of a compactly supported smooth function satisfies all
polynomial growth assumptions used for the cylinder class. -/
theorem smoothPrimitive_all_derivatives_growth (c : ℝ) (g : ℝ → ℝ)
    (hg : ContDiff ℝ ∞ g) (hs : HasCompactSupport g) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ a : ℕ, ∀ x,
      ‖iteratedFDeriv ℝ k (smoothPrimitive c g) x‖ ≤ C*(1+‖x‖)^a := by
  cases k with
  | zero =>
    obtain ⟨C,hC⟩ := hs.exists_bound_of_continuous hg.continuous
    refine ⟨|c|+max C 0,by positivity,1,fun x => ?_⟩
    rw [norm_iteratedFDeriv_zero,Real.norm_eq_abs,pow_one,Real.norm_eq_abs]
    have hb := smoothPrimitive_linear_bound c g (max C 0)
      (fun y => (hC y).trans (le_max_left _ _)) x
    nlinarith [abs_nonneg c,abs_nonneg x,le_max_right C 0]
  | succ k =>
    obtain ⟨C,hC,hb⟩ := hs.exists_bound_iteratedFDeriv hg k
    refine ⟨C,hC,0,fun x => ?_⟩
    have he : deriv (smoothPrimitive c g) = g := funext fun x =>
      (smoothPrimitive_hasDerivAt c g hg.continuous x).deriv
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv,iteratedDeriv_succ',he,
      ← norm_iteratedFDeriv_eq_norm_iteratedDeriv,pow_zero,mul_one]
    exact hb k le_rfl x

end Asakura.Chapter12
