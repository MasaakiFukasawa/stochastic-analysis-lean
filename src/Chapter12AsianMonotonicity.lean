import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Chapter12MonotoneFiber

open MeasureTheory Set
namespace Asakura.Chapter12

/-- With the bridge path fixed, the arithmetic average is strictly increasing
in the terminal Brownian value. This supplies the hypothesis of the fiber
argument, including the positive volatility and finite positive horizon. -/
theorem asian_average_strictMono (x σ T : ℝ) (hx : 0 < x) (hσ : 0 < σ) (hT : 0 < T)
    (c : ℝ → ℝ) (hc : ContinuousOn c (Icc 0 T)) :
    StrictMono (fun z : ℝ => (∫ s in 0..T, x*Real.exp (c s+σ*s/T*z))/T) := by
  intro z y hzy
  apply div_lt_div_of_pos_right _ hT
  apply intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt hT
  · have hcz : ContinuousOn (fun s => c s+σ*s/T*z) (Icc 0 T) := hc.add (by fun_prop)
    exact continuousOn_const.mul (Real.continuous_exp.comp_continuousOn hcz)
  · have hcy : ContinuousOn (fun s => c s+σ*s/T*y) (Icc 0 T) := hc.add (by fun_prop)
    exact continuousOn_const.mul (Real.continuous_exp.comp_continuousOn hcy)
  · intro s hs
    apply mul_le_mul_of_nonneg_left _ hx.le
    apply Real.exp_le_exp.mpr
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hzy.le
      (div_nonneg (mul_nonneg hσ.le hs.1.le) hT.le))
  · refine ⟨T,⟨hT.le,le_rfl⟩,?_⟩
    apply mul_lt_mul_of_pos_left _ hx
    apply Real.exp_lt_exp.mpr
    exact add_lt_add_of_le_of_lt le_rfl (mul_lt_mul_of_pos_left hzy (by positivity))

end Asakura.Chapter12
