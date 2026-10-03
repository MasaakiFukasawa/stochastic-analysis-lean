import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Filter
open scoped Topology
namespace Asakura.Chapter12

noncomputable def smoothCall (ε K x : ℝ) : ℝ :=
  ((x-K)+Real.sqrt ((x-K)^2+ε^2))/2

noncomputable def smoothCallSlope (ε K x : ℝ) : ℝ :=
  (1+(x-K)/Real.sqrt ((x-K)^2+ε^2))/2

/-- Explicit smooth positive-part approximation, including its derivative. -/
theorem smoothCall_derivative (ε K x : ℝ) (hε : 0 < ε) :
    HasDerivAt (smoothCall ε K) (smoothCallSlope ε K x) x := by
  have hy : HasDerivAt (fun x : ℝ => x-K) 1 x := (hasDerivAt_id x).sub_const K
  have hp : (x-K)^2+ε^2 ≠ 0 := ne_of_gt (by positivity)
  have hr : HasDerivAt (fun y : ℝ => (y-K)^2+ε^2) (2*(x-K)) x := by
    convert (hy.pow 2).add_const (ε^2) using 1 <;> simp
  have hs := HasDerivAt.sqrt hr hp
  unfold smoothCall smoothCallSlope
  convert (hy.add hs).div_const 2 using 1 <;> ring

/-- Uniform approximation of the kink; the payoff error is at most ε/2. -/
theorem smoothCall_error (ε K x : ℝ) (hε : 0 ≤ ε) :
    0 ≤ smoothCall ε K x-max (x-K) 0 ∧
    smoothCall ε K x-max (x-K) 0 ≤ ε/2 := by
  have hs0 : 0 ≤ Real.sqrt ((x-K)^2+ε^2) := Real.sqrt_nonneg _
  have hs2 : (Real.sqrt ((x-K)^2+ε^2))^2 = (x-K)^2+ε^2 := Real.sq_sqrt (by positivity)
  have ha : |x-K|^2 = (x-K)^2 := sq_abs _
  have hlo : |x-K| ≤ Real.sqrt ((x-K)^2+ε^2) := by nlinarith [sq_nonneg ε,abs_nonneg (x-K)]
  have hhi : Real.sqrt ((x-K)^2+ε^2) ≤ |x-K|+ε := by nlinarith [abs_nonneg (x-K),mul_nonneg (abs_nonneg (x-K)) hε]
  unfold smoothCall
  by_cases hx : 0 ≤ x-K
  · rw [max_eq_left hx,abs_of_nonneg hx] at *
    constructor <;> linarith
  · have hx' : x-K ≤ 0 := le_of_not_ge hx
    rw [max_eq_right hx',abs_of_nonpos hx'] at *
    constructor <;> linarith

/-- The derivative is bounded between zero and one uniformly in ε. -/
theorem smoothCall_slope_bounds (ε K x : ℝ) (hε : 0 < ε) :
    0 ≤ smoothCallSlope ε K x ∧ smoothCallSlope ε K x ≤ 1 := by
  have hs : 0 < Real.sqrt ((x-K)^2+ε^2) := Real.sqrt_pos.mpr (by positivity)
  have hs2 := Real.sq_sqrt (show 0 ≤ (x-K)^2+ε^2 by positivity)
  have ha : |x-K| ≤ Real.sqrt ((x-K)^2+ε^2) := by nlinarith [sq_abs (x-K),abs_nonneg (x-K),sq_nonneg ε]
  have hlo : -1 ≤ (x-K)/Real.sqrt ((x-K)^2+ε^2) := (le_div_iff₀ hs).mpr (by linarith [(abs_le.mp ha).1])
  have hhi : (x-K)/Real.sqrt ((x-K)^2+ε^2) ≤ 1 := (div_le_iff₀ hs).mpr (by linarith [(abs_le.mp ha).2])
  unfold smoothCallSlope
  constructor <;> linarith

/-- Away from the strike the derivative tends to the indicator used for
basket and Asian call payoffs. -/
theorem smoothCall_slope_limit (K x : ℝ) (hx : x ≠ K)
    (ε : ℕ → ℝ) (hε : Tendsto ε atTop (𝓝 0)) :
    Tendsto (fun n => smoothCallSlope (ε n) K x) atTop
      (𝓝 (if K < x then (1:ℝ) else 0)) := by
  have hden : Real.sqrt ((x-K)^2) ≠ 0 := by
    rw [Real.sqrt_sq_eq_abs]
    exact abs_ne_zero.mpr (sub_ne_zero.mpr hx)
  have hs : Tendsto (fun n => Real.sqrt ((x-K)^2+(ε n)^2)) atTop
      (𝓝 (Real.sqrt ((x-K)^2))) := by
    simpa only [Function.comp_def,zero_pow (by norm_num : 2 ≠ 0),add_zero] using Real.continuous_sqrt.continuousAt.tendsto.comp
      (tendsto_const_nhds.add (hε.pow 2))
  have ht : Tendsto (fun n => (1+(x-K)/Real.sqrt ((x-K)^2+(ε n)^2))/2) atTop
      (𝓝 ((1+(x-K)/Real.sqrt ((x-K)^2))/2)) :=
    (tendsto_const_nhds.add (tendsto_const_nhds.div hs hden)).div_const (2:ℝ)
  change Tendsto (fun n => smoothCallSlope (ε n) K x) atTop
    (𝓝 ((1+(x-K)/Real.sqrt ((x-K)^2))/2)) at ht
  convert ht using 1
  rw [Real.sqrt_sq_eq_abs]
  by_cases h : K < x
  · simp [h,abs_of_pos (sub_pos.mpr h),div_self (sub_ne_zero.mpr hx)]
  · have hh : x-K < 0 := sub_neg.mpr (lt_of_le_of_ne (le_of_not_gt h) hx)
    rw [if_neg h,abs_of_neg hh,div_neg,div_self (sub_ne_zero.mpr hx)]
    norm_num

end Asakura.Chapter12
