import Chapter4NormalCDF
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

open MeasureTheory ProbabilityTheory
namespace Asakura.Chapter11
open Asakura.Chapter4
set_option maxHeartbeats 2200000

/-- The discontinuous bounded payoff used before the image subtraction. -/
theorem barrier_truncated_payoff (x K b : ℝ) (hKb : K<b) (hxb : x≠b) :
    max (x-K) 0-max (x-b) 0-(b-K)*(if b<x then 1 else 0)=
      if x<b then max (x-K) 0 else 0 := by
  by_cases h : x<b
  · simp only [h,ite_true,not_lt_of_ge h.le,ite_false,mul_zero,sub_zero,
      max_eq_right (sub_nonpos.mpr h.le)]
  · have hx : b<x := lt_of_le_of_ne (le_of_not_gt h) (Ne.symm hxb)
    rw [if_pos hx,if_neg h,max_eq_left (sub_nonneg.mpr (hKb.le.trans hx.le)),
      max_eq_left (sub_nonneg.mpr hx.le)]
    ring

/-- Differentiate the actual digital Black--Scholes price. -/
theorem barrier_digital_delta (b r σ θ x : ℝ) (hb : b≠0) (hx : x≠0) :
    HasDerivAt (fun x => Real.exp (-r*θ)*normalCDF (bsD b (r-σ^2/2) σ x θ))
      (Real.exp (-r*θ)/(x*σ*Real.sqrt θ)*gaussianPDFReal 0 1 (bsD b (r-σ^2/2) σ x θ)) x := by
  have hh := ((normalCDF_hasDerivAt _).comp x
    (bsD_spatial_derivative b (r-σ^2/2) σ x θ hb hx)).const_mul (Real.exp (-r*θ))
  convert hh using 1
  · rfl
  · ring

/-- Differentiate the reflected price in the original stock coordinate,
including both the weight derivative and inverse-coordinate derivative. -/
theorem barrier_price_delta (b ν x : ℝ) (hb : 0<b) (hx : 0<x)
    (v : ℝ → ℝ) (dvx dvz : ℝ) (hvx : HasDerivAt v dvx x)
    (hvz : HasDerivAt v dvz (b^2/x)) :
    HasDerivAt (fun y => v y-(b/y)^ν*v (b^2/y))
      (dvx+(b/x)^ν*(ν/x*v (b^2/x)+b^2/x^2*dvz)) x := by
  have hi := (hasDerivAt_const x b).div (hasDerivAt_id x) hx.ne'
  have hp := (Real.hasDerivAt_rpow_const (p:=ν) (Or.inl (div_pos hb hx).ne')).comp x hi
  have hz := hvz.comp x ((hasDerivAt_const x (b^2)).div (hasDerivAt_id x) hx.ne')
  have hh := hvx.sub (hp.mul hz)
  have he : (b/x)^(ν-1)=(b/x)^ν/(b/x) := by rw [Real.rpow_sub (div_pos hb hx),Real.rpow_one]
  convert hh using 1
  · rfl
  · simp only [Function.comp_def,id_eq,mul_one,zero_mul,zero_sub,he]
    field_simp
    ring

end Asakura.Chapter11
