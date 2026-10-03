import Chapter12AsianBridgeConstruction
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

open MeasureTheory Set
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false

noncomputable def asianFirstTimeMoment (x σ r T : ℝ) (hT : 0 ≤ T)
    (f : C(Icc (0:ℝ) T,ℝ)) : ℝ :=
  ∫ s in 0..T,s*x*Real.exp ((r-σ^2/2)*s+σ*f (projIcc 0 T hT s))

/-- A pathwise positive lower bound for the stock, uniform on [0,T]. -/
theorem stock_path_lower_bound (x σ r T : ℝ) (hx : 0 < x) (hT : 0 ≤ T)
    (f : C(Icc (0:ℝ) T,ℝ)) (s : ℝ) (hs : s ∈ Icc 0 T) :
    x*Real.exp (-|r-σ^2/2| *T-|σ| *‖f‖) ≤
      x*Real.exp ((r-σ^2/2)*s+σ*f (projIcc 0 T hT s)) := by
  apply mul_le_mul_of_nonneg_left _ hx.le
  apply Real.exp_le_exp.mpr
  have hf : |f (projIcc 0 T hT s)| ≤ ‖f‖ := by
    simpa only [Real.norm_eq_abs] using f.norm_coe_le_norm (projIcc 0 T hT s)
  have h1 : |(r-σ^2/2)*s| ≤ |r-σ^2/2| *T := by
    rw [abs_mul,abs_of_nonneg hs.1]
    exact mul_le_mul_of_nonneg_left hs.2 (abs_nonneg _)
  have h2 : |σ*f (projIcc 0 T hT s)| ≤ |σ| *‖f‖ := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left hf (abs_nonneg _)
  linarith [(neg_abs_le ((r-σ^2/2)*s)),(neg_abs_le (σ*f (projIcc 0 T hT s)))]

/-- The first time moment has a strictly positive lower bound. This is the
source of every inverse moment needed for the Asian delta and vega. -/
theorem asian_first_time_moment_lower_bound (x σ r T : ℝ)
    (hx : 0 < x) (hT : 0 < T) (f : C(Icc (0:ℝ) T,ℝ)) :
    (T^2/2)*(x*Real.exp (-|r-σ^2/2| *T-|σ| *‖f‖)) ≤
      asianFirstTimeMoment x σ r T hT.le f := by
  let L := x*Real.exp (-|r-σ^2/2| *T-|σ| *‖f‖)
  have hlo : Continuous (fun s : ℝ => s*L) := by fun_prop
  have hhi : Continuous (fun s : ℝ => s*x*Real.exp
      ((r-σ^2/2)*s+σ*f (projIcc 0 T hT.le s))) := by fun_prop
  have h := intervalIntegral.integral_mono_on (μ := volume) hT.le
    (hlo.intervalIntegrable 0 T) (hhi.intervalIntegrable 0 T) (fun s hs => by
      have hb := mul_le_mul_of_nonneg_left (stock_path_lower_bound x σ r T hx hT.le f s hs) hs.1
      simpa only [L,mul_assoc] using hb)
  rw [intervalIntegral.integral_mul_const,integral_id] at h
  simpa only [sq,zero_mul,sub_zero,L,asianFirstTimeMoment] using h

theorem asian_first_time_moment_pos (x σ r T : ℝ)
    (hx : 0 < x) (hT : 0 < T) (f : C(Icc (0:ℝ) T,ℝ)) :
    0 < asianFirstTimeMoment x σ r T hT.le f := by
  apply lt_of_lt_of_le _ (asian_first_time_moment_lower_bound x σ r T hx hT f)
  positivity

end Asakura.Chapter12
