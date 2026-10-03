import FullAuditHeatLine
import Mathlib.Analysis.Calculus.MeanValue

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal
namespace Asakura.FullAudit

/-- The manuscript's mean-value bound, including the closed time-zero endpoint. -/
theorem HeatTest.segment_increment_bound (f : HeatTest) (k : ℕ) (x t u v s : ℝ)
    (hv : 0 ≤ v) (hvt : v ≤ t) (hs : s ∈ Icc (0:ℝ) 1) :
    |heatAverage (f.F k) (x+s*u) (t-s*v)-heatAverage (f.F k) x t| ≤
      (f.C (k+1)+f.C (k+2))*(|u|+v)*s := by
  have hb : ∀ r ∈ Ico (0:ℝ) 1,
      ‖u*heatAverage (f.F (k+1)) (x+r*u) (t-r*v)-
        (v/2)*heatAverage (f.F (k+2)) (x+r*u) (t-r*v)‖ ≤
        (f.C (k+1)+f.C (k+2))*(|u|+v) := by
    intro r _
    have h1 := heatAverage_bound (f.continuous (k+1)) (f.C (k+1)) (f.bound (k+1)) (x+r*u) (t-r*v)
    have h2 := heatAverage_bound (f.continuous (k+2)) (f.C (k+2)) (f.bound (k+2)) (x+r*u) (t-r*v)
    calc
      _ ≤ ‖u*heatAverage (f.F (k+1)) (x+r*u) (t-r*v)‖+
          ‖(v/2)*heatAverage (f.F (k+2)) (x+r*u) (t-r*v)‖ := norm_sub_le _ _
      _ ≤ |u| *f.C (k+1)+(v/2)*f.C (k+2) := by
        rw [norm_mul,norm_mul,Real.norm_eq_abs u,Real.norm_eq_abs (v/2),abs_of_nonneg (show 0 ≤ v/2 by positivity)]
        exact add_le_add (mul_le_mul_of_nonneg_left h1 (abs_nonneg u))
          (mul_le_mul_of_nonneg_left h2 (by positivity))
      _ ≤ _ := by
        nlinarith [mul_nonneg (f.bound_nonneg (k+1)) hv,
          mul_nonneg (f.bound_nonneg (k+2)) (abs_nonneg u),mul_nonneg (f.bound_nonneg (k+2)) hv]
  have h := norm_image_sub_le_of_norm_deriv_right_le_segment
    (f.segment_continuous k x t u v).continuousOn
    (fun r hr => (f.segment_derivative k x t u v r hv hvt hr).hasDerivWithinAt) hb s hs
  simpa only [Real.norm_eq_abs,zero_mul,add_zero,sub_zero] using h

/-- Actual bounded heat derivatives supply every hypothesis of the Hessian
estimate; no remainder estimate is assumed here. -/
theorem HeatTest.hessian_remainder_estimate (f : HeatTest) (x t u v ε : ℝ)
    (hv : 0 ≤ v) (hvt : v ≤ t) (hε : 0 < ε) (hvε : v ≤ ε) :
    |cltHessianRemainder
      (fun s => heatAverage (f.F 2) (x+s*u) (t-s*v))
      (fun s => (1/2)*heatAverage (f.F 3) (x+s*u) (t-s*v))
      (fun s => (1/4)*heatAverage (f.F 4) (x+s*u) (t-s*v)) u v| ≤
      (f.C 2+f.C 3+f.C 4)*(v^2+v*|u|+(if ε ≤ |u| then u^2 else 0))+
        ε*(f.C 3+f.C 4)*u^2 := by
  have h2 := f.bound_nonneg 2
  have h3 := f.bound_nonneg 3
  have h4 := f.bound_nonneg 4
  apply clt_hessian_lindeberg_bound _ _ _ (f.segment_continuous 2 x t u v).continuousOn
    ((f.segment_continuous 3 x t u v).const_mul (1/2)).continuousOn
    ((f.segment_continuous 4 x t u v).const_mul (1/4)).continuousOn
    _ _ u v ε (by positivity) (by positivity) hv hε hvε
  · intro s _
    have h := heatAverage_bound (f.continuous 2) (f.C 2) (f.bound 2) (x+s*u) (t-s*v)
    rw [Real.norm_eq_abs] at h
    linarith
  · intro s _
    have h := heatAverage_bound (f.continuous 3) (f.C 3) (f.bound 3) (x+s*u) (t-s*v)
    rw [Real.norm_eq_abs] at h
    rw [abs_mul,abs_of_pos (by norm_num : (0:ℝ) < 1/2)]
    linarith
  · intro s _
    have h := heatAverage_bound (f.continuous 4) (f.C 4) (f.bound 4) (x+s*u) (t-s*v)
    rw [Real.norm_eq_abs] at h
    rw [abs_mul,abs_of_pos (by norm_num : (0:ℝ) < 1/4)]
    linarith
  · intro s hs
    simpa only [zero_mul,add_zero,sub_zero] using f.segment_increment_bound 2 x t u v s hv hvt hs

end Asakura.FullAudit
