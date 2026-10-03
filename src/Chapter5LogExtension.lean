import Chapter3SmoothPositivePower
import Chapter5WeightedSquareCalculus

open MeasureTheory Set Filter
open scoped Topology
namespace Asakura.Chapter5
open Asakura.Chapter3Complete
set_option maxHeartbeats 1800000

/-- A global smooth logarithm extension equal to the logarithm on a
neighborhood of the positive range of the conditional exponential. -/
noncomputable def logExtension (c a x : ℝ) : ℝ := Real.log (smoothPositive (c/4) x)/a

theorem logExtension_contDiff (c a : ℝ) (hc : 0 < c) (n : ℕ) :
    ContDiff ℝ n (logExtension c a) := by
  exact ((smoothPositive_contDiff (c/4) n).log (fun x => (smoothPositive_pos (by positivity) x).ne')).div_const a

theorem logExtension_derivatives (c a x : ℝ) (hc : 0 < c) (hx : c ≤ x) :
    logExtension c a x = Real.log x/a ∧
    deriv (logExtension c a) x = 1/(a*x) ∧
    iteratedDeriv 2 (logExtension c a) x = -(1/(a*x^2)) := by
  have he : logExtension c a =ᶠ[𝓝 x] (fun y => Real.log y/a) := by
    filter_upwards [lt_mem_nhds (show c/2 < x by linarith)] with y hy
    unfold logExtension
    rw [smoothPositive_eq (by positivity) (by linarith)]
  have hx0 : x ≠ 0 := ne_of_gt (hc.trans_le hx)
  have hd y (hy : y ≠ 0) : HasDerivAt (fun z => Real.log z/a) (1/(a*y)) y := by
    convert (Real.hasDerivAt_log hy).div_const a using 1 <;> simp [div_eq_mul_inv,mul_comm]
  have hed : deriv (logExtension c a) =ᶠ[𝓝 x] (fun y => 1/(a*y)) := by
    filter_upwards [he.deriv, eventually_ne_nhds hx0] with y hy hy0
    exact hy.trans (hd y hy0).deriv
  refine ⟨he.eq_of_nhds,he.deriv_eq.trans (hd x hx0).deriv,?_⟩
  rw [iteratedDeriv_succ,iteratedDeriv_one,hed.deriv_eq]
  have hh := ((hasDerivAt_id x).inv hx0).div_const a
  convert hh.deriv using 1 <;> simp [div_eq_mul_inv,mul_comm,mul_left_comm,mul_assoc]

end Asakura.Chapter5
