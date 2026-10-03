import Chapter3SmoothPositivePower
import Mathlib.Analysis.InnerProductSpace.NormPow
import Mathlib.Analysis.Calculus.Deriv.Slope

open Set Filter
open scoped Topology
namespace Asakura.Chapter3Complete
set_option maxHeartbeats 2200000

/-- The derivative needed to check C² regularity of |x|^p at zero. -/
theorem hasDerivAt_mul_abs_rpow (q : ℝ) (hq : 0 < q) (x : ℝ) :
    HasDerivAt (fun y : ℝ => y*|y|^q) ((q+1)*|x|^q) x := by
  rcases lt_trichotomy x 0 with hx|hx|hx
  · have hd := (((hasDerivAt_id x).neg).rpow_const
      (p := q+1) (Or.inl (neg_ne_zero.mpr hx.ne))).neg
    have he : (fun y : ℝ => -((-y)^(q+1))) =ᶠ[𝓝 x] (fun y => y*|y|^q) := by
      filter_upwards [gt_mem_nhds hx] with y hy
      rw [abs_of_neg hy,Real.rpow_add_one (neg_ne_zero.mpr hy.ne)]
      ring
    have h := hd.congr_of_eventuallyEq he.symm
    convert h using 1 <;> simp only [abs_of_neg hx,add_sub_cancel_right,Pi.neg_apply,id_eq] <;> ring
  · subst x
    simp only [abs_zero,Real.zero_rpow hq.ne',mul_zero]
    rw [hasDerivAt_iff_tendsto]
    have he y : ‖y-0‖⁻¹*‖y*|y|^q-0*|0|^q-(y-0) • (0:ℝ)‖ = |y|^q := by
      by_cases hy : y = 0
      · simp [hy,Real.zero_rpow hq.ne']
      · simp only [sub_zero,zero_mul,smul_zero,Real.norm_eq_abs,abs_mul,
          abs_of_nonneg (Real.rpow_nonneg (abs_nonneg y) q)]
        field_simp
    simp_rw [he]
    simpa only [abs_zero,Real.zero_rpow hq.ne'] using
      (continuous_abs.rpow_const (fun _ => Or.inr hq.le)).continuousAt.tendsto (x := (0:ℝ))
  · have hd := Real.hasDerivAt_rpow_const (x := x) (p := q+1) (Or.inl hx.ne')
    have he : (fun y : ℝ => y^(q+1)) =ᶠ[𝓝 x] (fun y => y*|y|^q) := by
      filter_upwards [lt_mem_nhds hx] with y hy
      rw [abs_of_pos hy,Real.rpow_add_one hy.ne']
      ring
    have h := hd.congr_of_eventuallyEq he.symm
    simpa only [abs_of_pos hx,add_sub_cancel_right] using h

/-- The exact first and second derivatives used in the p>2 BDG argument. -/
theorem absolute_power_C2 (p : ℝ) (hp : 2 < p) :
    ContDiff ℝ 2 (fun x : ℝ => |x|^p) ∧
    (∀ x, deriv (fun y : ℝ => |y|^p) x = p*|x|^(p-2)*x) ∧
    (∀ x, iteratedDeriv 2 (fun y : ℝ => |y|^p) x = p*(p-1)*|x|^(p-2)) := by
  have hp1 : 1 < p := by linarith
  have hd x := hasDerivAt_abs_rpow x hp1
  have hde : deriv (fun y : ℝ => |y|^p) = fun x => p*(x*|x|^(p-2)) := by
    funext x
    rw [(hd x).deriv]
    ring
  have hdd x : HasDerivAt (deriv (fun y : ℝ => |y|^p)) (p*(p-1)*|x|^(p-2)) x := by
    rw [hde]
    convert (hasDerivAt_mul_abs_rpow (p-2) (by linarith) x).const_mul p using 1 <;> ring
  have hddc : Continuous (deriv (deriv (fun y : ℝ => |y|^p))) := by
    have he : deriv (deriv (fun y : ℝ => |y|^p)) = fun x => p*(p-1)*|x|^(p-2) :=
      funext (fun x => (hdd x).deriv)
    rw [he]
    exact continuous_const.mul (continuous_abs.rpow_const (fun _ => Or.inr (by linarith)))
  refine ⟨?_,fun x => (hd x).deriv,?_⟩
  · rw [show (2 : WithTop ℕ∞) = 1+1 by norm_num,contDiff_succ_iff_deriv]
    refine ⟨fun x => (hd x).differentiableAt,by simp,?_⟩
    exact contDiff_one_iff_deriv.mpr ⟨fun x => (hdd x).differentiableAt,hddc⟩
  · intro x
    simpa only [iteratedDeriv_succ,iteratedDeriv_zero] using (hdd x).deriv

end Asakura.Chapter3Complete
#print axioms Asakura.Chapter3Complete.hasDerivAt_mul_abs_rpow
#print axioms Asakura.Chapter3Complete.absolute_power_C2
