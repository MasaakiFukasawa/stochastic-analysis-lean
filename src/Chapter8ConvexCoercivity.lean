import Chapter8AveragedHessian
import FullAuditLangevinPaths

open Set MeasureTheory
open scoped RealInnerProductSpace
namespace Asakura.Chapter8
open Asakura.FullAudit
set_option maxHeartbeats 400000

/-- Integrate the Hessian lower bound twice, retaining the affine term at zero. -/
theorem strongly_convex_quadratic_lower_bound {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (U : E → ℝ) (g : E → E) (H : E → E →L[ℝ] E) (κ : ℝ)
    (hU : ∀ x, HasFDerivAt U (innerSL ℝ (g x)) x)
    (hg : ∀ x, HasFDerivAt g (H x) x)
    (hH : ∀ x v, κ*‖v‖^2 ≤ ⟪v,H x v⟫) (x : E) :
    U 0+⟪g 0,x⟫+κ/2*‖x‖^2 ≤ U x := by
  let f := fun s : ℝ => U (s • x)-s*⟪g 0,x⟫-κ/2*s^2*‖x‖^2
  have hd (s : ℝ) : HasDerivAt f
      (⟪g (s • x),x⟫-⟪g 0,x⟫-κ*s*‖x‖^2) s := by
    have hu := (hU (s • x)).comp_hasDerivAt s ((hasDerivAt_id s).smul_const x)
    have hh := (hu.sub ((hasDerivAt_id s).mul_const ⟪g 0,x⟫)).sub
      ((((hasDerivAt_id s).pow 2).const_mul (κ/2)).mul_const (‖x‖^2))
    convert hh using 1
    · rfl
    · simp only [innerSL_apply_apply,one_smul,one_mul,id_eq,Nat.cast_ofNat,
        show (2:ℕ)-1=1 by rfl,pow_one,mul_one]
      ring
  have hpos (s : ℝ) (hs : 0 < s) : 0 ≤ ⟪g (s • x),x⟫-⟪g 0,x⟫-κ*s*‖x‖^2 := by
    have hh := langevin_gradient_monotone g H κ hg hH (s • x) 0
    simp only [sub_zero,real_inner_smul_left,inner_sub_right,norm_smul,
      Real.norm_eq_abs,abs_of_pos hs,mul_pow] at hh
    rw [real_inner_comm (g (s • x)) x,real_inner_comm (g 0) x] at hh
    nlinarith
  have hf : MonotoneOn f (Icc 0 1) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 1)
      ((continuous_iff_continuousAt.mpr (fun s => (hd s).continuousAt)).continuousOn)
    · intro s hs
      exact (hd s).differentiableAt.differentiableWithinAt
    · intro s hs
      rw [(hd s).deriv]
      apply hpos s
      have hh : s ∈ Ioo (0:ℝ) 1 := by simpa using hs
      exact hh.1
  have hh := hf (by simp : (0:ℝ) ∈ Icc 0 1) (by simp : (1:ℝ) ∈ Icc 0 1) zero_le_one
  dsimp only [f] at hh
  simp only [zero_smul,one_smul,zero_mul,one_mul,zero_pow (by norm_num : (2:ℕ) ≠ 0),
    one_pow,mul_zero,mul_one,sub_zero] at hh
  linarith

/-- Completing the square absorbs the affine term, yielding the Gaussian
majorant needed for normalisation and every polynomial Gibbs moment. -/
theorem strongly_convex_coercive_bound {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (U : E → ℝ) (g : E → E) (H : E → E →L[ℝ] E) (κ : ℝ) (hκ : 0 < κ)
    (hU : ∀ x, HasFDerivAt U (innerSL ℝ (g x)) x)
    (hg : ∀ x, HasFDerivAt g (H x) x)
    (hH : ∀ x v, κ*‖v‖^2 ≤ ⟪v,H x v⟫) (x : E) :
    κ/4*‖x‖^2+U 0-‖g 0‖^2/κ ≤ U x := by
  have hh := strongly_convex_quadratic_lower_bound U g H κ hU hg hH x
  have hi := neg_le_of_abs_le (abs_real_inner_le_norm (g 0) x)
  have hs := sq_nonneg (κ*‖x‖-2*‖g 0‖)
  have hdiv : κ*(‖g 0‖^2/κ)=‖g 0‖^2 := mul_div_cancel₀ _ hκ.ne'
  nlinarith

end Asakura.Chapter8
