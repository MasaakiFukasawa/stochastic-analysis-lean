import Chapter8NewtonEnergy
import Mathlib.Analysis.SpecialFunctions.Exponential

open MeasureTheory Set
open scoped RealInnerProductSpace
namespace Asakura.Chapter8
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false

/-- The matrix-exponential estimate used in the small-mass proof follows
from the quadratic lower bound for the resistance operator. -/
theorem damped_semigroup_norm_bound {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E]
    (Γ : E →L[ℝ] E) (α m : ℝ) (hm : 0 < m)
    (hΓ : ∀ x, α*‖x‖^2 ≤ ⟪x,Γ x⟫) (T : ℝ) (hT : 0 ≤ T) :
    ‖NormedSpace.exp (T • (-m⁻¹ • Γ))‖ ≤ Real.exp (-α*T/m) := by
  let A := -m⁻¹ • Γ
  have hd (x : E) (t : ℝ) : HasDerivAt (fun s : ℝ => NormedSpace.exp (s • A) x)
      (A (NormedSpace.exp (t • A) x)) t := by
    have hh := (hasDerivAt_exp_smul_const' A t).clm_apply (hasDerivAt_const t x)
    simpa only [map_zero,add_zero,ContinuousLinearMap.mul_apply] using hh
  have hb (x : E) : ‖NormedSpace.exp (T • A) x‖ ≤ Real.exp (-α*T/m)*‖x‖ := by
    let X := fun t : ℝ => NormedSpace.exp (t • A) x
    have hc : Continuous X := continuous_iff_continuousAt.mpr (fun t => (hd x t).continuousAt)
    have he := dissipative_energy_bound (fun t => ‖X t‖^2) (α/m) T hT
      (hc.norm.pow 2).continuousOn
      (fun t _ => by
        have hh := (hd x t).norm_sq
        refine ⟨2*⟪X t,A (X t)⟫,?_,?_⟩
        · exact hh
        · dsimp only [A]
          rw [ContinuousLinearMap.smul_apply,inner_smul_right]
          have h := mul_le_mul_of_nonneg_left (hΓ (X t)) (inv_nonneg.mpr hm.le)
          simp only [div_eq_mul_inv]
          nlinarith)
      T ⟨hT,le_rfl⟩
    have h0 : X 0=x := by simp [X]
    rw [h0] at he
    have hexp : Real.exp (-2*(α/m)*T) = (Real.exp (-α*T/m))^2 := by
      rw [pow_two,← Real.exp_add]
      congr 1
      ring
    rw [hexp,← mul_pow] at he
    exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp he
  apply ContinuousLinearMap.opNorm_le_bound _ (Real.exp_pos _).le
  exact hb

/-- Integrating the exponential kernel gives the factor used after
integrating the velocity equation. This is an operator identity applied
to arbitrary x, rather than a scalar-only computation. -/
theorem damped_semigroup_integral {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E]
    (Γ : E ≃L[ℝ] E) (m : ℝ) (hm : m ≠ 0) (t : ℝ) (x : E) :
    (∫ s in (0:ℝ)..t, NormedSpace.exp (s • (-m⁻¹ • Γ.toContinuousLinearMap)) x) =
      m • Γ.symm (x-NormedSpace.exp (t • (-m⁻¹ • Γ.toContinuousLinearMap)) x) := by
  let A := -m⁻¹ • Γ.toContinuousLinearMap
  let X := fun s : ℝ => NormedSpace.exp (s • A) x
  have hd (s : ℝ) : HasDerivAt X (A (X s)) s := by
    have hh := (hasDerivAt_exp_smul_const' A s).clm_apply (hasDerivAt_const s x)
    simpa only [map_zero,add_zero,ContinuousLinearMap.mul_apply] using hh
  have hc : Continuous X := continuous_iff_continuousAt.mpr (fun s => (hd s).continuousAt)
  have hp (s : ℝ) : HasDerivAt (fun r => m • Γ.symm (x-X r)) (X s) s := by
    have hh := (Γ.symm.hasFDerivAt.comp_hasDerivAt s
      ((hasDerivAt_const s x).sub (hd s))).const_smul m
    convert hh using 1
    · rfl
    · change X s = m • Γ.symm (0-(-m⁻¹) • Γ (X s))
      simp only [zero_sub,neg_smul,neg_neg,map_smul,Γ.symm_apply_apply,
        smul_smul,mul_inv_cancel₀ hm,one_smul]
  have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hp s)
    (hc.intervalIntegrable 0 t)
  have h0 : X 0=x := by simp [X]
  rw [h0,sub_self,map_zero,smul_zero,sub_zero] at hh
  exact hh

end Asakura.Chapter8
