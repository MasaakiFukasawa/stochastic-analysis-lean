import Chapter9PosteriorBounds
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

open MeasureTheory
open scoped RealInnerProductSpace
namespace Asakura.Chapter9
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

noncomputable def covarianceOperator {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [MeasurableSpace E] (P : Measure E) : E →L[ℝ] E :=
  ∫ x,(innerSL ℝ (x-∫ y,y ∂P)).smulRight (x-∫ y,y ∂P) ∂P

theorem covariance_operator_norm_le {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] (P : Measure E) [IsProbabilityMeasure P]
    (h2 : MemLp (fun x : E => x) 2 P) :
    ‖covarianceOperator P‖ ≤ ∫ x,‖x‖^2 ∂P := by
  have hr (z : E) : ‖(innerSL ℝ z).smulRight z‖=‖z‖^2 := by
    rw [ContinuousLinearMap.norm_smulRight_apply,innerSL_apply_norm,pow_two]
  calc
    _ ≤ ∫ x,‖(innerSL ℝ (x-∫ y,y ∂P)).smulRight (x-∫ y,y ∂P)‖ ∂P :=
      norm_integral_le_integral_norm _
    _ = ∫ x,‖x-∫ y,y ∂P‖^2 ∂P := by simp_rw [hr]
    _ ≤ _ := Asakura.Chapter8.centered_second_moment_le P h2

/-- The manuscript's R² bound is an operator-norm bound, not just a
coordinatewise variance bound. It follows by bounding the trace through
the centered second moment. -/
theorem bounded_covariance_operator {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] (P : Measure E) [IsProbabilityMeasure P]
    (R : ℝ) (hR : 0≤R) (hb : ∀ᵐ x ∂P,‖x‖≤R) :
    ‖covarianceOperator P‖ ≤ R^2 := by
  have h2 : MemLp (fun x : E => x) 2 P :=
    (memLp_const (μ := P) (p := 2) R).of_le (by fun_prop) (by
      filter_upwards [hb] with x hx
      simpa only [Real.norm_eq_abs,abs_of_nonneg hR] using hx)
  apply (covariance_operator_norm_le P h2).trans
  have hi := (memLp_two_iff_integrable_sq_norm h2.aestronglyMeasurable).mp h2
  have he := integral_mono_ae hi (integrable_const (R^2)) (by
    filter_upwards [hb] with x hx
    exact pow_le_pow_left₀ (norm_nonneg x) hx 2)
  simpa using he

theorem covariance_operator_apply {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] (P : Measure E) [IsProbabilityMeasure P]
    (h2 : MemLp (fun x : E => x) 2 P) (h : E) :
    covarianceOperator P h=∫ x,⟪x-∫ y,y ∂P,h⟫ • (x-∫ y,y ∂P) ∂P := by
  let m := ∫ y,y ∂P
  have hc : MemLp (fun x => x-m) 2 P := h2.sub (memLp_const m)
  have hi := (memLp_two_iff_integrable_sq_norm hc.aestronglyMeasurable).mp hc
  have hm : Continuous (fun x : E => (innerSL ℝ (x-m)).smulRight (x-m)) := by fun_prop
  have hiop : Integrable (fun x : E => (innerSL ℝ (x-m)).smulRight (x-m)) P := by
    apply hi.mono' hm.aestronglyMeasurable
    apply ae_of_all
    intro x
    rw [ContinuousLinearMap.norm_smulRight_apply,innerSL_apply_norm,pow_two]
  unfold covarianceOperator
  rw [ContinuousLinearMap.integral_apply hiop]
  rfl
end Asakura.Chapter9
