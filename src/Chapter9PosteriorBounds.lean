import Chapter8CenteredMoment

open MeasureTheory
open scoped RealInnerProductSpace
namespace Asakura.Chapter9
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

/-- Every posterior supported in the same radius-R ball has mean bounded
by R and covariance quadratic form bounded by R^2 times the squared norm.
The factor is R^2, not the coarser 4R^2 bound for the centered support. -/
theorem bounded_posterior_moments {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] (P : Measure E) [IsProbabilityMeasure P]
    (R : ℝ) (hR : 0≤R) (hb : ∀ᵐ x ∂P,‖x‖≤R) :
    ‖∫ x,x ∂P‖≤R ∧ ∀ h : E,
      (∫ x,⟪h,x-(∫ y,y ∂P)⟫^2 ∂P)≤R^2*‖h‖^2 := by
  have h2 : MemLp (fun x : E => x) 2 P :=
    (memLp_const (μ := P) (p := 2) R).of_le (by fun_prop) (by
      filter_upwards [hb] with x hx
      simpa only [Real.norm_eq_abs,abs_of_nonneg hR] using hx)
  have hi := (memLp_two_iff_integrable_sq_norm h2.aestronglyMeasurable).mp h2
  have hmoment : (∫ x,‖x‖^2 ∂P)≤R^2 := by
    have hh := integral_mono_ae hi (integrable_const (R^2)) (by
      filter_upwards [hb] with x hx
      exact pow_le_pow_left₀ (norm_nonneg x) hx 2)
    simpa using hh
  refine ⟨?_,?_⟩
  · simpa using norm_integral_le_of_norm_le_const hb
  · intro h
    let m := ∫ y,y ∂P
    have hc : MemLp (fun x => x-m) 2 P := h2.sub (memLp_const m)
    have hci := (memLp_two_iff_integrable_sq_norm hc.aestronglyMeasurable).mp hc
    have hp := (innerSL ℝ h).comp_memLp' hc
    have hpi : Integrable (fun x => ⟪h,x-m⟫^2) P := by
      simpa only [Function.comp_def,innerSL_apply_apply,Real.norm_eq_abs,sq_abs] using
        (memLp_two_iff_integrable_sq_norm hp.aestronglyMeasurable).mp hp
    have hle : (∫ x,⟪h,x-m⟫^2 ∂P)≤‖h‖^2*(∫ x,‖x-m‖^2 ∂P) := by
      rw [←integral_const_mul]
      apply integral_mono_ae hpi (hci.const_mul _)
      apply ae_of_all
      intro x
      have hh := pow_le_pow_left₀ (abs_nonneg ⟪h,x-m⟫) (abs_real_inner_le_norm h (x-m)) 2
      simpa only [sq_abs,mul_pow] using hh
    exact hle.trans (by
      have hh := mul_le_mul_of_nonneg_left
        ((Asakura.Chapter8.centered_second_moment_le P h2).trans hmoment) (sq_nonneg ‖h‖)
      simpa only [mul_comm] using hh)
end Asakura.Chapter9
