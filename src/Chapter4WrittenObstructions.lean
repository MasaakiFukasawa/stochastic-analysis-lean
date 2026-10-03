import FullAuditChapter4Gronwall
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.MeasurableSpace.CountablyGenerated

open MeasureTheory Set
namespace Asakura.Chapter4
set_option backward.isDefEq.respectTransparency false

/-- Integrating a varying coefficient against a variation process is not
multiplication by the coefficient at the endpoint. -/
theorem variation_integral_not_endpoint_product :
    (∫ s : ℝ in 0..1, 2*s) ≠ 2*(1:ℝ)*1 := by
  rw [intervalIntegral.integral_const_mul, integral_id]
  norm_num

/-- Both possible paths solve the continuous (non-Lipschitz) ODE on t≥0.
Thus pathwise existence does not specify an adapted selection. -/
def selectedODE (b : Bool) (t : ℝ) : ℝ := if b then t^2 else 0

theorem selected_ode_initial (b : Bool) : selectedODE b 0 = 0 := by cases b <;> simp [selectedODE]

theorem selected_ode_solves (b : Bool) (t : ℝ) (ht : 0 ≤ t) :
    HasDerivAt (selectedODE b) (2*Real.sqrt |selectedODE b t|) t := by
  cases b
  · change HasDerivAt (fun _ : ℝ => 0) _ t
    simpa [selectedODE] using hasDerivAt_const t (0:ℝ)
  · change HasDerivAt (fun s : ℝ => s^2) _ t
    have h := (hasDerivAt_id t).pow 2
    convert h using 1
    · ext z; rfl
    · simp [selectedODE, abs_of_nonneg (sq_nonneg t), Real.sqrt_sq ht]

theorem selected_ode_not_measurable_at_trivial_information :
    ¬ Measurable[⊥] (fun b : Bool => selectedODE b 1) := by
  intro h
  obtain ⟨c,hc⟩ := eq_const_of_measurable_bot h
  have h0 := congrFun hc false
  have h1 := congrFun hc true
  simp [selectedODE] at h0 h1
  linarith

/-- The f=σ sqrt(1+u²) specialization mentioned in the text is the a=1
case of the hyperbolic example, not its arbitrary-a form. -/
theorem hyperbolic_specialization_needs_unit_scale :
    (Real.sqrt ((2:ℝ)^2+0^2)) ≠ Real.sqrt (1+0^2) := by norm_num

end Asakura.Chapter4
