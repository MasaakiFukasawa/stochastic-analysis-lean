import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Tactic.FieldSimp

open MeasureTheory Filter
namespace Asakura.Chapter10
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

/-- The deterministic integrating factor scales the actual conditional mean;
dividing the Kalman estimate therefore gives the market's estimate of V. -/
theorem kyle_conditional_mean_scaling {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) (H : MeasurableSpace Ω) (V a : Ω → ℝ) (L : ℝ) (hL : L≠0)
    (ha : P[(fun w => L*V w)|H]=ᵐ[P] a) :
    P[V|H]=ᵐ[P] (fun w => a w/L) := by
  have hc := condExp_smul (μ := P) L V H
  filter_upwards [ha,hc] with w ha hc
  change P[(fun w => L*V w)|H] w=L*P[V|H] w at hc
  rw [ha] at hc
  exact (eq_div_iff hL).mpr (by simpa only [mul_comm] using hc.symm)

/-- Conditional covariance rescales by the square of the deterministic
factor; the deterministic Riccati variance thus becomes S/L². -/
theorem kyle_conditional_variance_scaling {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (H : MeasurableSpace Ω) (V a : Ω → ℝ) (L S : ℝ) (hL : L≠0)
    (hvar : P[(fun w => (L*V w-a w)^2)|H]=ᵐ[P] (fun _ => S)) :
    P[(fun w => (V w-a w/L)^2)|H]=ᵐ[P] (fun _ => S/L^2) := by
  have he : (fun w => (L*V w-a w)^2)=(fun w => L^2*(V w-a w/L)^2) := by
    funext w
    field_simp
  rw [he] at hvar
  have hc := condExp_smul (μ := P) (L^2) (fun w => (V w-a w/L)^2) H
  filter_upwards [hvar,hc] with w hv hc
  change P[(fun w => L^2*(V w-a w/L)^2)|H] w=L^2*P[(fun w => (V w-a w/L)^2)|H] w at hc
  rw [hv] at hc
  exact (eq_div_iff (pow_ne_zero 2 hL)).mpr (by simpa only [mul_comm] using hc.symm)

end Asakura.Chapter10
