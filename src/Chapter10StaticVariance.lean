import Chapter10VarianceTransform
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.Positivity

open MeasureTheory Set
namespace Asakura.Chapter10
set_option maxHeartbeats 1600000

/-- The written reciprocal-information formula is positive, has the given
initial value, and solves the static-state Riccati equation. -/
theorem static_variance_formula (c : ℝ → ℝ) (hc : Continuous c)
    (S0 σ : ℝ) (hS0 : 0<S0) (hσ : 0<σ) :
    let S := fun t => (S0⁻¹+∫ s in 0..t,(c s)^2/σ^2)⁻¹
    S 0=S0 ∧ ∀ t,0≤t → 0<S t ∧
      HasDerivAt S (-((c t)^2*(S t)^2)/σ^2) t := by
  dsimp only
  constructor
  · simp
  · intro t ht
    have hf : Continuous (fun s => (c s)^2/σ^2) := (hc.pow 2).div_const _
    have hnonneg : 0≤∫ s in 0..t,(c s)^2/σ^2 :=
      intervalIntegral.integral_nonneg ht (fun s _ => div_nonneg (sq_nonneg _) (sq_nonneg _))
    have hpos : 0<S0⁻¹+∫ s in 0..t,(c s)^2/σ^2 := add_pos_of_pos_of_nonneg (inv_pos.mpr hS0) hnonneg
    refine ⟨inv_pos.mpr hpos,?_⟩
    apply inverse_information_derivative _ t (c t) σ _ hpos.ne'
    exact (intervalIntegral.integral_hasDerivAt_right (hf.intervalIntegrable 0 t)
      (hf.stronglyMeasurableAtFilter _ _) hf.continuousAt).const_add _

end Asakura.Chapter10
