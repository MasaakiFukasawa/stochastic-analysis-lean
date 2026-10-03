import Chapter5HeatFDeriv
import Chapter5LinearImageAverage

open MeasureTheory ProbabilityTheory
open scoped NNReal
namespace Asakura.Chapter5
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false

/-- The stronger regularity class used for the verified smooth
approximants. Neither the payoff itself nor its support is required bounded. -/
structure SmoothCylinderData (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] where
  value : E → ℝ
  first : E → E →L[ℝ] ℝ
  second : E → E →L[ℝ] E →L[ℝ] ℝ
  firstBound : ℝ≥0
  secondBound : ℝ≥0
  derivative : ∀ x,HasFDerivAt value (first x) x
  secondDerivative : ∀ x,HasFDerivAt first (second x) x
  firstContinuous : Continuous first
  secondContinuous : Continuous second
  first_le : ∀ x,‖first x‖≤firstBound
  second_le : ∀ x,‖second x‖≤secondBound

/-- The recursion constructs new derivative maps by actual integration;
it does not merely assume that averaging preserves the regularity class. -/
noncomputable def SmoothCylinderData.average
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (u : SmoothCylinderData E) (ν : Measure E) [IsProbabilityMeasure ν]
    (hi : Integrable (fun z : E => z) ν) (t : ℝ) : SmoothCylinderData E := by
  have h0 := averaged_bounded_fderiv ν hi u.value u.first u.derivative
    u.firstContinuous u.firstBound u.first_le
  have h1 := averaged_bounded_fderiv ν hi u.first u.second u.secondDerivative
    u.secondContinuous u.secondBound u.second_le
  exact {
    value := fun x => ∫ z,u.value (x+Real.sqrt t • z) ∂ν
    first := fun x => ∫ z,u.first (x+Real.sqrt t • z) ∂ν
    second := fun x => ∫ z,u.second (x+Real.sqrt t • z) ∂ν
    firstBound := u.firstBound
    secondBound := u.secondBound
    derivative := fun x => h0.1 x t
    secondDerivative := fun x => h1.1 x t
    firstContinuous := h0.2.1.comp (continuous_id.prodMk continuous_const)
    secondContinuous := h1.2.1.comp (continuous_id.prodMk continuous_const)
    first_le := fun x => h0.2.2.1 x t
    second_le := fun x => h1.2.2.1 x t }

theorem SmoothCylinderData.average_value
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (u : SmoothCylinderData E) (ν : Measure E) [IsProbabilityMeasure ν]
    (hi : Integrable (fun z : E => z) ν) (t : ℝ) (x : E) :
    (u.average ν hi t).value x=∫ z,u.value (x+Real.sqrt t • z) ∂ν := rfl

/-- Finite-dimensional Gaussian steps automatically supply the required
first moment, including when their covariance is degenerate. -/
noncomputable def SmoothCylinderData.gaussianAverage
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (u : SmoothCylinderData E) (n : ℕ) (Q : (Fin (n+1) → ℝ) →L[ℝ] E) (t : ℝ) : SmoothCylinderData E :=
  u.average ((Measure.pi (fun _ : Fin (n+1) => gaussianReal 0 1)).map Q)
    ((linear_image_second_moment _ Q (Asakura.FullAudit.finite_gaussian_all_moments 2 (by norm_num))).integrable (by norm_num)) t

end Asakura.Chapter5
