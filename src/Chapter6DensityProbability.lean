import Chapter6ExponentialClosed

open MeasureTheory Set Filter
open scoped ENNReal
namespace Asakura.Chapter6

/-- The measure defined by a nonnegative mean-one density is a probability
measure; this discharges the probability instance in the measure-change theorem. -/
theorem mean_one_density_probability {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (D : Ω → ℝ) (hi : Integrable D P)
    (hp : ∀ᵐ w ∂P,0 ≤ D w) (hm : (∫ w,D w ∂P) = 1) :
    IsProbabilityMeasure (P.withDensity (fun w => ENNReal.ofReal (D w))) := by
  constructor
  rw [withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal hi hp,hm]
  simp

end Asakura.Chapter6
