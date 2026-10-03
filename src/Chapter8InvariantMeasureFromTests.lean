import Chapter8IntegratedGeneratorZero
import Chapter4SmoothMeasureDetermination
import Mathlib.MeasureTheory.Integral.Prod

open MeasureTheory Set
namespace Asakura.Chapter8
set_option maxHeartbeats 1600000

/-- Equality of propagated smooth test integrals is equality of the
actual laws, using the independent initial-state/noise product measure. -/
theorem invariant_measure_from_tests {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (π : Measure (Fin d → ℝ)) (P : Measure Ω)
    [IsProbabilityMeasure π] [IsProbabilityMeasure P]
    (X : (Fin d → ℝ) × Ω → (Fin d → ℝ)) (hX : Measurable X)
    (he : ∀ f : (Fin d → ℝ) → ℝ, ContDiff ℝ (⊤:ℕ∞) f → HasCompactSupport f →
      (∫ x, (∫ w, f (X (x,w)) ∂P) ∂π) = ∫ x, f x ∂π) :
    (π.prod P).map X = π := by
  letI : IsProbabilityMeasure ((π.prod P).map X) :=
    (Measure.isProbabilityMeasure_map_iff hX.aemeasurable).mpr inferInstance
  apply Asakura.Chapter4.measure_eq_of_smooth_compact_tests
  intro f hf hs
  obtain ⟨C,hC⟩ := hs.exists_bound_of_continuous hf.continuous
  have hi : Integrable (fun z => f (X z)) (π.prod P) :=
    (integrable_const C).mono' (hf.continuous.measurable.comp hX).aestronglyMeasurable
      (ae_of_all _ fun z => hC (X z))
  rw [integral_map hX.aemeasurable hf.continuous.aestronglyMeasurable,
    integral_prod _ hi]
  exact he f hf hs

end Asakura.Chapter8
