import Chapter6PositiveRealDensity

open MeasureTheory Set Filter
namespace Asakura.Chapter6

/-- Equivalent laws rule out a statistic that identifies both distinct
parameters almost surely from the one observed path. -/
theorem equivalent_laws_no_exact_identification {Ω Θ : Type*} [MeasurableSpace Ω]
    (P Q : Measure Ω) [IsProbabilityMeasure P] (T : Ω → Θ)
    (θ η : Θ) (hne : θ≠η)
    (hAE : ∀ p : Ω → Prop,(∀ᵐ w ∂P,p w) ↔ ∀ᵐ w ∂Q,p w)
    (hP : ∀ᵐ w ∂P,T w=θ) : ¬(∀ᵐ w ∂Q,T w=η) := by
  intro hQ
  obtain ⟨w,hθ,hη⟩ := (hP.and ((hAE _).mpr hQ)).exists
  exact hne (hθ.symm.trans hη)

end Asakura.Chapter6
