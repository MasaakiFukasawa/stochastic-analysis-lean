import FullAuditTestMeasure
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.Probability.Kernel.Composition.IntegralCompProd

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace Asakura.Chapter4

/-- The pi-lambda step in the manuscript, applied to the restricted law
and the mixture of transition probabilities. Only open-set tests are
assumed; all Borel sets are obtained in the conclusion. Measurability of
the transition family is explicitly represented by `Kernel`. -/
theorem markov_restricted_law_of_open_tests
    {Ω E : Type*} [MeasurableSpace Ω] [TopologicalSpace E]
    [MeasurableSpace E] [BorelSpace E]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → E) (hX : Measurable X)
    (κ : Kernel Ω E) [IsMarkovKernel κ]
    (A : Set Ω) (hA : MeasurableSet A)
    (ho : ∀ O : Set E, IsOpen O →
      P (X ⁻¹' O ∩ A) = ∫⁻ ω in A, κ ω O ∂P) :
    (P.restrict A).map X = κ ∘ₘ (P.restrict A) := by
  apply ext_of_generate_finite {O : Set E | IsOpen O}
    BorelSpace.measurable_eq isPiSystem_isOpen
  · intro O hO
    rw [Measure.map_apply hX hO.measurableSet,
      Measure.restrict_apply (hX hO.measurableSet),
      Measure.bind_apply hO.measurableSet κ.aemeasurable]
    exact ho O hO
  · rw [Measure.map_apply hX MeasurableSet.univ,
      Measure.bind_apply MeasurableSet.univ κ.aemeasurable]
    simp

/-- Once the restricted laws agree, integration gives every bounded
Borel test, not just the indicators used in the pi-lambda argument. -/
theorem markov_bounded_test_of_restricted_law
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → E) (hX : Measurable X)
    (κ : Kernel Ω E) [IsMarkovKernel κ]
    (A : Set Ω)
    (hlaw : (P.restrict A).map X = κ ∘ₘ (P.restrict A))
    (f : E → ℝ) (hf : Measurable f)
    (C : ℝ) (hb : ∀ x, ‖f x‖ ≤ C) :
    (∫ ω in A, f (X ω) ∂P) = ∫ ω in A, (∫ x, f x ∂κ ω) ∂P := by
  have hi : Integrable f (κ ∘ₘ (P.restrict A)) :=
    (integrable_const C).mono' hf.aestronglyMeasurable (ae_of_all _ hb)
  rw [← integral_map hX.aemeasurable hf.aestronglyMeasurable,hlaw]
  exact Kernel.integral_comp (κ := Kernel.const Unit (P.restrict A)) (η := κ) (a := ()) hi

end Asakura.Chapter4
