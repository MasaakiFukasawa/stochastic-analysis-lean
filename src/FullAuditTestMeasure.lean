import FullAuditStrongMarkovTests
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology BoundedContinuousFunction
namespace Asakura.FullAudit

/-- The bounded continuous test equalities identify the restricted image measure. -/
theorem restricted_law_of_continuous_tests {Ω E : Type*} {m : MeasurableSpace Ω}
    [MeasurableSpace E] [TopologicalSpace E] [BorelSpace E] [HasOuterApproxClosed E]
    (P : Measure Ω) [IsProbabilityMeasure P] (μ : Measure E) [IsProbabilityMeasure μ]
    (X : Ω → E) (hX : Measurable[m] X) (A : Set Ω) (hA : MeasurableSet[m] A)
    (h : ∀ f : E →ᵇ ℝ, (∫ ω in A, f (X ω) ∂P) = ∫ _ in A, (∫ x, f x ∂μ) ∂P) :
    (P.restrict A).map X = P A • μ := by
  letI : IsFiniteMeasure (P A • μ) := ⟨by simp [Measure.smul_apply,measure_lt_top]⟩
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  rw [integral_map hX.aemeasurable f.continuous.aestronglyMeasurable,integral_smul_measure]
  rw [h f]
  simp only [integral_const,Measure.real,Measure.restrict_apply_univ,smul_eq_mul]

/-- Restricted laws also give the full law (A=univ) and independence from G. -/
theorem independent_law_of_restricted_laws {Ω E : Type*} (G : MeasurableSpace Ω) {m : MeasurableSpace Ω}
    [MeasurableSpace E] (P : Measure Ω) [IsProbabilityMeasure P]
    (μ : Measure E) (hG : G ≤ m)
    (X : Ω → E) (hX : Measurable[m] X)
    (h : ∀ A, MeasurableSet[G] A → (P.restrict A).map X = P A • μ) :
    HasLaw X μ P ∧ Indep (MeasurableSpace.comap X inferInstance) G P := by
  have hmap : P.map X = μ := by simpa using h univ MeasurableSet.univ
  refine ⟨⟨hX.aemeasurable,hmap⟩,?_⟩
  rw [Indep_iff]
  rintro S A ⟨D,hD,rfl⟩ hA
  have he := congrArg (fun ν : Measure E => ν D) (h A hA)
  rw [Measure.map_apply hX hD,Measure.restrict_apply (hX hD),Measure.smul_apply] at he
  have hDlaw : P (X ⁻¹' D) = μ D := by rw [← hmap,Measure.map_apply hX hD]
  simpa only [hDlaw,smul_eq_mul,mul_comm] using he
end Asakura.FullAudit
