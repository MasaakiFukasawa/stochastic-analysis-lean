import FullAuditStieltjesExtension
import Mathlib.MeasureTheory.VectorMeasure.Variation.SignedMeasure

open MeasureTheory Set
open scoped ENNReal
namespace Asakura.FullAudit

/-- Additivity on a finite measurable partition in real rather than extended-real values. -/
theorem real_measure_finpartition {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] {E : Set Ω} (hE : MeasurableSet E)
    (P : Finpartition (⟨E,hE⟩ : Subtype MeasurableSet)) :
    ∑ F ∈ P.parts, μ.real (F : Set Ω) = μ.real E := by
  have h := VectorMeasure.sum_finpartition μ.toSignedMeasure P
  simpa only [Measure.toSignedMeasure_apply_measurable hE,
    Measure.toSignedMeasure_apply_measurable (Subtype.property _)] using h

/-- The manuscript's second finite Cauchy-Schwarz application, now to arbitrary
measurable partitions of E. -/
theorem signed_cs_partition {Ω : Type*} [MeasurableSpace Ω]
    (α β : Measure Ω) [IsFiniteMeasure α] [IsFiniteMeasure β] (ν : SignedMeasure Ω)
    (hbound : ∀ E, MeasurableSet E → |ν E| ≤ Real.sqrt (α.real E)*Real.sqrt (β.real E))
    {E : Set Ω} (hE : MeasurableSet E)
    (P : Finpartition (⟨E,hE⟩ : Subtype MeasurableSet)) :
    ∑ F ∈ P.parts, |ν (F : Set Ω)| ≤ Real.sqrt (α.real E)*Real.sqrt (β.real E) := by
  calc
    _ ≤ ∑ F ∈ P.parts, Real.sqrt (α.real (F : Set Ω))*Real.sqrt (β.real (F : Set Ω)) :=
      Finset.sum_le_sum (fun F _ => hbound F F.property)
    _ ≤ Real.sqrt (∑ F ∈ P.parts, α.real (F : Set Ω))*
        Real.sqrt (∑ F ∈ P.parts, β.real (F : Set Ω)) :=
      Real.sum_sqrt_mul_sqrt_le P.parts (fun _ => ENNReal.toReal_nonneg)
        (fun _ => ENNReal.toReal_nonneg)
    _ = _ := by rw [real_measure_finpartition α hE P,real_measure_finpartition β hE P]

/-- Taking the supremum over finite measurable partitions gives exactly the
variation bound in the manuscript, not a bound on the absolute signed mass alone. -/
theorem signed_cs_totalVariation {Ω : Type*} [MeasurableSpace Ω]
    (α β : Measure Ω) [IsFiniteMeasure α] [IsFiniteMeasure β] (ν : SignedMeasure Ω)
    (hbound : ∀ E, MeasurableSet E → |ν E| ≤ Real.sqrt (α.real E)*Real.sqrt (β.real E))
    {E : Set Ω} (hE : MeasurableSet E) :
    ν.totalVariation E ≤ ENNReal.ofReal (Real.sqrt (α.real E)*Real.sqrt (β.real E)) := by
  classical
  rw [ν.totalVariation_eq_variation]
  simp only [VectorMeasure.variation_apply, preVariation, VectorMeasure.ennrealToMeasure_apply hE,
    ennrealPreVariation_apply, preVariationFun, hE, dite_true, iSup_le_iff]
  intro P
  have h := signed_cs_partition α β ν hbound hE P
  have he : (∑ F ∈ P.parts, ‖ν (F : Set Ω)‖ₑ) =
      ENNReal.ofReal (∑ F ∈ P.parts, |ν (F : Set Ω)|) := by
    simp only [← ofReal_norm, Real.norm_eq_abs]
    exact (ENNReal.ofReal_sum_of_nonneg (fun _ _ => abs_nonneg _)).symm
  rw [he]
  exact ENNReal.ofReal_le_ofReal h

end Asakura.FullAudit
