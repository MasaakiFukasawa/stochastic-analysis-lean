import FullAuditMonotoneClass
import Mathlib.MeasureTheory.VectorMeasure.Operations
import Mathlib.Analysis.SpecialFunctions.Sqrt

open MeasureTheory Set Filter
open scoped Topology
namespace Asakura.FullAudit

/-- Finite positive measures have real-valued continuity on increasing sequences. -/
theorem finite_real_iUnion {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (E : ℕ → Set Ω)
    (hE : ∀ n, MeasurableSet (E n)) (hm : Monotone E) :
    Tendsto (fun n => μ.real (E n)) atTop (𝓝 (μ.real (⋃ n, E n))) := by
  have h := VectorMeasure.tendsto_vectorMeasure_iUnion_atTop_nat
    (v := μ.toSignedMeasure) hm hE
  simpa only [Measure.toSignedMeasure_apply_measurable (MeasurableSet.iUnion hE),
    Measure.toSignedMeasure_apply_measurable (hE _)] using h

theorem finite_real_iInter {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (E : ℕ → Set Ω)
    (hE : ∀ n, MeasurableSet (E n)) (hm : Antitone E) :
    Tendsto (fun n => μ.real (E n)) atTop (𝓝 (μ.real (⋂ n, E n))) := by
  have h := VectorMeasure.tendsto_vectorMeasure_iInter_atTop_nat
    (v := μ.toSignedMeasure) hm hE
  simpa only [Measure.toSignedMeasure_apply_measurable (MeasurableSet.iInter hE),
    Measure.toSignedMeasure_apply_measurable (hE _)] using h

/-- The precise monotone class used in the manuscript: an inequality for nu(E),
not yet total variation. Signed measure continuity handles both monotone directions. -/
theorem signed_cs_monotone_class {Ω : Type*} [MeasurableSpace Ω]
    (α β : Measure Ω) [IsFiniteMeasure α] [IsFiniteMeasure β] (ν : SignedMeasure Ω) :
    WrittenMonotone {E | MeasurableSet E ∧ |ν E| ≤ Real.sqrt (α.real E)*Real.sqrt (β.real E)} := by
  constructor
  · intro E hE hm
    have ha := (Real.continuous_sqrt.tendsto _).comp (finite_real_iUnion α E (fun n => (hE n).1) hm)
    have hb := (Real.continuous_sqrt.tendsto _).comp (finite_real_iUnion β E (fun n => (hE n).1) hm)
    have hn := (VectorMeasure.tendsto_vectorMeasure_iUnion_atTop_nat
      (v := ν) hm (fun n => (hE n).1)).abs
    exact ⟨MeasurableSet.iUnion (fun n => (hE n).1),
      le_of_tendsto_of_tendsto' hn (ha.mul hb) (fun n => (hE n).2)⟩
  · intro E hE hm
    have ha := (Real.continuous_sqrt.tendsto _).comp (finite_real_iInter α E (fun n => (hE n).1) hm)
    have hb := (Real.continuous_sqrt.tendsto _).comp (finite_real_iInter β E (fun n => (hE n).1) hm)
    have hn := (VectorMeasure.tendsto_vectorMeasure_iInter_atTop_nat
      (v := ν) hm (fun n => (hE n).1)).abs
    exact ⟨MeasurableSet.iInter (fun n => (hE n).1),
      le_of_tendsto_of_tendsto' hn (ha.mul hb) (fun n => (hE n).2)⟩

/-- Extension from a generating algebra, using the newly proved written monotone-class theorem. -/
theorem signed_cs_from_algebra {Ω : Type*} [m : MeasurableSpace Ω]
    (α β : Measure Ω) [IsFiniteMeasure α] [IsFiniteMeasure β] (ν : SignedMeasure Ω)
    (A : Set (Set Ω)) (hgen : m = MeasurableSpace.generateFrom A)
    (huniv : (univ : Set Ω) ∈ A) (hcompl : ∀ E ∈ A, Eᶜ ∈ A)
    (hinter : ∀ E ∈ A, ∀ F ∈ A, E ∩ F ∈ A)
    (hbound : ∀ E ∈ A, |ν E| ≤ Real.sqrt (α.real E)*Real.sqrt (β.real E)) :
    ∀ E, MeasurableSet E → |ν E| ≤ Real.sqrt (α.real E)*Real.sqrt (β.real E) := by
  have h := monotone_class_written A _ huniv hcompl hinter
    (signed_cs_monotone_class α β ν) (by
      intro E hE
      refine ⟨?_, hbound E hE⟩
      rw [hgen]
      exact MeasurableSpace.measurableSet_generateFrom hE)
  intro E hE
  exact (h E (by rwa [← hgen])).2

end Asakura.FullAudit
