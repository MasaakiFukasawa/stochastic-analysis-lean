import FullAuditStieltjesIntegral
import Mathlib.MeasureTheory.SetSemiring

open MeasureTheory Set
namespace Asakura.FullAudit

/-- Finite additivity on a partition, with explicit measurability of the parts. -/
theorem signed_partition_sum {Ω : Type*} [MeasurableSpace Ω]
    (ν : SignedMeasure Ω) {E : Set Ω} (P : Finpartition E)
    (hP : ∀ F ∈ P.parts, MeasurableSet F) :
    ∑ F ∈ P.parts, ν F = ν E := by
  have h := ν.of_biUnion_finset P.disjoint hP
  have hs : (⋃ F ∈ P.parts, F) = E := by
    rw [← Finset.sup_set_eq_biUnion]
    exact P.sup_parts
  simpa only [id_eq, hs] using h.symm

theorem real_partition_sum {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] {E : Set Ω} (hE : MeasurableSet E)
    (P : Finpartition E) (hP : ∀ F ∈ P.parts, MeasurableSet F) :
    ∑ F ∈ P.parts, μ.real F = μ.real E := by
  have h := signed_partition_sum μ.toSignedMeasure P hP
  rw [Measure.toSignedMeasure_apply_measurable hE] at h
  convert h using 1
  apply Finset.sum_congr rfl
  intro F hF
  exact (Measure.toSignedMeasure_apply_measurable (hP F hF)).symm

/-- The first finite Cauchy-Schwarz step in the original proof, extending a
semiring estimate to finite disjoint unions. -/
theorem signed_cs_supClosure {Ω : Type*} [m : MeasurableSpace Ω]
    (α β : Measure Ω) [IsFiniteMeasure α] [IsFiniteMeasure β] (ν : SignedMeasure Ω)
    (C : Set (Set Ω)) (hC : IsSetSemiring C)
    (hm : ∀ E ∈ C, MeasurableSet E)
    (hc : ∀ E ∈ C, |ν E| ≤ Real.sqrt (α.real E)*Real.sqrt (β.real E)) :
    ∀ E ∈ supClosure C, |ν E| ≤ Real.sqrt (α.real E)*Real.sqrt (β.real E) := by
  intro E hE
  obtain ⟨P,hP⟩ := hC.mem_supClosure_iff.mp hE
  have hp : ∀ F ∈ P.parts, MeasurableSet F := fun F hF => hm F (hP hF)
  have he : MeasurableSet E := by
    rw [← P.sup_parts, Finset.sup_set_eq_biUnion]
    exact MeasurableSet.biUnion (Finset.countable_toSet _) hp
  calc
    |ν E| = |∑ F ∈ P.parts, ν F| := by rw [signed_partition_sum ν P hp]
    _ ≤ ∑ F ∈ P.parts, |ν F| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ F ∈ P.parts, Real.sqrt (α.real F)*Real.sqrt (β.real F) :=
      Finset.sum_le_sum (fun F hF => hc F (hP hF))
    _ ≤ Real.sqrt (∑ F ∈ P.parts, α.real F)*Real.sqrt (∑ F ∈ P.parts, β.real F) :=
      Real.sum_sqrt_mul_sqrt_le P.parts (fun _ => ENNReal.toReal_nonneg)
        (fun _ => ENNReal.toReal_nonneg)
    _ = _ := by rw [real_partition_sum α he P hp,real_partition_sum β he P hp]

/-- Finite disjoint unions of a generating semiring containing the whole space
form exactly the algebra required by the written monotone-class argument. -/
theorem stieltjes_integral_from_semiring {Ω : Type*} [m : MeasurableSpace Ω]
    (α β : Measure Ω) [IsFiniteMeasure α] [IsFiniteMeasure β] (ν : SignedMeasure Ω)
    (C : Set (Set Ω)) (hC : IsSetSemiring C)
    (hgen : m = MeasurableSpace.generateFrom C) (huniv : (univ : Set Ω) ∈ C)
    (hc : ∀ E ∈ C, |ν E| ≤ Real.sqrt (α.real E)*Real.sqrt (β.real E))
    (f g : Ω → ℝ) (hf : Measurable f) (hg : Measurable g) :
    (∫⁻ x, ENNReal.ofReal |f x*g x| ∂ν.totalVariation) ≤
      (∫⁻ x, ENNReal.ofReal ((f x)^2) ∂α)^(1/2:ℝ)*
      (∫⁻ x, ENNReal.ofReal ((g x)^2) ∂β)^(1/2:ℝ) := by
  have hR := hC.isSetRing_supClosure
  have hu : (univ : Set Ω) ∈ supClosure C := subset_supClosure huniv
  have hm : ∀ E ∈ C, MeasurableSet E := by
    intro E hE
    rw [hgen]
    exact MeasurableSpace.measurableSet_generateFrom hE
  have hs : m = MeasurableSpace.generateFrom (supClosure C) := by
    rw [hgen]
    apply le_antisymm (MeasurableSpace.generateFrom_mono subset_supClosure)
    exact MeasurableSpace.generateFrom_le (fun _ hE =>
      measurableSet_generateFrom_of_mem_supClosure hE)
  apply stieltjes_integral_from_algebra α β ν (supClosure C) hs hu
    (fun E hE => ?_) (fun E hE F hF => hR.inter_mem hE hF)
    (signed_cs_supClosure α β ν C hC hm hc) f g hf hg
  simpa only [compl_eq_univ_sdiff] using hR.sdiff_mem hu hE

end Asakura.FullAudit
