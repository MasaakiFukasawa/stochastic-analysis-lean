import FullAuditBVClamp

open MeasureTheory Set
open scoped ENNReal
namespace Asakura.Chapter1Complete

noncomputable def jordanSubtype {Ω : Type*} [MeasurableSpace Ω]
    (j : JordanDecomposition Ω) (S : Set Ω) (hS : MeasurableSet S) : JordanDecomposition S where
  posPart := j.posPart.comap Subtype.val
  negPart := j.negPart.comap Subtype.val
  mutuallySingular := by
    obtain ⟨A,hA,hp,hn⟩ := j.mutuallySingular
    refine ⟨Subtype.val ⁻¹' A,hA.preimage measurable_subtype_coe,?_,?_⟩
    · rw [comap_subtype_coe_apply hS]
      exact measure_mono_null (image_preimage_subset _ _) hp
    · rw [comap_subtype_coe_apply hS]
      exact measure_mono_null (by rintro x ⟨y,hy,rfl⟩; exact hy) hn

noncomputable def signedSubtype {Ω : Type*} [MeasurableSpace Ω]
    (ν : SignedMeasure Ω) (S : Set Ω) (hS : MeasurableSet S) : SignedMeasure S :=
  (jordanSubtype ν.toJordanDecomposition S hS).toSignedMeasure

theorem signed_subtype_apply {Ω : Type*} [MeasurableSpace Ω]
    (ν : SignedMeasure Ω) (S : Set Ω) (hS : MeasurableSet S)
    (E : Set S) (hE : MeasurableSet E) :
    signedSubtype ν S hS E=ν (Subtype.val '' E) := by
  rw [SignedMeasure.apply_eq_posPart_real_sub_negPart_real _ hE,
    SignedMeasure.apply_eq_posPart_real_sub_negPart_real _
      ((MeasurableEmbedding.subtype_coe hS).measurableSet_image.mpr hE)]
  simp only [signedSubtype,JordanDecomposition.toJordanDecomposition_toSignedMeasure,
    jordanSubtype,measureReal_def,comap_subtype_coe_apply hS]

theorem signed_subtype_variation {Ω : Type*} [MeasurableSpace Ω]
    (ν : SignedMeasure Ω) (S : Set Ω) (hS : MeasurableSet S) :
    (signedSubtype ν S hS).totalVariation=ν.totalVariation.comap Subtype.val := by
  simp only [SignedMeasure.totalVariation,signedSubtype,
    JordanDecomposition.toJordanDecomposition_toSignedMeasure,jordanSubtype]
  exact ((MeasurableEmbedding.subtype_coe hS).comap_add _ _).symm

end Asakura.Chapter1Complete
