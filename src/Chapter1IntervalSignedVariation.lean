import Chapter1SignedSubtype

open MeasureTheory Set Filter
open Asakura.FullAudit
open scoped ENNReal Topology
namespace Asakura.Chapter1Complete
set_option maxHeartbeats 2000000

noncomputable def intervalSigned (a b : ℝ) (hab : a≤b) (C : ℝ → ℝ)
    (hC : BoundedVariationOn C (Icc a b))
    (hr : ∀ x∈Icc a b,ContinuousWithinAt C (Icc a b∩Ici x) x) : SignedMeasure ℝ :=
  bvSigned (C ∘ intervalClamp a b hab) (intervalClamp_boundedVariation a b hab C hC)
    (intervalClamp_right_continuous a b hab C hr) a

lemma interval_signed_increment (a b : ℝ) (hab : a≤b) (C : ℝ → ℝ)
    (hC : BoundedVariationOn C (Icc a b))
    (hr : ∀ x∈Icc a b,ContinuousWithinAt C (Icc a b∩Ici x) x)
    {s t : ℝ} (hs : a≤s) (hst : s≤t) (ht : t≤b) :
    intervalSigned a b hab C hC hr (Ioc s t)=C t-C s := by
  rw [intervalSigned,bvSigned_Ioc _ _ _ _ _ _ hst]
  simp only [Function.comp_def,intervalClamp_eq a b hab ⟨hs,hst.trans ht⟩,
    intervalClamp_eq a b hab ⟨hs.trans hst,ht⟩]

lemma interval_signed_variation (a b : ℝ) (hab : a≤b) (C : ℝ → ℝ)
    (hC : BoundedVariationOn C (Icc a b))
    (hr : ∀ x∈Icc a b,ContinuousWithinAt C (Icc a b∩Ici x) x)
    {t : ℝ} (ht : t∈Icc a b) :
    (intervalSigned a b hab C hC hr).totalVariation.real (Ioc a t)=
      (eVariationOn C (Icc a t)).toReal := by
  let D := C ∘ intervalClamp a b hab
  have hD := intervalClamp_boundedVariation a b hab C hC
  have hrD := intervalClamp_right_continuous a b hab C hr
  rw [intervalSigned,bvSigned_totalVariation,measureReal_def,StieltjesFunction.measure_Ioc]
  change (ENNReal.ofReal (variationOnFromTo D univ a t-variationOnFromTo D univ a a)).toReal=_
  rw [variationOnFromTo.self,sub_zero,variationOnFromTo.eq_of_le D univ ht.1,univ_inter,
    ENNReal.toReal_ofReal ENNReal.toReal_nonneg]
  congr 1
  apply eVariationOn.congr
  intro x hx
  exact congrArg C (intervalClamp_eq a b hab ⟨hx.1,hx.2.trans ht.2⟩)

lemma subtype_interval_signed_increment (a b : ℝ) (hab : a≤b) (C : ℝ → ℝ)
    (hC : BoundedVariationOn C (Icc a b))
    (hr : ∀ x∈Icc a b,ContinuousWithinAt C (Icc a b∩Ici x) x)
    {t s r : ℝ} (ht : t≤b) (hs : a≤s) (hsr : s≤r) (hr' : r≤t) :
    signedSubtype (intervalSigned a b hab C hC hr) (Ioc a t) measurableSet_Ioc
      (Subtype.val ⁻¹' Ioc s r)=C r-C s := by
  rw [signed_subtype_apply _ _ _ _ (measurableSet_Ioc.preimage measurable_subtype_coe)]
  have he : Subtype.val '' (Subtype.val ⁻¹' Ioc s r : Set (Ioc a t))=Ioc s r := by
    rw [Subtype.image_preimage_coe]
    exact inter_eq_right.mpr (fun x hx => ⟨lt_of_le_of_lt hs hx.1,hx.2.trans hr'⟩)
  rw [he]
  exact interval_signed_increment a b hab C hC hr hs hsr (hr'.trans ht)

lemma subtype_interval_signed_total (a b : ℝ) (hab : a≤b) (C : ℝ → ℝ)
    (hC : BoundedVariationOn C (Icc a b))
    (hr : ∀ x∈Icc a b,ContinuousWithinAt C (Icc a b∩Ici x) x)
    {t : ℝ} (ht : t∈Icc a b) :
    (signedSubtype (intervalSigned a b hab C hC hr) (Ioc a t) measurableSet_Ioc).totalVariation.real univ=
      (eVariationOn C (Icc a t)).toReal := by
  rw [signed_subtype_variation,measureReal_def,comap_subtype_coe_apply measurableSet_Ioc,
    image_univ,Subtype.range_coe]
  exact interval_signed_variation a b hab C hC hr ht

end Asakura.Chapter1Complete
