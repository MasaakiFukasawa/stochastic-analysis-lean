import FullAuditBVVariation

open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace Asakura.FullAudit

noncomputable def bvSigned (C : ℝ → ℝ) (hC : BoundedVariationOn C univ)
    (hr : ∀ x, ContinuousWithinAt C (Ici x) x) (a : ℝ) : SignedMeasure ℝ := by
  letI := (bv_parts_finite C hC hr a).1
  letI := (bv_parts_finite C hC hr a).2
  exact (bvPositive C hC hr a).measure.toSignedMeasure-(bvNegative C hC hr a).measure.toSignedMeasure

/-- The constructed signed Stieltjes measure has exactly the requested increments. -/
theorem bvSigned_Ioc (C : ℝ → ℝ) (hC : BoundedVariationOn C univ)
    (hr : ∀ x, ContinuousWithinAt C (Ici x) x) (a s t : ℝ) (hst : s ≤ t) :
    bvSigned C hC hr a (Ioc s t) = C t-C s := by
  letI := (bv_parts_finite C hC hr a).1
  letI := (bv_parts_finite C hC hr a).2
  have hp := (bvPositive C hC hr a).mono hst
  have hn := (bvNegative C hC hr a).mono hst
  change ((bvPositive C hC hr a).measure.toSignedMeasure-(bvNegative C hC hr a).measure.toSignedMeasure) (Ioc s t) = _
  rw [VectorMeasure.sub_apply,Measure.toSignedMeasure_apply_measurable measurableSet_Ioc,
    Measure.toSignedMeasure_apply_measurable measurableSet_Ioc]
  simp only [measureReal_def,StieltjesFunction.measure_Ioc,
    ENNReal.toReal_ofReal (sub_nonneg.mpr hp),ENNReal.toReal_ofReal (sub_nonneg.mpr hn)]
  change ((variationOnFromTo C univ a t+(C t-C a))/2-(variationOnFromTo C univ a s+(C s-C a))/2)-
    ((variationOnFromTo C univ a t-(C t-C a))/2-(variationOnFromTo C univ a s-(C s-C a))/2) = _
  ring

/-- First half of the identification in the manuscript: |dC| is bounded by dV. -/
theorem bvSigned_variation_le (C : ℝ → ℝ) (hC : BoundedVariationOn C univ)
    (hr : ∀ x, ContinuousWithinAt C (Ici x) x) (a : ℝ) :
    (bvSigned C hC hr a).totalVariation ≤ (bvVariation C hC hr a).measure := by
  letI := (bv_parts_finite C hC hr a).1
  letI := (bv_parts_finite C hC hr a).2
  have he : bvPositive C hC hr a+bvNegative C hC hr a = bvVariation C hC hr a := by
    ext x
    change (variationOnFromTo C univ a x+(C x-C a))/2+(variationOnFromTo C univ a x-(C x-C a))/2 = variationOnFromTo C univ a x
    ring
  rw [← he,StieltjesFunction.measure_add,SignedMeasure.totalVariation_eq_variation]
  simpa only [bvSigned,Measure.variation_toSignedMeasure] using
    (VectorMeasure.variation_sub_le (μ := (bvPositive C hC hr a).measure.toSignedMeasure) (ν := (bvNegative C hC hr a).measure.toSignedMeasure))

/-- The reverse bound on intervals comes from the supremum over all finite
interval partitions, after which uniqueness identifies the measures. -/
theorem bvSigned_totalVariation (C : ℝ → ℝ) (hC : BoundedVariationOn C univ)
    (hr : ∀ x, ContinuousWithinAt C (Ici x) x) (a : ℝ) :
    (bvSigned C hC hr a).totalVariation = (bvVariation C hC hr a).measure := by
  apply Measure.ext_of_Ioc
  intro s t hst
  apply le_antisymm ((bvSigned_variation_le C hC hr a) (Ioc s t))
  have he : (bvVariation C hC hr a).measure (Ioc s t) = eVariationOn C (Icc s t) := by
    rw [StieltjesFunction.measure_Ioc]
    change ENNReal.ofReal (variationOnFromTo C univ a t-variationOnFromTo C univ a s) = _
    rw [variationOnFromTo.sub_right hC.locallyBoundedVariationOn (mem_univ _) (mem_univ _) (mem_univ _),
      variationOnFromTo.eq_of_le C univ hst.le,univ_inter,ENNReal.ofReal_toReal (hC.mono (subset_univ _))]
  rw [he]
  exact interval_variation_le_signed_variation C (bvSigned C hC hr a)
    (bvSigned_Ioc C hC hr a) s t

end Asakura.FullAudit
