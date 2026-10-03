import Chapter2SignedMeasureIdentification
import FullAuditSignedIntegral
import Mathlib.MeasureTheory.VectorMeasure.Variation.SignedMeasure

open MeasureTheory Set
namespace Asakura.Chapter2Complete
open Asakura.FullAudit
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

theorem signed_totalVariation_restrict {S : Type*} [MeasurableSpace S]
    (ν : SignedMeasure S) {B : Set S} (hB : MeasurableSet B) :
    (show SignedMeasure S from ν.restrict B).totalVariation = ν.totalVariation.restrict B := by
  simp only [SignedMeasure.totalVariation_eq_variation, VectorMeasure.variation_restrict hB]

/-- Restricting the actual signed measure agrees with an indicator in the
Jordan integral. This uses the manuscript's decomposition-independence proof. -/
theorem signed_integral_restrict {S : Type*} [MeasurableSpace S]
    (ν : SignedMeasure S) {B : Set S} (hB : MeasurableSet B)
    (f : S → ℝ) (hm : Measurable f) (hi : Integrable f (ν.totalVariation.restrict B)) :
    signedIntegralRaw (ν.restrict B) f = signedIntegralRaw ν (B.indicator f) := by
  let κ : SignedMeasure S := ν.restrict B
  have he : ∀ E, MeasurableSet E →
      (ν.toJordanDecomposition.posPart.restrict B).real E -
        (ν.toJordanDecomposition.negPart.restrict B).real E =
      κ.toJordanDecomposition.posPart.real E - κ.toJordanDecomposition.negPart.real E := by
    intro E hE
    rw [← κ.apply_eq_posPart_real_sub_negPart_real hE]
    change _ = (ν.restrict B) E
    rw [VectorMeasure.restrict_apply ν hB hE]
    rw [ν.apply_eq_posPart_real_sub_negPart_real (hE.inter hB)]
    simp only [Measure.real, Measure.restrict_apply hE]
  have hd : κ.toJordanDecomposition.posPart + κ.toJordanDecomposition.negPart =
      ν.toJordanDecomposition.posPart.restrict B + ν.toJordanDecomposition.negPart.restrict B := by
    change κ.totalVariation = _
    rw [signed_totalVariation_restrict ν hB]
    exact Measure.restrict_add _ _ _
  have hi' : Integrable f
      (ν.toJordanDecomposition.posPart.restrict B + ν.toJordanDecomposition.negPart.restrict B) := by
    rw [← Measure.restrict_add]
    exact hi
  have h := signed_integral_independent_written
    (ν.toJordanDecomposition.posPart.restrict B) (ν.toJordanDecomposition.negPart.restrict B)
    κ.toJordanDecomposition.posPart κ.toJordanDecomposition.negPart he hd.le f hm hi'
  change (∫ x, f x ∂κ.toJordanDecomposition.posPart) -
    (∫ x, f x ∂κ.toJordanDecomposition.negPart) = _
  rw [h]
  simp only [signedIntegralRaw, integral_indicator hB]

/-- Finite-horizon covariance measures are consistent under restriction.
Only their interval increments and absence of mass before time zero enter. -/
theorem signed_stopped_interval_consistency (C : ℝ → ℝ) (b d : ℝ) (hd : 0 ≤ d)
    (hdb : d ≤ b) (ν κ : SignedMeasure ℝ)
    (hν0 : ν.totalVariation (Iic 0) = 0) (hκ0 : κ.totalVariation (Iic 0) = 0)
    (hν : ∀ s t, 0 ≤ s → s ≤ t → ν (Ioc s t) = C (min t d)-C (min s d))
    (hκ : ∀ s t, 0 ≤ s → s ≤ t → κ (Ioc s t) = C (min t b)-C (min s b)) :
    ν = κ.restrict (Iic d) := by
  apply signed_measure_ext_positive_Ioc ν _ hν0
  · rw [signed_totalVariation_restrict κ measurableSet_Iic, Measure.restrict_apply measurableSet_Iic]
    exact measure_mono_null inter_subset_left hκ0
  · intro s t hs hst
    rw [VectorMeasure.restrict_apply κ measurableSet_Iic measurableSet_Ioc]
    have he : Ioc s t ∩ Iic d = Ioc s (min t d) := by ext r; simp
    rw [he,hν s t hs hst]
    by_cases hsd : s ≤ d
    · rw [hκ s (min t d) hs (le_min hst hsd), min_eq_left ((min_le_right t d).trans hdb),
        min_eq_left (hsd.trans hdb), min_eq_left hsd]
    · have hds := (lt_of_not_ge hsd).le
      rw [Ioc_eq_empty_of_le ((min_le_right t d).trans hds), VectorMeasure.empty,
        min_eq_right hds, min_eq_right (hds.trans hst), sub_self]

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.signed_integral_restrict
#print axioms Asakura.Chapter2Complete.signed_stopped_interval_consistency
