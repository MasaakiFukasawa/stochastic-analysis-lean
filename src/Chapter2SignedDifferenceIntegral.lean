import Chapter2SignedRestriction

open MeasureTheory Set Filter
open scoped Topology ENNReal Classical
namespace Asakura.Chapter2Complete
open Asakura.FullAudit
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

theorem signed_difference_variation_le
    {S : Type*} [MeasurableSpace S] (α β : Measure S)
    [IsFiniteMeasure α] [IsFiniteMeasure β] :
    (α.toSignedMeasure-β.toSignedMeasure).totalVariation ≤ α+β := by
  rw [SignedMeasure.totalVariation_eq_variation]
  simpa only [Measure.variation_toSignedMeasure] using
    (VectorMeasure.variation_sub_le (μ := α.toSignedMeasure) (ν := β.toSignedMeasure))

/-- Decomposition independence for an integrable function, without adding
measurability outside the supporting finite time interval. -/
theorem signed_difference_integral
    {S : Type*} [MeasurableSpace S] (α β : Measure S)
    [IsFiniteMeasure α] [IsFiniteMeasure β]
    (f : S → ℝ) (hi : Integrable f (α+β)) :
    signedIntegralRaw (α.toSignedMeasure-β.toSignedMeasure) f =
      (∫ r, f r ∂α)-(∫ r, f r ∂β) := by
  let ν : SignedMeasure S := α.toSignedMeasure-β.toSignedMeasure
  have hd : ν.totalVariation ≤ α+β := signed_difference_variation_le α β
  let g := hi.aestronglyMeasurable.mk f
  have hg : Measurable g := hi.aestronglyMeasurable.stronglyMeasurable_mk.measurable
  have he : f =ᵐ[α+β] g := hi.aestronglyMeasurable.ae_eq_mk
  have hig : Integrable g (α+β) := hi.congr he
  have hset : ∀ B, MeasurableSet B → α.real B-β.real B =
      ν.toJordanDecomposition.posPart.real B-ν.toJordanDecomposition.negPart.real B := by
    intro B hB
    rw [← ν.apply_eq_posPart_real_sub_negPart_real hB]
    change _ = (α.toSignedMeasure-β.toSignedMeasure) B
    rw [VectorMeasure.sub_apply,Measure.toSignedMeasure_apply_measurable hB,
      Measure.toSignedMeasure_apply_measurable hB]
  have hid := signed_integral_independent_written α β ν.toJordanDecomposition.posPart
    ν.toJordanDecomposition.negPart hset hd g hg hig
  have hp : ν.toJordanDecomposition.posPart ≤ α+β :=
    (show ν.toJordanDecomposition.posPart ≤ ν.totalVariation from fun B => le_add_right le_rfl).trans hd
  have hn : ν.toJordanDecomposition.negPart ≤ α+β :=
    (show ν.toJordanDecomposition.negPart ≤ ν.totalVariation from fun B => le_add_left le_rfl).trans hd
  change (∫ r, f r ∂ν.toJordanDecomposition.posPart)-(∫ r, f r ∂ν.toJordanDecomposition.negPart) = _
  rw [integral_congr_ae (ae_mono hp he),integral_congr_ae (ae_mono hn he),hid]
  rw [integral_congr_ae (ae_mono (show α ≤ α+β from fun B => le_add_right le_rfl) he),
    integral_congr_ae (ae_mono (show β ≤ α+β from fun B => le_add_left le_rfl) he)]

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.signed_difference_integral
