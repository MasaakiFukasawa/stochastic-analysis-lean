import Chapter12SignedDensityVariation
open MeasureTheory
namespace Asakura.Chapter12
open Asakura.FullAudit Asakura.Chapter2Complete

theorem signed_add_integrable {S : Type*} [MeasurableSpace S]
    (ν κ : SignedMeasure S) (f : S → ℝ)
    (hν : Integrable f ν.totalVariation) (hκ : Integrable f κ.totalVariation) :
    Integrable f (ν+κ).totalVariation := by
  rw [SignedMeasure.totalVariation_eq_variation]
  apply (integrable_add_measure.mpr ⟨hν,hκ⟩).mono_measure
  simpa only [SignedMeasure.totalVariation_eq_variation] using
    (VectorMeasure.variation_add_le (μ:=ν) (ν:=κ))

theorem signed_integral_add_measure {S : Type*} [MeasurableSpace S]
    (ν κ : SignedMeasure S) (f : S → ℝ)
    (hν : Integrable f ν.totalVariation) (hκ : Integrable f κ.totalVariation) :
    signedIntegralRaw (ν+κ) f=signedIntegralRaw ν f+signedIntegralRaw κ f := by
  rw [signed_integral_eq_vector_integral _ _ (signed_add_integrable ν κ f hν hκ),
    signed_integral_eq_vector_integral _ _ hν,signed_integral_eq_vector_integral _ _ hκ]
  exact VectorMeasure.integral_add_vectorMeasure
    (by simpa only [VectorMeasure.Integrable,←SignedMeasure.totalVariation_eq_variation] using hν)
    (by simpa only [VectorMeasure.Integrable,←SignedMeasure.totalVariation_eq_variation] using hκ)
end Asakura.Chapter12
#print axioms Asakura.Chapter12.signed_integral_add_measure
