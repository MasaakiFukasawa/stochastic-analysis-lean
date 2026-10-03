import Chapter12SignedWeightedIntegrability

open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace Asakura.Chapter12
open Asakura.FullAudit Asakura.Chapter2Complete
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

theorem signed_integral_eq_vector_integral {S : Type*} [MeasurableSpace S]
    (ν : SignedMeasure S) (f : S → ℝ) (hf : Integrable f ν.totalVariation) :
    signedIntegralRaw ν f=∫ᵛ x,f x ∂<•ν := by
  have hp : ν.toJordanDecomposition.posPart ≤ ν.totalVariation := by intro s; exact le_add_right le_rfl
  have hn : ν.toJordanDecomposition.negPart ≤ ν.totalVariation := by intro s; exact le_add_left le_rfl
  have he : ν=ν.toJordanDecomposition.posPart.toSignedMeasure-ν.toJordanDecomposition.negPart.toSignedMeasure :=
    ν.toSignedMeasure_toJordanDecomposition.symm
  have hpi : ν.toJordanDecomposition.posPart.toSignedMeasure.Integrable f := by
    simpa only [VectorMeasure.Integrable,Measure.variation_toSignedMeasure] using hf.mono_measure hp
  have hni : ν.toJordanDecomposition.negPart.toSignedMeasure.Integrable f := by
    simpa only [VectorMeasure.Integrable,Measure.variation_toSignedMeasure] using hf.mono_measure hn
  conv_rhs => rw [he]
  rw [VectorMeasure.integral_sub_vectorMeasure hpi hni,
    VectorMeasure.integral_toSignedMeasure,VectorMeasure.integral_toSignedMeasure]
  rfl

theorem signed_weighted_eq_vector_density {S : Type*} [MeasurableSpace S]
    (ν : SignedMeasure S) (g : S → ℝ) (hg : Integrable g ν.totalVariation) :
    signedWeighted ν g=ν.withDensity g (ContinuousLinearMap.lsmul ℝ ℝ).flip := by
  have hgi : ν.Integrable g := by
    simpa only [VectorMeasure.Integrable,← SignedMeasure.totalVariation_eq_variation] using hg
  ext A hA
  rw [signed_weighted_apply ν g hg A hA,VectorMeasure.withDensity_apply hgi,
    ← VectorMeasure.integral_indicator hA]
  exact signed_integral_eq_vector_integral ν _ (hg.indicator hA)

/-- Exact total variation of the actual signed density, including sign
changes of the integrand. -/
theorem signed_weighted_totalVariation {S : Type*} [MeasurableSpace S]
    (ν : SignedMeasure S) (g : S → ℝ) (hg : Integrable g ν.totalVariation) :
    (signedWeighted ν g).totalVariation=ν.totalVariation.withDensity (fun x => ‖g x‖ₑ) := by
  have hgi : ν.Integrable g := by
    simpa only [VectorMeasure.Integrable,← SignedMeasure.totalVariation_eq_variation] using hg
  rw [signed_weighted_eq_vector_density ν g hg,SignedMeasure.totalVariation_eq_variation,
    VectorMeasure.variation_withDensity hgi (by intro x y; simp [nnnorm_mul,mul_comm]),
    VectorMeasure.variation_transpose_lsmul_flip,← SignedMeasure.totalVariation_eq_variation]

end Asakura.Chapter12
#print axioms Asakura.Chapter12.signed_weighted_totalVariation
