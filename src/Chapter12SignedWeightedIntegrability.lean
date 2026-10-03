import Chapter2SignedDensityIdentification
import Mathlib.MeasureTheory.VectorMeasure.WithDensityVec
import Mathlib.MeasureTheory.VectorMeasure.Variation.SignedMeasure

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter12
open Asakura.Chapter2Complete
set_option maxHeartbeats 1200000

/-- Integrability for the actual signed density follows from the product,
so reverse Ito associativity need not assume an already constructed integral. -/
theorem signed_weighted_integrable {S : Type*} [MeasurableSpace S]
    (ν : SignedMeasure S) (g h : S → ℝ) (hg : Measurable g) (hh : Measurable h)
    (hgi : Integrable g ν.totalVariation)
    (hprod : Integrable (fun x => h x*g x) ν.totalVariation) :
    Integrable h (signedWeighted ν g).totalVariation := by
  have hp : ν.toJordanDecomposition.posPart ≤ ν.totalVariation := by intro s; exact le_add_right le_rfl
  have hn : ν.toJordanDecomposition.negPart ≤ ν.totalVariation := by intro s; exact le_add_left le_rfl
  have hbound : (signedWeighted ν g).totalVariation ≤
      ν.toJordanDecomposition.posPart.withDensity (fun x => ‖g x‖ₑ) +
      ν.toJordanDecomposition.negPart.withDensity (fun x => ‖g x‖ₑ) := by
    rw [SignedMeasure.totalVariation_eq_variation, signedWeighted]
    calc
      _ ≤ _ := VectorMeasure.variation_sub_le
      _ = _ := by rw [Measure.variation_withDensityᵥ (hgi.mono_measure hp),
        Measure.variation_withDensityᵥ (hgi.mono_measure hn)]
  have hi (μ : Measure S) (hμ : μ ≤ ν.totalVariation) :
      Integrable h (μ.withDensity (fun x => ‖g x‖ₑ)) := by
    apply (integrable_withDensity_iff_integrable_smul' hg.enorm
      (ae_of_all _ (fun x => enorm_lt_top))).2
    apply Integrable.mono' (hprod.mono_measure hμ).norm
      ((hg.norm.mul hh).aestronglyMeasurable)
    exact ae_of_all _ (fun x => by simp [norm_mul, mul_comm])
  exact ((hi _ hp).add_measure (hi _ hn)).mono_measure hbound

end Asakura.Chapter12
#print axioms Asakura.Chapter12.signed_weighted_integrable
