import Chapter2SignedDensityIntegral
import Chapter2SignedRestriction
import Chapter2StochasticIntervalIntegrand

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter2Complete
open Asakura.FullAudit
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false

theorem signed_weighted_totalVariation_ac {S : Type*} [MeasurableSpace S]
    (ν : SignedMeasure S) (g : S → ℝ) (hg : Integrable g ν.totalVariation) :
    (signedWeighted ν g).totalVariation ≪ ν.totalVariation := by
  have hp : ν.toJordanDecomposition.posPart ≤ ν.totalVariation := by intro s; exact le_add_right le_rfl
  have hn : ν.toJordanDecomposition.negPart ≤ ν.totalVariation := by intro s; exact le_add_left le_rfl
  have ha : signedWeighted ν g ≪ᵥ ν.totalVariation.toENNRealVectorMeasure := by
    apply VectorMeasure.AbsolutelyContinuous.mk
    intro B hB hz
    rw [Measure.toENNRealVectorMeasure_apply_measurable hB] at hz
    have hp0 : ν.toJordanDecomposition.posPart B = 0 := le_antisymm ((hp B).trans_eq hz) bot_le
    have hn0 : ν.toJordanDecomposition.negPart B = 0 := le_antisymm ((hn B).trans_eq hz) bot_le
    rw [signed_weighted_apply ν g hg B hB,signedIntegralRaw,integral_indicator hB,integral_indicator hB,
      Measure.restrict_zero_set hp0,Measure.restrict_zero_set hn0,integral_zero_measure,sub_self]
  simpa using (SignedMeasure.absolutelyContinuous_ennreal_iff _ _).mp ha

theorem signed_integral_supported_cumulative (ν : SignedMeasure ℝ) (g : ℝ → ℝ)
    (hg : Measurable g) (hgi : Integrable g ν.totalVariation) (d : ℝ)
    (hν : ν = ν.restrict (Iic d)) :
    signedIntegralRaw ν g = signedCumulative ν g d := by
  calc
    _ = signedIntegralRaw (ν.restrict (Iic d)) g := congrArg (fun v => signedIntegralRaw v g) hν
    _ = _ := signed_integral_restrict ν measurableSet_Iic g hg hgi.integrableOn

/-- Identify the Stieltjes measure of a cumulative signed integral, from
its actual interval increments; then establish the iterated integral rule. -/
theorem signed_cumulative_density_identification
    (ν κ : SignedMeasure ℝ) (g : ℝ → ℝ) (hg : Measurable g)
    (hgi : Integrable g ν.totalVariation) (d : ℝ)
    (hν0 : ν.totalVariation (Iic 0) = 0) (hκ0 : κ.totalVariation (Iic 0) = 0)
    (hν : ν = ν.restrict (Iic d))
    (hκ : ∀ a b, 0 ≤ a → a ≤ b → κ (Ioc a b) =
      signedCumulative ν g (min b d)-signedCumulative ν g (min a d)) :
    κ = signedWeighted ν g := by
  apply signed_measure_ext_positive_Ioc κ (signedWeighted ν g) hκ0
    ((signed_weighted_totalVariation_ac ν g hgi) hν0)
  intro a b ha hab
  rw [hκ a b ha hab,signed_weighted_apply ν g hgi _ measurableSet_Ioc,
    signed_integral_supported_cumulative ν _ (hg.indicator measurableSet_Ioc)
      (hgi.indicator measurableSet_Ioc) d hν,
    signed_cumulative_stochastic_interval ν g hgi a b d hab]

theorem signed_iterated_integral_of_cumulative
    (ν κ : SignedMeasure ℝ) (g h : ℝ → ℝ) (hg : Measurable g) (hh : Measurable h)
    (hgi : Integrable g ν.totalVariation) (hhi : Integrable h κ.totalVariation)
    (hhg : Integrable (fun r => h r*g r) ν.totalVariation) (d : ℝ)
    (hν0 : ν.totalVariation (Iic 0) = 0) (hκ0 : κ.totalVariation (Iic 0) = 0)
    (hν : ν = ν.restrict (Iic d))
    (hκ : ∀ a b, 0 ≤ a → a ≤ b → κ (Ioc a b) =
      signedCumulative ν g (min b d)-signedCumulative ν g (min a d)) :
    signedIntegralRaw κ h = signedIntegralRaw ν (fun r => h r*g r) := by
  have he := signed_cumulative_density_identification ν κ g hg hgi d hν0 hκ0 hν hκ
  apply signed_density_integral ν κ g h hg hh hgi hhi hhg
  intro B hB
  rw [he,signed_weighted_apply ν g hgi B hB]

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.signed_iterated_integral_of_cumulative
