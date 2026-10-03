import Chapter5BracketCommonTime
import Chapter2CumulativeSupport
import Chapter2SignedDensityIntegral

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter5
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

/-- An integral against the Stieltjes measure of an indefinite time
integral is the corresponding weighted time integral. The density only
needs to be integrable, so this applies to Borel diffusion coefficients. -/
theorem cumulative_stieltjes_density_integral
    (b : ℝ) (hb : 0 ≤ b) (G H : ℝ → ℝ) (hG : Measurable G) (hH : Measurable H)
    (hi : IntervalIntegrable G volume 0 b)
    (κ : SignedMeasure ℝ) (hHi : Integrable H κ.totalVariation)
    (hHGi : IntervalIntegrable (fun r => H r*G r) volume 0 b)
    (hκ : ∀ s t, s ≤ t → κ (Ioc s t) =
      (∫ r in 0..intervalClamp 0 b hb t, G r) - (∫ r in 0..intervalClamp 0 b hb s, G r)) :
    signedIntegralRaw κ H = ∫ r in 0..b, H r*G r := by
  let μ := volume.restrict (Ioc (0:ℝ) b)
  let ν : SignedMeasure ℝ := μ.toSignedMeasure
  have hv : ν.totalVariation = μ := by
    simp only [ν,SignedMeasure.totalVariation_eq_variation,Measure.variation_toSignedMeasure]
  have hgi : Integrable G ν.totalVariation := by rw [hv]; exact hi.1
  have hhgi : Integrable (fun r => H r*G r) ν.totalVariation := by rw [hv]; exact hHGi.1
  have heq (t : ℝ) : signedCumulative ν G t = ∫ r in 0..intervalClamp 0 b hb t, G r := by
    change signedIntegralRaw ν ((Iic t).indicator G) = _
    rw [show ν = μ.toSignedMeasure from rfl,
      signed_integral_positive_measure μ _ ((show Integrable G μ from hi.1).indicator measurableSet_Iic),
      integral_indicator measurableSet_Iic]
    have hs : ∀ᵐ r ∂μ, r ∈ Ioc 0 b := ae_restrict_mem measurableSet_Ioc
    rw [cumulative_integral_clamp 0 b hb μ hs G t]
    change (∫ r in Iic (intervalClamp 0 b hb t), G r ∂volume.restrict (Ioc 0 b)) = _
    rw [Measure.restrict_restrict measurableSet_Iic,
      Iic_inter_Ioc_of_le (intervalClamp_mem 0 b hb t).2,
      intervalIntegral.integral_of_le (intervalClamp_mem 0 b hb t).1]
  have hk : κ = signedWeighted ν G := by
    apply signed_measure_ext_Ioc
    intro s t hst
    rw [hκ s t hst.le,← heq t,← heq s,signed_weighted_apply ν G hgi _ measurableSet_Ioc,
      signed_cumulative_increment ν G hgi s t hst.le]
  have he := signed_density_integral ν κ G H hG hH hgi hHi hhgi (by
    intro B hB
    rw [hk,signed_weighted_apply ν G hgi B hB])
  rw [he,show ν = μ.toSignedMeasure from rfl,
    signed_integral_positive_measure μ _ (show Integrable (fun r => H r*G r) μ from hHGi.1)]
  exact (intervalIntegral.integral_of_le hb).symm

end Asakura.Chapter5
