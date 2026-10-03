import Chapter2SignedElementaryIntegral

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter2Complete
open Asakura.FullAudit
set_option maxHeartbeats 900000

/-- The interval CS estimate ensures that identifying integrands for the
quadratic-variation measure also identifies their covariance integrals. -/
theorem signed_cs_absolute_continuity
    (α β : Measure ℝ) [IsFiniteMeasure α] [IsFiniteMeasure β] (ν : SignedMeasure ℝ)
    (hc : ∀ s t, s ≤ t → |ν (Ioc s t)| ≤ Real.sqrt (α.real (Ioc s t))*Real.sqrt (β.real (Ioc s t))) :
    ν.totalVariation ≪ α := by
  apply Measure.AbsolutelyContinuous.mk
  intro s hs hzero
  have h := signed_cs_totalVariation α β ν (signed_cs_real_intervals α β ν hc) hs
  have hz : α.real s = 0 := by simp [Measure.real,hzero]
  simpa only [hz,Real.sqrt_zero,zero_mul,ENNReal.ofReal_zero,le_zero_iff] using h

theorem signed_integral_congr_of_absolute_continuity
    {S : Type*} [MeasurableSpace S] (μ : Measure S) (ν : SignedMeasure S)
    (hν : ν.totalVariation ≪ μ) {f g : S → ℝ} (hfg : f =ᵐ[μ] g) :
    signedIntegralRaw ν f = signedIntegralRaw ν g := by
  exact signedIntegralRaw_congr_ae ν.totalVariation ν 1 (by norm_num) (by simp) (hν.ae_eq hfg)

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.signed_cs_absolute_continuity
#print axioms Asakura.Chapter2Complete.signed_integral_congr_of_absolute_continuity
