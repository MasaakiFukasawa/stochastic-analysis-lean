import Chapter2ItoCovarianceCharacterization

open MeasureTheory Set Filter
namespace Asakura.Chapter7
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete

/-- A common almost-everywhere identity of integrands preserves the actual
signed-integral characterization of the Ito integral. -/
theorem ito_integrand_common_ae
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (F : ClosedTime T → MeasurableSpace Ω)
    (X Y : ClosedTime T → Ω → ℝ) (H G : Ω × ℝ → ℝ)
    (h : ItoCovarianceFormula P F X H Y)
    (he : ∀ᵐ w ∂P,∀ r,H (w,r) = G (w,r)) :
    ItoCovarianceFormula P F X G Y := by
  intro Y0 C0 hY0 hC0
  obtain ⟨D,hD,hd⟩ := h Y0 C0 hY0 hC0
  refine ⟨D,hD,?_⟩
  intro d hd0 hdT
  obtain ⟨ν,hν,hzero,hi,hint⟩ := hd d hd0 hdT
  refine ⟨ν,hν,hzero,?_,?_⟩
  · filter_upwards [he,hi] with w hw hiw
    simpa only [← funext hw] using hiw
  · filter_upwards [he,hint] with w hw hiw
    simpa only [← funext hw] using hiw

end Asakura.Chapter7
