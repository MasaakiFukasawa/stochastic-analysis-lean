import Chapter4BrownianSystem
import Chapter6MeasurableCovarianceDensity
import Chapter6CovarianceCommonTime

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter7
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter4 Asakura.Chapter6
set_option maxHeartbeats 2600000

/-- The actual quadratic variation of a continuous Brownian integrand,
identified simultaneously on each finite interval. -/
theorem continuous_ito_clock_density
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (B : BrownianSystem P 1) (Y : HalfClosedTime → Ω → ℝ)
    (hY : LocalMProcessWitness P B.F Y) (H : Ω × ℝ → ℝ)
    (hc : ∀ w,Continuous (fun r => H (w,r)))
    (hI : ItoCovarianceFormula P B.F (B.W 0) H Y) :
    ∃ C,LocalCovarianceWitness P B.F Y Y C ∧
      ∀ b : ℝ,0 ≤ b → ∀ᵐ w ∂P,∀ r ∈ Icc 0 b,
        C (realTimeClamp r) w = ∫ s in 0..r,(H (w,s))^2 := by
  have hi w b (hb : 0 ≤ b) : IntervalIntegrable (fun r => H (w,r)) volume 0 b := (hc w).intervalIntegrable 0 b
  obtain ⟨D,hD,hd⟩ := measurable_ito_clock_cross P B.F (B.W 0) (B.W 0) Y (B.C 0 0)
    (B.martingale 0) hY (B.cov 0 0) H hI True
    (by intro w r hr; simpa using B.diagonal_clock 0 w r hr) hi
  have hd' (r : ℝ) (hr : 0 ≤ r) : D (realTimeClamp r) =ᵐ[P] fun w => ∫ s in 0..r,H (w,s) := by simpa using hd r hr
  have hdcommon := covariance_density_common_time P B.F Y (B.W 0) D hY (B.martingale 0) hD H
    (fun b hb => ae_of_all _ fun w => hi w b hb) hd'
  obtain ⟨C,hC,hCeq⟩ := measurable_ito_covariance_density P B.F (B.W 0) Y Y D hY
    (hD.symm P B.F) H H (fun w => (hc w).measurable) (fun w => (hc w).measurable) hI
    (fun b hb => ae_of_all _ fun w => hi w b hb)
    (fun b _ => ae_of_all _ fun w => ((hc w).mul (hc w)).intervalIntegrable 0 b) hdcommon
  refine ⟨C,hC,?_⟩
  apply covariance_density_common_time P B.F Y Y C hY hY hC (fun z => (H z)^2)
    (fun b _ => ae_of_all _ fun w => ((hc w).pow 2).intervalIntegrable 0 b)
  intro r hr
  simpa only [pow_two] using hCeq r hr

end Asakura.Chapter7
