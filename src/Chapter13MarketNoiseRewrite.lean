import Chapter13MarketBrownian
import Chapter12ItoIntegratorLinear

open MeasureTheory Set Filter
open scoped Topology BigOperators
namespace Asakura.Chapter13
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter12
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

/-- The original vector stochastic integral is the scalar integral against
the normalized Brownian motion. This is an identity of actual Ito integrals,
including points at which the vector coefficient vanishes. -/
theorem market_noise_rewrite {Ω:Type*} {m:MeasurableSpace Ω}
    (P:Measure Ω) [IsProbabilityMeasure P] {d:ℕ} (B:BrownianSystem P (d+1))
    (σ:Ω × ℝ → EuclideanSpace ℝ (Fin (d+1))) (hσ:Measurable σ)
    (γ:Ω × ℝ → ℝ) (hγ:Measurable γ)
    (N Y:Fin (d+1) → HalfClosedTime → Ω → ℝ)
    (hN:∀i,LocalMProcessWitness P B.F (N i)) (hY:∀i,LocalMProcessWitness P B.F (Y i))
    (hNI:∀i,ItoCovarianceFormula P B.F (B.W i) (fun z => γ z*σ z i) (N i))
    (hYI:∀i,ItoCovarianceFormula P B.F (B.W i) (fun z => σ z i/‖σ z‖) (Y i)) :
    ItoCovarianceFormula P B.F (fun t w => ∑i,Y i t w) (fun z => γ z*‖σ z‖) (fun t w => ∑i,N i t w) := by
  have he i z:γ z*‖σ z‖*(σ z i/‖σ z‖)=γ z*σ z i := by
    by_cases hz:σ z=0
    · simp [hz]
    · field_simp [norm_ne_zero_iff.mpr hz]
  have hi i:ItoCovarianceFormula P B.F (Y i) (fun z => γ z*‖σ z‖) (N i) := by
    apply ito_reverse_associativity P (by simp : (0:EReal)<⊤) B.F B.mono B.le B.null
      (B.W i) (Y i) (N i) (fun z => σ z i/‖σ z‖) (fun z => γ z*‖σ z‖)
      (B.martingale i) (hY i) (hN i)
    · intro w
      exact (((PiLp.continuous_apply 2 _ i).measurable.comp hσ).div hσ.norm).comp measurable_prodMk_left
    · intro w
      exact (hγ.mul hσ.norm).comp measurable_prodMk_left
    · exact hYI i
    · simpa only [he] using hNI i
  exact ito_integrator_nonempty_sum P (by simp) B.F B.mono B.le B.null d Y N _ hY hi
end Asakura.Chapter13
#print axioms Asakura.Chapter13.market_noise_rewrite
