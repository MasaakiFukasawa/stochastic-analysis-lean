import Chapter5DominatedLocalMean
import Chapter3ItoVariationCovariance
import Chapter3LocalItoFormula
import Chapter2LocalCovarianceAE

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter5
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

/-- Stochastic integration preserves zero covariation. The zero measure
in the variation integral is constructed explicitly. -/
theorem ito_preserves_zero_covariation
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (hT : 0 < T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t ≤ m)
    (X Y N : ClosedTime T → Ω → ℝ)
    (hY : LocalMProcessWitness P F Y) (hN : LocalMProcessWitness P F N)
    (hzero : LocalCovarianceWitness P F X N (fun _ _ => 0))
    (H : Ω × ℝ → ℝ) (hHm : ∀ w,Measurable (fun r => H (w,r)))
    (hI : ItoCovarianceFormula P F X H Y) :
    LocalCovarianceWitness P F Y N (fun _ _ => 0) := by
  obtain ⟨c,hc,_,hcT,_,_,hcc⟩ := positive_real_time_exhaustion hT
  obtain ⟨D,hD,he⟩ := ito_covariance_identified_with_variation_integral P hT F
    X Y N (fun _ _ => 0) (fun _ _ => 0) hY hN hzero H hHm hI
    c (fun n => (hc n).le) hcT hcc (fun _ _ _ => continuousAt_const)
    (zero_variation_integral P c (fun n => (hc n).le) H)
  refine ⟨?_,?_⟩
  · simp only [sub_zero]
    apply hD.defect.congr_ae_of_stopped_regular P F
    · filter_upwards [he] with w hw
      intro t ht
      rw [hw t ht,sub_zero]
    · intro σ hσ hσt
      obtain ⟨hym,hyc⟩ := hY.stopped_regular P F hF hle σ hσ hσt
      obtain ⟨hnm,hnc⟩ := hN.stopped_regular P F hF hle σ hσ hσt
      exact ⟨fun t => (hym t).mul (hnm t),fun w => (hyc w).mul (hnc w)⟩
  · simpa only [zero_mul] using hD.variation.smul F 0

/-- Distinct Brownian coordinate integrals are orthogonal in terminal L².
Both covariance transformations and uniform integrability of their product
are derived, so the multi-coordinate Cauchy argument needs no assumed
orthogonality of the integrals. -/
theorem ito_integrals_terminal_orthogonal
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (hT : 0 < T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t ≤ m)
    (W V X Y : ClosedTime T → Ω → ℝ)
    (hW : LocalMProcessWitness P F W) (hV : LocalMProcessWitness P F V)
    (hX : ContinuousM2Witness P F X) (hY : ContinuousM2Witness P F Y)
    (hWV : LocalCovarianceWitness P F W V (fun _ _ => 0))
    (H G : Ω × ℝ → ℝ) (hHm : ∀ w,Measurable (fun r => H (w,r)))
    (hGm : ∀ w,Measurable (fun r => G (w,r)))
    (hXI : ItoCovarianceFormula P F W H X) (hYI : ItoCovarianceFormula P F V G Y) :
    (∫ w,X ⊤ w*Y ⊤ w ∂P) = 0 := by
  obtain ⟨c,_,_,_,hct,hcut,hcc⟩ := positive_real_time_exhaustion hT
  have hXL := continuous_m2_is_local P F hF hle (fun n => realTimeClamp (c n)) hct.monotone hcut hcc X hX
  have hYL := continuous_m2_is_local P F hF hle (fun n => realTimeClamp (c n)) hct.monotone hcut hcc Y hY
  have hXV := ito_preserves_zero_covariation P hT F hF hle W X V hXL hV hWV H hHm hXI
  have hYX := ito_preserves_zero_covariation P hT F hF hle V Y X hYL hXL hXV.symm G hGm hYI
  have hXY : LocalMProcessWitness P F (fun t w => X t w*Y t w) := by
    simpa only [sub_zero] using hYX.symm.defect
  exact M2_product_local_orthogonal P F hF hle X Y hX hY hXY

end Asakura.Chapter5
