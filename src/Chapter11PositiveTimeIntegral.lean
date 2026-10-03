import Chapter2ItoIntegrandEncoding

open MeasureTheory Set Filter
namespace Asakura.Chapter2Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

/-- The value at time zero is irrelevant to the actual Ito integral,
 because every covariance Stieltjes measure gives Iic 0 zero mass. -/
theorem ItoCovarianceFormula.congr_on_positive_time_domain
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (F : ClosedTime T → MeasurableSpace Ω)
    (X Y : ClosedTime T → Ω → ℝ) (H G : Ω × ℝ → ℝ)
    (h : ItoCovarianceFormula P F X H Y)
    (he : ∀ ω (r : ℝ), 0 < r → (r:EReal) < T → H (ω,r) = G (ω,r)) :
    ItoCovarianceFormula P F X G Y := by
  intro N C hN hC
  obtain ⟨D,hD,hd⟩ := h N C hN hC
  refine ⟨D,hD,?_⟩
  intro d hd0 hdT
  obtain ⟨ν,hν,hν0,hνi,hνD⟩ := hd d hd0 hdT
  have heq : ∀ᵐ ω ∂P, (fun r => H (ω,r)) =ᵐ[(ν ω).totalVariation] (fun r => G (ω,r)) := by
    filter_upwards [hν0] with ω h0
    have hr : ν ω = (ν ω).restrict (Iic d) := by
      apply signed_stopped_interval_consistency (fun r => C (realTimeClamp r) ω)
        d d hd0 le_rfl (ν ω) (ν ω) h0 h0
      all_goals
        intro a b ha hab
        simpa only [real_time_clamp_mono.map_min] using hν ω a b ha hab
    have hm : (ν ω).totalVariation = (ν ω).totalVariation.restrict (Iic d) := by
      calc
        _ = (show SignedMeasure ℝ from (ν ω).restrict (Iic d)).totalVariation := congrArg SignedMeasure.totalVariation hr
        _ = _ := signed_totalVariation_restrict _ measurableSet_Iic
    have hup : ∀ᵐ r ∂(ν ω).totalVariation, r ≤ d := by
      rw [hm]
      exact ae_restrict_mem measurableSet_Iic
    have hlo : ∀ᵐ r ∂(ν ω).totalVariation, 0 < r := by
      rw [ae_iff]
      simp only [not_lt]
      change (ν ω).totalVariation (Iic 0) = 0
      exact h0
    filter_upwards [hup,hlo] with r hr hpos
    exact he ω r hpos ((EReal.coe_le_coe hr).trans_lt hdT)
  refine ⟨ν,hν,hν0,?_,?_⟩
  · filter_upwards [hνi,heq] with ω hi heω
    exact hi.congr heω
  · filter_upwards [hνD,heq] with ω hDω heω
    exact hDω.trans (signed_integral_congr_of_absolute_continuity _ (ν ω) (by rfl) heω)

end Asakura.Chapter2Complete
