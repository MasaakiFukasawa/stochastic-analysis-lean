import Chapter7ConditionalIntegralMean

open MeasureTheory Set
namespace Asakura.Chapter9
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false

/-- Conditional Fubini with state-dependent conditional means, proved from
set integrals. This is the exchange needed for a reverse transition kernel. -/
theorem conditional_integral_exchange {Ω S E : Type*} [m : MeasurableSpace Ω]
    [MeasurableSpace S] [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (P : Measure Ω) [IsProbabilityMeasure P] (μ : Measure S) [SigmaFinite μ]
    (H K : Ω × S → E) (hH : Integrable H (P.prod μ)) (hK : Integrable K (P.prod μ))
    (F : MeasurableSpace Ω) (hle : F≤m)
    (hm : AEStronglyMeasurable[F] (fun w => ∫ s,K (w,s) ∂μ) P)
    (he : ∀ᵐ s ∂μ,P[(fun w => H (w,s))|F] =ᵐ[P] fun w => K (w,s)) :
    P[(fun w => ∫ s,H (w,s) ∂μ)|F] =ᵐ[P] (fun w => ∫ s,K (w,s) ∂μ) := by
  letI : MeasurableSpace Ω := m
  apply (ae_eq_condExp_of_forall_setIntegral_eq hle hH.integral_prod_left
    (fun A _ _ => hK.integral_prod_left.integrableOn) ?_ hm).symm
  intro A hA _
  have hHr : Integrable H ((P.restrict A).prod μ) :=
    hH.mono_measure (Measure.prod_mono Measure.restrict_le_self le_rfl)
  have hKr : Integrable K ((P.restrict A).prod μ) :=
    hK.mono_measure (Measure.prod_mono Measure.restrict_le_self le_rfl)
  rw [integral_integral_swap (f := fun w s => K (w,s)) hKr,
    integral_integral_swap (f := fun w s => H (w,s)) hHr]
  apply integral_congr_ae
  filter_upwards [he,hH.prod_left_ae] with s hs hsi
  rw [←setIntegral_condExp hle hsi hA]
  exact setIntegral_congr_ae (hle A hA) (hs.symm.mono (fun w hw _ => hw))
end Asakura.Chapter9
