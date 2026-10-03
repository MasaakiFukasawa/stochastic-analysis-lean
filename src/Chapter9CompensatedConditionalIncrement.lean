import Chapter9BoundedConditionalFubini

open MeasureTheory
namespace Asakura.Chapter9
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

/-- The integrated transition identity and conditional Fubini produce the
conditional zero-mean compensated increment used in the martingale proof. -/
theorem compensated_conditional_increment {Ω S : Type*} [m : MeasurableSpace Ω]
    [MeasurableSpace S] (P : Measure Ω) [IsProbabilityMeasure P]
    (μ : Measure S) [IsFiniteMeasure μ] (H K : Ω × S → ℝ)
    (hH : Measurable H) (hK : Measurable K) (C : ℝ)
    (hb : ∀ᵐ s ∂μ,∀ᵐ w ∂P,‖H (w,s)‖≤C)
    (F : MeasurableSpace Ω) (hle : F≤m)
    (hm : AEStronglyMeasurable[F] (fun w => ∫ s,K (w,s) ∂μ) P)
    (he : ∀ᵐ s ∂μ,P[(fun w => H (w,s))|F]=ᵐ[P] (fun w => K (w,s)))
    (U V : Ω → ℝ) (hU : Integrable U P)
    (htrans : P[U|F]=ᵐ[P] (fun w => V w+∫ s,K (w,s) ∂μ)) :
    P[(fun w => U w-∫ s,H (w,s) ∂μ)|F]=ᵐ[P] V := by
  letI : MeasurableSpace Ω := m
  obtain ⟨hi,hce⟩ := bounded_conditional_integral_exchange P μ H K hH hK C hb F hle hm he
  have hh := condExp_sub hU hi F
  apply hh.trans
  filter_upwards [htrans,hce] with w hw hk
  change P[U|F] w-P[(fun w => ∫ s,H (w,s) ∂μ)|F] w=V w
  rw [hw,hk]
  ring
end Asakura.Chapter9
