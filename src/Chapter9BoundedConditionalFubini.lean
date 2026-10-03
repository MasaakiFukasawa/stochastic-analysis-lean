import Chapter9ConditionalFubini
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real

open MeasureTheory Set
namespace Asakura.Chapter9
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

 theorem measurable_product_bound {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S]
    (P : Measure Ω) (μ : Measure S) [SFinite P] [SFinite μ]
    (H : Ω × S → ℝ) (hm : Measurable H) (C : ℝ)
    (hb : ∀ᵐ s ∂μ,∀ᵐ w ∂P,‖H (w,s)‖≤C) : ∀ᵐ z ∂P.prod μ,‖H z‖≤C := by
  have hs : MeasurableSet {z | ‖H z‖≤C} := measurableSet_le hm.norm measurable_const
  exact (Measure.ae_prod_iff_ae_ae hs).mpr ((Measure.ae_ae_comm hs).mpr hb)

/-- Conditional Fubini with bounded sections. Integrability of the
conditional transition field follows from the conditional-expectation bound;
it is not assumed as an extra unproved regularity condition. -/
theorem bounded_conditional_integral_exchange {Ω S : Type*} [m : MeasurableSpace Ω]
    [MeasurableSpace S] (P : Measure Ω) [IsProbabilityMeasure P]
    (μ : Measure S) [IsFiniteMeasure μ] (H K : Ω × S → ℝ)
    (hH : Measurable H) (hK : Measurable K) (C : ℝ)
    (hb : ∀ᵐ s ∂μ,∀ᵐ w ∂P,‖H (w,s)‖≤C)
    (F : MeasurableSpace Ω) (hle : F≤m)
    (hm : AEStronglyMeasurable[F] (fun w => ∫ s,K (w,s) ∂μ) P)
    (he : ∀ᵐ s ∂μ,P[(fun w => H (w,s))|F]=ᵐ[P] (fun w => K (w,s))) :
    Integrable (fun w => ∫ s,H (w,s) ∂μ) P ∧
      P[(fun w => ∫ s,H (w,s) ∂μ)|F]=ᵐ[P] (fun w => ∫ s,K (w,s) ∂μ) := by
  letI : MeasurableSpace Ω := m
  have hiH : Integrable H (P.prod μ) := Integrable.of_bound hH.aestronglyMeasurable C
    (measurable_product_bound P μ H hH C hb)
  have hbK : ∀ᵐ s ∂μ,∀ᵐ w ∂P,‖K (w,s)‖≤C := by
    filter_upwards [he,hb] with s hs hbs
    have hh := ae_bdd_norm_condExp_of_ae_bdd_norm (m := F) hbs
    filter_upwards [hs,hh] with w hw hb
    rw [hw] at hb
    exact hb
  have hiK : Integrable K (P.prod μ) := Integrable.of_bound hK.aestronglyMeasurable C
    (measurable_product_bound P μ K hK C hbK)
  exact ⟨hiH.integral_prod_left,conditional_integral_exchange P μ H K hiH hiK F hle hm he⟩
end Asakura.Chapter9
