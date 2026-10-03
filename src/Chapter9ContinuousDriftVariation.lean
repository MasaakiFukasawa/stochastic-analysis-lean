import Chapter9AdaptedTimeIntegral
import Chapter5ProgressiveDriftVariation

open MeasureTheory Set
namespace Asakura.Chapter9
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter5
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

/-- The drift primitive with a random initial value is an adapted finite
 variation process. Positive and negative time integrals give its parts. -/
theorem continuous_drift_variation {Ω : Type*} [m : MeasurableSpace Ω]
    (F : HalfClosedTime → MeasurableSpace Ω) (hF : Monotone F)
    (a : ℝ → Ω → ℝ) (x : Ω → ℝ) (hx : Measurable[F ⊥] x)
    (b : ℝ) (hb : 0≤b)
    (ha : ∀ r∈Icc 0 b,Measurable[F (realTimeClamp r)] (a r))
    (hac : ∀ w,ContinuousOn (fun r => a r w) (Icc 0 b)) :
    AdaptedLocalVariationWitness F (fun t w => x w+∫ r in 0..(finitePrefixTime b hb t).val,a r w) := by
  let μ := volume.restrict (Ioc 0 b)
  let U := fun w t => x w+∫ r in Iic t,max (a r w) 0 ∂μ
  let V := fun w t => ∫ r in Iic t,max (-a r w) 0 ∂μ
  have hi w : Integrable (fun r => a r w) μ :=
    ((hac w).intervalIntegrable_of_Icc (μ := volume) hb).1
  have hip w : Integrable (fun r => max (a r w) 0) μ := (hi w).pos_part
  have hin w : Integrable (fun r => max (-a r w) 0) μ := (hi w).neg_part
  have hUc w : Continuous (U w) := continuous_const.add (continuous_cumulative_integral μ _ (hip w))
  have hVc w : Continuous (V w) := continuous_cumulative_integral μ _ (hin w)
  have hUm w : Monotone (U w) := by
    intro s t hst
    dsimp only [U]
    apply add_le_add_right
    exact setIntegral_mono_set (hip w).integrableOn (ae_of_all _ fun r => le_max_right _ _)
      (ae_of_all _ fun r hr => hr.trans hst)
  have hVm w : Monotone (V w) := by
    intro s t hst
    exact setIntegral_mono_set (hin w).integrableOn (ae_of_all _ fun r => le_max_right _ _)
      (ae_of_all _ fun r hr => hr.trans hst)
  have had (r : Icc (0:ℝ) b) :
      Measurable[F (realTimeClamp r.val)] (fun w => U w r.val) ∧
      Measurable[F (realTimeClamp r.val)] (fun w => V w r.val) := by
    have hp : Measurable[F (realTimeClamp r.val)] (fun w => ∫ u in 0..r.val,max (a u w) 0) := by
      apply measurable_past_integral (m := F (realTimeClamp r.val)) _ _ r.property.1
      · intro u hu
        exact ((ha u ⟨hu.1,hu.2.trans r.property.2⟩).mono
          (hF (real_time_clamp_mono hu.2)) le_rfl).max measurable_const
      · intro w
        exact fun u hu => ((hac w) u ⟨hu.1,hu.2.trans r.property.2⟩).mono (Icc_subset_Icc le_rfl r.property.2) |>.max continuousWithinAt_const
    have hn : Measurable[F (realTimeClamp r.val)] (fun w => ∫ u in 0..r.val,max (-a u w) 0) := by
      apply measurable_past_integral (m := F (realTimeClamp r.val)) _ _ r.property.1
      · intro u hu
        exact ((ha u ⟨hu.1,hu.2.trans r.property.2⟩).mono
          (hF (real_time_clamp_mono hu.2)) le_rfl).neg.max measurable_const
      · intro w
        exact fun u hu => (((hac w) u ⟨hu.1,hu.2.trans r.property.2⟩).mono (Icc_subset_Icc le_rfl r.property.2)).neg.max continuousWithinAt_const
    simpa only [U,V,μ,restricted_cumulative_time_integral _ b r.val r.property] using!
      And.intro ((hx.mono (hF bot_le) le_rfl).add hp) hn
  have hv := adapted_variation_of_finite_interval_parts F hF b hb le_top U V had
    (fun w => ⟨hUm w,hVm w⟩)
    (fun w r => ⟨(hUc w).continuousAt.continuousWithinAt,(hVc w).continuousAt.continuousWithinAt⟩)
  have he : (fun t w => U w (finitePrefixTime (T := (⊤:EReal)) b hb t).val-
      V w (finitePrefixTime b hb t).val)=
      (fun t w => x w+∫ r in 0..(finitePrefixTime b hb t).val,a r w) := by
    funext t w
    dsimp only [U,V]
    rw [add_sub_assoc,← integral_sub (hip w).integrableOn (hin w).integrableOn]
    simp only [max_zero_sub_max_neg_zero_eq_self]
    rw [restricted_cumulative_time_integral _ b _ (finitePrefixTime b hb t).property]
  rw [he] at hv
  exact global_variation_localized (by simp : (0:EReal)<⊤) F hF _ hv
end Asakura.Chapter9
