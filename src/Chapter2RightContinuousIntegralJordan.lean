import Chapter2UnboundedCumulativeAdapted
import Chapter2RightContinuousCumulative
import Chapter2CumulativeIntegral

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter2Complete
open Asakura.FullAudit
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

/-- Actual cumulative Stieltjes integration on a finite interval produces
adapted right-continuous increasing positive and negative parts. No
continuity of A, atomlessness, or deterministic bound on its mass is used. -/
theorem right_continuous_stieltjes_integral_jordan
    {Ω : Type*} (a b : ℝ) (hab : a ≤ b)
    (F : Icc a b → MeasurableSpace Ω) (hF : Monotone F)
    (A : Ω → ℝ → ℝ)
    (hA : ∀ ω, MonotoneOn (A ω) (Icc a b))
    (hr : ∀ ω t, t ∈ Icc a b → ContinuousWithinAt (A ω) (Icc a b ∩ Ici t) t)
    (hm : ∀ t : Icc a b, @Measurable _ _ (F t) inferInstance (fun ω => A ω t.val))
    (H : Ω × Icc a b → ℝ)
    (hH : @Measurable _ _ (progressiveSpace F) inferInstance H)
    (hi : ∀ ω, Integrable (fun r => H (ω,projIcc a b hab r))
      (intervalStieltjes a b hab (A ω) (hA ω) (hr ω)).measure) :
    ∃ U V : Ω → ℝ → ℝ,
      (∀ ω, Monotone (U ω) ∧ Monotone (V ω)) ∧
      (∀ ω t, ContinuousWithinAt (U ω) (Ici t) t ∧
        ContinuousWithinAt (V ω) (Ici t) t) ∧
      (∀ t : Icc a b, @Measurable _ _ (F t) inferInstance (fun ω => U ω t.val) ∧
        @Measurable _ _ (F t) inferInstance (fun ω => V ω t.val)) ∧
      (∀ ω t, (∫ r in Iic t, H (ω,projIcc a b hab r)
        ∂(intervalStieltjes a b hab (A ω) (hA ω) (hr ω)).measure) = U ω t - V ω t) := by
  let μ := fun ω => (intervalStieltjes a b hab (A ω) (hA ω) (hr ω)).measure
  let Hp := fun p => max (H p) 0
  let Hn := fun p => max (-H p) 0
  have hHp : @Measurable _ _ (progressiveSpace F) inferInstance Hp := hH.max measurable_const
  have hHn : @Measurable _ _ (progressiveSpace F) inferInstance Hn := hH.neg.max measurable_const
  have hip ω : Integrable (fun r => Hp (ω,projIcc a b hab r)) (μ ω) := (hi ω).pos_part
  have hin ω : Integrable (fun r => Hn (ω,projIcc a b hab r)) (μ ω) := (hi ω).neg_part
  let U := fun ω t => ∫ r in Iic t, Hp (ω,projIcc a b hab r) ∂μ ω
  let V := fun ω t => ∫ r in Iic t, Hn (ω,projIcc a b hab r) ∂μ ω
  refine ⟨U,V,?_,?_,?_,?_⟩
  · intro ω
    constructor
    · intro s t hst
      exact setIntegral_mono_set (hip ω).integrableOn
        (ae_of_all _ (fun r => le_max_right _ _)) (ae_of_all _ (fun r hr => hr.trans hst))
    · intro s t hst
      exact setIntegral_mono_set (hin ω).integrableOn
        (ae_of_all _ (fun r => le_max_right _ _)) (ae_of_all _ (fun r hr => hr.trans hst))
  · intro ω t
    exact ⟨right_continuous_cumulative_integral _ _ (hip ω) t,
      right_continuous_cumulative_integral _ _ (hin ω) t⟩
  · intro t
    exact ⟨cumulative_stieltjes_adapted_without_mass_bound a b hab F hF A hA hr hm Hp hHp t,
      cumulative_stieltjes_adapted_without_mass_bound a b hab F hF A hA hr hm Hn hHn t⟩
  · intro ω t
    change (∫ r in Iic t, H (ω,projIcc a b hab r) ∂μ ω) =
      (∫ r in Iic t, Hp (ω,projIcc a b hab r) ∂μ ω) -
      (∫ r in Iic t, Hn (ω,projIcc a b hab r) ∂μ ω)
    rw [← integral_sub (hip ω).integrableOn (hin ω).integrableOn]
    apply integral_congr_ae
    exact ae_of_all _ (fun r => (max_zero_sub_max_neg_zero_eq_self (H (ω,projIcc a b hab r))).symm)

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.right_continuous_stieltjes_integral_jordan
