import Chapter5ProgressivePrimitive
import Chapter5ClockSemimartingale
import Chapter2CumulativeIntegral

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter13
open Asakura.Chapter5 Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

lemma restricted_cumulative_time_integral_global_helper (g : ℝ → ℝ) (R r : ℝ) (hr : r∈Icc 0 R) :
    (∫ s in Iic r,g s ∂volume.restrict (Ioc 0 R))=∫ s in 0..r,g s := by
  rw [Measure.restrict_restrict measurableSet_Iic,intervalIntegral.integral_of_le hr.1]
  have he : Iic r ∩ Ioc (0:ℝ) R = Ioc 0 r := by
    ext s
    constructor
    · rintro ⟨hs,hs0,_⟩
      exact ⟨hs0,hs⟩
    · rintro ⟨hs0,hs⟩
      exact ⟨hs,hs0,hs.trans hr.2⟩
  rw [he]

/-- A progressively measurable integrable driver gives the actual adapted
finite-variation process. The positive and negative parts are constructed
as increasing continuous time integrals. -/
theorem progressive_integrable_drift_global_variation
    {Ω : Type*} {T : EReal} [Fact (0≤T)] (hT : 0<T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F)
    (R : ℝ) (hR : 0≤R) (hRT : (R:EReal)≤T)
    (G : Ω × ℝ → ℝ)
    (hGp : @Measurable _ _ (progressiveSpace (fun t : Icc (0:ℝ) R => F (realTimeClamp t.val))) inferInstance
      (fun z : Ω × Icc (0:ℝ) R => G (z.1,z.2.val)))
    (hGi : ∀ w,Integrable (fun r => G (w,r)) (volume.restrict (Ioc 0 R))) :
    ∃ A : ClosedTime T → Ω → ℝ,
      AdaptedVariationWitness F A ∧ (∀ w,Continuous (fun t => A t w)) ∧
      ∀ t w,A t w=∫ r in 0..(finitePrefixTime R hR t).val,G (w,r) := by
  let μ := volume.restrict (Ioc (0:ℝ) R)
  let gp := fun z => max (G z) 0
  let gn := fun z => max (-G z) 0
  let U := fun w t => ∫ r in Iic t,gp (w,r) ∂μ
  let V := fun w t => ∫ r in Iic t,gn (w,r) ∂μ
  have hip w : Integrable (fun r => gp (w,r)) μ := (hGi w).pos_part
  have hin w : Integrable (fun r => gn (w,r)) μ := (hGi w).neg_part
  have hUc w : Continuous (U w) := continuous_cumulative_integral μ _ (hip w)
  have hVc w : Continuous (V w) := continuous_cumulative_integral μ _ (hin w)
  have hUm w : Monotone (U w) := by
    intro s t hst
    exact setIntegral_mono_set (hip w).integrableOn (ae_of_all _ fun r => le_max_right _ _) (ae_of_all _ fun r hr => hr.trans hst)
  have hVm w : Monotone (V w) := by
    intro s t hst
    exact setIntegral_mono_set (hin w).integrableOn (ae_of_all _ fun r => le_max_right _ _) (ae_of_all _ fun r hr => hr.trans hst)
  have he w r (hr : r∈Icc 0 R) : U w r-V w r=∫ s in 0..r,G (w,s) := by
    dsimp only [U,V]
    rw [← integral_sub (hip w).integrableOn (hin w).integrableOn]
    calc
      _ = ∫ s in Iic r,G (w,s) ∂μ := by
        apply integral_congr_ae
        exact ae_of_all _ fun s => max_zero_sub_max_neg_zero_eq_self (G (w,s))
      _ = _ := restricted_cumulative_time_integral_global_helper _ R r hr
  have had (r : Icc (0:ℝ) R) : Measurable[F (realTimeClamp r.val)] (fun w => U w r.val) ∧
      Measurable[F (realTimeClamp r.val)] (fun w => V w r.val) := by
    have hp := progressive_time_primitive_adapted R hR
      (fun t : Icc (0:ℝ) R => F (realTimeClamp t.val)) gp (hGp.max measurable_const) r
    have hn := progressive_time_primitive_adapted R hR
      (fun t : Icc (0:ℝ) R => F (realTimeClamp t.val)) gn (hGp.neg.max measurable_const) r
    constructor
    · simpa only [U,μ,restricted_cumulative_time_integral_global_helper _ R r.val r.property] using hp
    · simpa only [V,μ,restricted_cumulative_time_integral_global_helper _ R r.val r.property] using hn
  let A := fun t w => U w (finitePrefixTime (T := T) R hR t).val-V w (finitePrefixTime R hR t).val
  have hAv : AdaptedVariationWitness F A := adapted_variation_of_finite_interval_parts F hF R hR hRT U V had
    (fun w => ⟨hUm w,hVm w⟩) (fun w r => ⟨(hUc w).continuousAt.continuousWithinAt,(hVc w).continuousAt.continuousWithinAt⟩)
  refine ⟨A,hAv,?_,?_⟩
  · intro w
    exact ((hUc w).sub (hVc w)).comp (continuous_subtype_val.comp (finite_prefix_time_continuous R hR))
  · intro t w
    exact he w _ (finitePrefixTime R hR t).property

end Asakura.Chapter13

#print axioms Asakura.Chapter13.progressive_integrable_drift_global_variation
#print axioms Asakura.Chapter13.restricted_cumulative_time_integral_global_helper
