import Chapter11BoundedStrategyIntegral
import Chapter5LocalPathBrownianIntegral
import Chapter11WealthJoint
import Chapter11IntegralMeanZero
import Chapter3OpenPathMeasurable

open MeasureTheory Set Filter
namespace Asakura.Chapter11
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter5 Asakura.Chapter6
set_option maxHeartbeats 3200000
set_option backward.isDefEq.respectTransparency false

/-- Measurability and local energy of a continuous adapted process times
an arbitrary bounded progressive coefficient. -/
theorem continuous_weight_bounded_energy {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : BrownianSystem P 1)
    (H : Ω × ℝ → ℝ) (hHm : Measurable H)
    (hHp : ∀ d,0<d → @Measurable _ _
      (progressiveSpace (fun t : Icc (0:ℝ) d => B.F (realTimeClamp t.val))) inferInstance
      (fun z : Ω × Icc (0:ℝ) d => H (z.1,z.2.val)))
    (K : ℝ) (hK : 0≤K) (hHb : ∀ z,|H z|≤K)
    (V : HalfClosedTime → Ω → ℝ)
    (hVa : ∀ t,t<⊤ → Measurable[B.F t] (V t))
    (hVc : ∀ w t,t<⊤ → ContinuousAt (fun s => V s w) t) :
    Measurable (fun z : Ω × ℝ => V (realTimeClamp z.2) z.1) ∧
    (∀ d,0<d → @Measurable _ _
      (progressiveSpace (fun t : Icc (0:ℝ) d => B.F (realTimeClamp t.val))) inferInstance
      (fun z : Ω × Icc (0:ℝ) d => V (realTimeClamp z.2.val) z.1*H (z.1,z.2.val))) ∧
    ∀ d,0<d → ∀ᵐ w ∂P,IntervalIntegrable (fun r => (V (realTimeClamp r) w*H (w,r))^2) volume 0 d := by
  have hr := open_process_real_regularity B.F V hVa hVc
  have htime (r : ℝ) : realTimeClamp (T:=(⊤:EReal)) r<⊤ :=
    (real_time_clamp_mono (le_max_left r 0)).trans_lt (real_time_below (max r 0) (le_max_right r 0) (EReal.coe_lt_top _))
  have hVrc w : Continuous (fun r : ℝ => V (realTimeClamp r) w) := by
    apply continuous_iff_continuousAt.mpr
    intro r
    exact (hVc w _ (htime r)).comp real_time_clamp_continuous.continuousAt
  have hVm : Measurable (fun z : Ω × ℝ => V (realTimeClamp z.2) z.1) :=
    (measurable_uncurry_of_continuous_of_measurable hVrc (fun r => (hVa _ (htime r)).mono (B.le _) le_rfl)).comp measurable_swap
  have hVp d (hd : 0<d) := continuous_adapted_real_progressive B.F B.mono
    (fun z => V (realTimeClamp z.2) z.1) d hd.le
    (fun r h => hr.1 r h.1 (EReal.coe_lt_top r)) (fun w => (hVrc w).continuousOn)
  have hi d (hd : 0<d) : ∀ᵐ w ∂P,IntervalIntegrable (fun r => (V (realTimeClamp r) w*H (w,r))^2) volume 0 d := by
    apply ae_of_all
    intro w
    apply (intervalIntegrable_iff_integrableOn_Ioc_of_le hd.le).mpr
    change Integrable (fun r => (V (realTimeClamp r) w*H (w,r))^2) (volume.restrict (Ioc 0 d))
    have hHi : Integrable (fun r => (H (w,r))^2) (volume.restrict (Ioc 0 d)) := by
      simpa only [pow_two,Function.comp_def,IntegrableOn] using (bounded_product_time_integrable _ _
        (hHm.comp measurable_prodMk_left) (hHm.comp measurable_prodMk_left) K hK
        (fun r => hHb (w,r)) (fun r => hHb (w,r)) d hd.le).1
    simpa only [mul_pow] using continuous_multiplier_integrable d hd.le _
      ((ae_restrict_mem measurableSet_Ioc).mono fun r h => ⟨h.1.le,h.2⟩)
      (fun r => (V (realTimeClamp r) w)^2) (fun r => (H (w,r))^2)
      ((hVrc w).pow 2).continuousOn ((hVrc w).measurable.pow_const 2) hHi
  exact ⟨hVm,fun d hd => (hVp d hd).mul (hHp d hd),hi⟩

end Asakura.Chapter11
