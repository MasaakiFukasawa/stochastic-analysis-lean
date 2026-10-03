import Chapter11BoundedStrategyIntegral
import Chapter5LocalPathBrownianIntegral
import Chapter2ItoAssociativity
import Chapter3OpenPathMeasurable

open MeasureTheory Set Filter
namespace Asakura.Chapter11
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter5 Asakura.Chapter6
set_option maxHeartbeats 3200000
set_option backward.isDefEq.respectTransparency false

/-- Multiply a bounded progressive Brownian integrand by a continuous
adapted process. Both resulting integrals are constructed and identified. -/
theorem bounded_brownian_integral_continuous_weight {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : BrownianSystem P 1)
    (H : Ω × ℝ → ℝ) (hHm : Measurable H)
    (hHp : ∀ d,0<d → @Measurable _ _
      (progressiveSpace (fun t : Icc (0:ℝ) d => B.F (realTimeClamp t.val))) inferInstance
      (fun z : Ω × Icc (0:ℝ) d => H (z.1,z.2.val)))
    (K : ℝ) (hK : 0≤K) (hHb : ∀ z,|H z|≤K)
    (N V : HalfClosedTime → Ω → ℝ) (hN : LocalMProcessWitness P B.F N)
    (hNI : ItoCovarianceFormula P B.F (B.W 0) H N)
    (hVa : ∀ t,t<⊤ → Measurable[B.F t] (V t))
    (hVc : ∀ w t,t<⊤ → ContinuousAt (fun s => V s w) t) :
    ∃ Z M : HalfClosedTime → Ω → ℝ,
      LocalMProcessWitness P B.F Z ∧ LocalMProcessWitness P B.F M ∧
      ItoCovarianceFormula P B.F N (fun z => V (realTimeClamp z.2) z.1) Z ∧
      ItoCovarianceFormula P B.F (B.W 0) (fun z => V (realTimeClamp z.2) z.1*H z) M ∧
      ∀ᵐ w ∂P,∀ t,t<⊤ → Z t w=M t w := by
  have hT : (0:EReal)<⊤ := by simp
  obtain ⟨c,hc,hcm,hcT,hct,hcut,hcc⟩ := positive_real_time_exhaustion hT
  have hr := open_process_real_regularity B.F V hVa hVc
  obtain ⟨Z,hZ,hZI⟩ := continuous_adapted_ito_exists P hT B.F B.mono B.le B.null N hN
    (fun z => V (realTimeClamp z.2) z.1) hr.1 hr.2
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
  have hi j : ∀ᵐ w ∂P,IntervalIntegrable (fun r => (V (realTimeClamp r) w*H (w,r))^2) volume 0 (c j) := by
    apply ae_of_all
    intro w
    apply (intervalIntegrable_iff_integrableOn_Ioc_of_le (hc j).le).mpr
    change Integrable (fun r => (V (realTimeClamp r) w*H (w,r))^2) (volume.restrict (Ioc 0 (c j)))
    have hHi : Integrable (fun r => (H (w,r))^2) (volume.restrict (Ioc 0 (c j))) := by
      simpa only [pow_two,Function.comp_def,IntegrableOn] using (bounded_product_time_integrable _ _
        (hHm.comp measurable_prodMk_left) (hHm.comp measurable_prodMk_left) K hK
        (fun r => hHb (w,r)) (fun r => hHb (w,r)) (c j) (hc j).le).1
    simpa only [mul_pow] using continuous_multiplier_integrable (c j) (hc j).le _
      ((ae_restrict_mem measurableSet_Ioc).mono fun r h => ⟨h.1.le,h.2⟩)
      (fun r => (V (realTimeClamp r) w)^2) (fun r => (H (w,r))^2)
      ((hVrc w).pow 2).continuousOn ((hVrc w).measurable.pow_const 2) hHi
  obtain ⟨M,hM,hMI⟩ := brownian_local_path_energy_integral_constructed P hT B.F B.mono B.le B.null
    (B.W 0) (B.C 0 0) (B.martingale 0) (B.cov 0 0) c hc hcm hcT hct hcut hcc
    (fun j w r h => by simpa using B.clock 0 0 w r h.1)
    (fun z => V (realTimeClamp z.2) z.1*H z) (hVm.mul hHm)
    (fun j => (hVp (c j) (hc j)).mul (hHp (c j) (hc j))) hi
  refine ⟨Z,M,hZ,hM,hZI,hMI,?_⟩
  exact ito_integral_associativity P hT B.F B.mono B.le B.null (B.W 0) N Z M H _
    (B.martingale 0) hN hZ hM (fun w => hHm.comp measurable_prodMk_left)
    (fun w => (hVrc w).measurable) hNI hZI hMI

end Asakura.Chapter11
