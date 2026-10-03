import Chapter11BoundedStrategyIntegral
import Chapter5BrownianIntegralBracket

open MeasureTheory Set Filter
namespace Asakura.Chapter11
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter5 Asakura.Chapter6
set_option maxHeartbeats 3200000
set_option backward.isDefEq.respectTransparency false

/-- Finite expected Brownian energy makes the actual local integral a true
square-integrable martingale up to the given time, hence of mean zero. -/
theorem brownian_finite_energy_mean_zero {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : BrownianSystem P 1)
    (G : Ω × ℝ → ℝ) (hGm : Measurable G)
    (hGp : ∀ d,0<d → @Measurable _ _
      (progressiveSpace (fun t : Icc (0:ℝ) d => B.F (realTimeClamp t.val))) inferInstance
      (fun z : Ω × Icc (0:ℝ) d => G (z.1,z.2.val)))
    (hGi : ∀ d,0<d → ∀ᵐ w ∂P,IntervalIntegrable (fun r => (G (w,r))^2) volume 0 d)
    (N : HalfClosedTime → Ω → ℝ) (hN : LocalMProcessWitness P B.F N)
    (hNI : ItoCovarianceFormula P B.F (B.W 0) G N)
    (R : ℝ) (hR : 0≤R)
    (hE : Integrable (fun z => (G z)^2) (P.prod (volume.restrict (Icc 0 R)))) :
    ContinuousM2Witness P B.F (fun t w => N (min (realTimeClamp R) t) w) ∧
    Integrable (N (realTimeClamp R)) P ∧ (∫ w,N (realTimeClamp R) w ∂P)=0 := by
  have hT : (0:EReal)<⊤ := by simp
  obtain ⟨c,hc,hcm,hcT,hct,hcut,hcc⟩ := positive_real_time_exhaustion hT
  obtain ⟨C,hC,hCe⟩ := clock_ito_integral_bracket P hT B.F B.mono B.le B.null
    (B.W 0) (B.C 0 0) N (B.martingale 0) (B.cov 0 0) hN
    c hc hcm hcT hct hcut hcc (fun j w r hr => by simpa using B.clock 0 0 w r hr.1)
    G (fun j => hGp (c j) (hc j)) (fun j => hGi (c j) (hc j)) hNI
  have he : C (realTimeClamp R)=ᵐ[P] fun w => ∫ r in Icc 0 R,(G (w,r))^2 := by
    filter_upwards [hCe R hR (EReal.coe_lt_top R)] with w hw
    rw [hw,intervalIntegral.integral_of_le hR,integral_Icc_eq_integral_Ioc]
  have hi : Integrable (C (realTimeClamp R)) P := hE.integral_prod_left.congr he.symm
  have hs t : MeasurableSet[B.F t] {w : Ω | realTimeClamp (T := (⊤:EReal)) R≤t} := by
    by_cases h : realTimeClamp (T := (⊤:EReal)) R≤t <;> simp [h]
  have hh := stopped_local_M2_equivalences P B.F B.mono B.le B.null N C hN hC
    (fun _ => realTimeClamp R) hs (fun _ => real_time_below R hR (EReal.coe_lt_top R))
  have hm := hh.2.mp (hh.1.mp hi)
  have hni : Integrable (N (realTimeClamp R)) P := by
    simpa only [min_self] using (hm.moment (realTimeClamp R)).integrable (by norm_num)
  have hz := integral_congr_ae ((hm.martingale ⊥ (realTimeClamp R) bot_le).trans hm.initial)
  rw [integral_condExp (B.le ⊥)] at hz
  exact ⟨hm,hni,by simpa only [min_self,Pi.zero_apply,integral_zero] using hz⟩

end Asakura.Chapter11
