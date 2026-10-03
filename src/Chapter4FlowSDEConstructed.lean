import Chapter4BrownianVariationIto
import Chapter4ODEVariationDensity
import Chapter4FlowDrift
import Chapter4ClockVariationIntegral
import Chapter3OpenPathMeasurable

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter4
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter5
set_option maxHeartbeats 3600000
set_option backward.isDefEq.respectTransparency false

/-- The manuscript's random-ODE flow construction, in its Ito form. The
variation of Y, the stochastic integral, and both drift identifications are
proved from the displayed ODE and the Brownian bracket. -/
theorem flow_random_ode_constructed_sde
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0≤T)] (hT : 0<T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (hnull : ∀ t E,MeasurableSet[m] E → P E=0 → MeasurableSet[F t] E)
    (W Y A : ClosedTime T → Ω → ℝ) (hW : LocalMProcessWitness P F W)
    (hA : LocalCovarianceWitness P F W W A)
    (hclock : ∀ w (r : ℝ),0≤r → (r:EReal)<T → A (realTimeClamp r) w=r)
    (hYa : ∀ t,t<⊤ → Measurable[F t] (Y t))
    (hYc : ∀ w t,t<⊤ → ContinuousAt (fun s => Y s w) t)
    (φ : (Fin 2 → ℝ) → ℝ) (hφ : ContDiff ℝ 2 φ)
    (f g : ℝ → ℝ) (hf : ContDiff ℝ 1 f) (hg : Continuous g)
    (hflow : ∀ x y,fderiv ℝ φ ![x,y] (Pi.single 0 1)=f (φ ![x,y]))
    (hinit : ∀ y,φ ![0,y]=y)
    (hd : ∀ w (r : ℝ),0<r → (r:EReal)<T →
      HasDerivAt (fun s => Y (realTimeClamp s) w)
        (g (φ ![W (realTimeClamp r) w,Y (realTimeClamp r) w])/
          fderiv ℝ φ ![W (realTimeClamp r) w,Y (realTimeClamp r) w] (Pi.single 1 1)) r) :
    let X := fun t w => φ ![W t w,Y t w]
    AdaptedLocalVariationWitness F Y ∧
    ∃ N : ClosedTime T → Ω → ℝ,
      LocalMProcessWitness P F N ∧
      ItoCovarianceFormula P F W (fun z => f (X (realTimeClamp z.2) z.1)) N ∧
      ∀ (d : ℝ),0≤d → (d:EReal)<T →
        X (realTimeClamp d)=ᵐ[P] fun w => X ⊥ w+N (realTimeClamp d) w+
          (∫ r in 0..d,g (X (realTimeClamp r) w)+
            deriv f (X (realTimeClamp r) w)*f (X (realTimeClamp r) w)/2) := by
  dsimp only
  let V := fun t w => ![W t w,Y t w]
  let B := fun z : Fin 2 → ℝ => g (φ z)/fderiv ℝ φ z (Pi.single 1 1)
  obtain ⟨hBc,hcancel⟩ := flow_drift_continuous_and_cancellation φ hφ f hf hflow hinit g hg
  have hVc w t (ht : t<⊤) : ContinuousAt (fun s => V s w) t := by
    apply continuousAt_pi.mpr
    intro i
    fin_cases i
    · exact hW.path P F w t ht
    · exact hYc w t ht
  have hVm w : Measurable (fun r : ℝ => V (realTimeClamp r) w) := by
    apply measurable_pi_lambda
    intro i
    fin_cases i
    · exact open_path_real_measurable _ (hW.path P F w)
    · exact open_path_real_measurable _ (hYc w)
  have hVrc w (R : ℝ) (hR : 0≤R) (hRT : (R:EReal)<T) :
      ContinuousOn (fun r => V (realTimeClamp r) w) (Icc 0 R) := by
    intro r hr
    exact ((hVc w _ (real_time_below r hr.1 ((EReal.coe_le_coe hr.2).trans_lt hRT))).comp
      real_time_clamp_continuous.continuousAt).continuousWithinAt
  have hBrc w R hR hRT := hBc.comp_continuousOn (hVrc w R hR hRT)
  have hY := ode_adapted_local_variation hT F hF Y (fun r w => B (V (realTimeClamp r) w))
    hYa hYc hBrc hd
  obtain ⟨c,hc0,hcm,hcT,_,_,hcc⟩ := positive_real_time_exhaustion hT
  let hc := fun n => (hc0 n).le
  obtain ⟨N,D,J,hN,hNI,hD,hJ,he⟩ := martingale_variation_ito P hT F hF hle hnull
    W Y A hW hY hYc hA φ hφ c hc hcm.monotone hcT hcc
  have hpy : Continuous (fun z => fderiv ℝ φ z (Pi.single 1 1)) :=
    (hφ.continuous_fderiv (by norm_num)).clm_apply continuous_const
  refine ⟨hY,N,hN,?_,?_⟩
  · simpa only [hflow] using hNI
  intro d hd0 hdT
  have hdt := real_time_below d hd0 hdT
  have hDi := ode_variation_integral_density P Y D
    (fun z => B (V (realTimeClamp z.2) z.1))
    (fun z => fderiv ℝ φ (V (realTimeClamp z.2) z.1) (Pi.single 1 1))
    hYc (fun w => hBc.measurable.comp (hVm w)) hBrc hd c hc hcT hcc
    (fun w => hpy.measurable.comp (hVm w)) (fun n w => hpy.comp_continuousOn (hVrc w _ (hc n) (hcT n))) hD d hd0 hdT
  obtain ⟨j,hj⟩ := hcc _ hdt
  have hdj : d≤c j := by
    change (realTimeClamp d:EReal)<(realTimeClamp (c j):EReal) at hj
    rw [real_time_clamp_eq d hd0 hdT.le,real_time_clamp_eq (c j) (hc j) (hcT j).le] at hj
    exact (EReal.coe_lt_coe_iff.mp hj).le
  have hJi := clock_variation_integral_at_time P A J _ c hc hcT
    (fun n w r hr => hclock w r hr.1 ((EReal.coe_le_coe hr.2).trans_lt (hcT n))) hJ j d hd0 hdj
  filter_upwards [he,hDi,hJi] with w hew hdw hjw
  have heD : D (realTimeClamp d) w=∫ r in 0..d,g (φ (V (realTimeClamp r) w)) := by
    rw [hdw]
    apply intervalIntegral.integral_congr
    intro r _
    exact hcancel _
  have heJ : J (realTimeClamp d) w=∫ r in 0..d,
      deriv f (φ (V (realTimeClamp r) w))*f (φ (V (realTimeClamp r) w)) := by
    rw [hjw]
    apply intervalIntegral.integral_congr
    intro r _
    exact flow_second_derivative φ hφ f hf hflow _ _
  have hi1 := ((hg.comp hφ.continuous).comp_continuousOn (hVrc w d hd0 hdT)).intervalIntegrable_of_Icc (μ := volume) hd0
  have hi2 := (((hf.continuous_deriv le_rfl).comp hφ.continuous).mul
    (hf.continuous.comp hφ.continuous)).comp_continuousOn (hVrc w d hd0 hdT)
  have hi2' := hi2.intervalIntegrable_of_Icc (μ := volume) hd0
  have hh := hew (realTimeClamp d) hdt
  rw [heD,heJ] at hh
  dsimp only [Function.comp_def,Pi.mul_apply,V] at hi1 hi2' hh
  rw [intervalIntegral.integral_add hi1 (hi2'.div_const 2),intervalIntegral.integral_div]
  exact hh.trans (by ring)

end Asakura.Chapter4
