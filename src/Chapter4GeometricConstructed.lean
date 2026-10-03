import Chapter4GeometricCalculus
import Chapter5TimeSpaceBrownian

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter4
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter5
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

/-- The explicit geometric Brownian path solves the integral equation on
an arbitrary finite horizon. The noise integral is constructed by Ito's
formula; its integrand is precisely b times the explicit path on this horizon. -/
theorem geometric_sde_constructed
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0≤T)] (hT : 0<T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (hnull : ∀ t E,MeasurableSet[m] E → P E=0 → MeasurableSet[F t] E)
    (W A : ClosedTime T → Ω → ℝ) (hW : LocalMProcessWitness P F W)
    (hA : LocalCovarianceWitness P F W W A)
    (hclock : ∀ w (r : ℝ),0≤r → (r:EReal)<T → A (realTimeClamp r) w=r)
    (R : ℝ) (hR : 0≤R) (hRT : (R:EReal)<T) (y a b : ℝ) :
    ∃ N : ClosedTime T → Ω → ℝ,
      LocalMProcessWitness P F N ∧
      ItoCovarianceFormula P F W
        (fun z => b*geometricFlow y a b ![(finitePrefixTime (T := T) R hR (realTimeClamp z.2)).val,
          W (realTimeClamp z.2) z.1]) N ∧
      ∀ d∈Icc 0 R,(fun w => geometricFlow y a b ![d,W (realTimeClamp d) w]) =ᵐ[P]
        fun w => y+a*(∫ r in 0..d,geometricFlow y a b ![r,W (realTimeClamp r) w])+N (realTimeClamp d) w := by
  obtain ⟨c,hc,hcm,hcT,hct,hcut,hcc⟩ := positive_real_time_exhaustion hT
  obtain ⟨N,hN,hNI,he⟩ := time_space_clock_martingale_ito P hT F hF hle hnull W A hW hA
    R hR hRT (geometricFlow y a b) (geometricFlow_smooth y a b)
    c (fun n => (hc n).le) hcm.monotone hcT hcc
    (fun n w r hr => hclock w r hr.1 ((EReal.coe_le_coe hr.2).trans_lt (hcT n)))
  refine ⟨N,hN,?_,?_⟩
  · simpa only [geometricFlow_fderiv_space] using hNI
  · intro d hd
    filter_upwards [he d hd.1 hd.2,hW.initial P F] with w hw hzero
    simp only [geometricFlow_fderiv_time,geometricFlow_fderiv_second] at hw
    simp only [Pi.zero_apply] at hzero
    rw [hzero] at hw
    have hinit : geometricFlow y a b ![0,0]=y := by simp [geometricFlow]
    rw [hinit,intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul] at hw
    calc geometricFlow y a b ![d,W (realTimeClamp d) w] = _ := hw
         _ = _ := by ring

end Asakura.Chapter4
