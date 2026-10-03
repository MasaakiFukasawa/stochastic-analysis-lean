import Chapter11IntegralMeanZero
import Chapter2M2CovarianceL1Bound

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter11
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter5 Asakura.Chapter6
set_option maxHeartbeats 3400000
set_option backward.isDefEq.respectTransparency false

/-- Matching a local Ito representation to the represented price gives
finite energy and a bound uniform over all preterminal stopping horizons.
The energy identity is derived from the actual quadratic variation. -/
theorem brownian_prefix_energy_of_price {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : BrownianSystem P 1)
    (G : Ω × ℝ → ℝ)
    (hGp : ∀ d,0<d → @Measurable _ _
      (progressiveSpace (fun t : Icc (0:ℝ) d => B.F (realTimeClamp t.val))) inferInstance
      (fun z : Ω × Icc (0:ℝ) d => G (z.1,z.2.val)))
    (hGi : ∀ d,0<d → ∀ᵐ w ∂P,IntervalIntegrable (fun r => (G (w,r))^2) volume 0 d)
    (N M : HalfClosedTime → Ω → ℝ) (hN : LocalMProcessWitness P B.F N)
    (hNI : ItoCovarianceFormula P B.F (B.W 0) G N) (hM : ContinuousM2Witness P B.F M)
    (R : ℝ) (hR : 0≤R)
    (he : ∀ t∈Icc 0 R,N (realTimeClamp t)=ᵐ[P] M (realTimeClamp t)) :
    Integrable (fun w => ∫ r in 0..R,(G (w,r))^2) P ∧
      (∫ w,(∫ r in 0..R,(G (w,r))^2) ∂P)=∫ w,(M (realTimeClamp R) w)^2 ∂P ∧
      (∫ w,(∫ r in 0..R,(G (w,r))^2) ∂P)≤∫ w,(M ⊤ w)^2 ∂P := by
  have hT : (0:EReal)<⊤ := by simp
  obtain ⟨c,hc,hcm,hcT,hct,hcut,hcc⟩ := positive_real_time_exhaustion hT
  obtain ⟨C,hC,hCe⟩ := clock_ito_integral_bracket P hT B.F B.mono B.le B.null
    (B.W 0) (B.C 0 0) N (B.martingale 0) (B.cov 0 0) hN
    c hc hcm hcT hct hcut hcc (fun j w r hr => by simpa using B.clock 0 0 w r hr.1)
    G (fun j => hGp (c j) (hc j)) (fun j => hGi (c j) (hc j)) hNI
  have hstop t : MeasurableSet[B.F t] {w : Ω | realTimeClamp (T:=(⊤:EReal)) R≤t} := by
    by_cases h : realTimeClamp (T:=(⊤:EReal)) R≤t <;> simp [h]
  have hRt := real_time_below R hR (EReal.coe_lt_top R)
  obtain ⟨hnm,hnc⟩ := hN.stopped_regular P B.F B.mono B.le (fun _ => realTimeClamp R) hstop (fun _ => hRt)
  have hMs := continuous_m2_stopped P B.F B.mono B.le M hM (fun _ => realTimeClamp R) hstop
  have hEq t : (fun w => N (min (realTimeClamp R) t) w)=ᵐ[P] fun w => M (min (realTimeClamp R) t) w := by
    obtain ⟨r,hr,hrT,heq⟩ := finite_closed_time_real (min (realTimeClamp R) t) ((min_le_left _ _).trans_lt hRt)
    have hrR : r≤R := by
      have hh : realTimeClamp (T:=(⊤:EReal)) r≤realTimeClamp R := heq ▸ min_le_left _ _
      change (realTimeClamp r:EReal)≤(realTimeClamp R:EReal) at hh
      rw [real_time_clamp_eq r hr le_top,real_time_clamp_eq R hR le_top] at hh
      exact EReal.coe_le_coe_iff.mp hh
    simpa only [←heq] using he r ⟨hr,hrR⟩
  have hNs : ContinuousM2Witness P B.F (fun t w => N (min (realTimeClamp R) t) w) := by
    refine ⟨hnm,fun t => (hMs.moment t).ae_eq (hEq t).symm,hnc,?_,?_⟩
    · intro s t hst
      exact (condExp_congr_ae (hEq t)).trans ((hMs.martingale s t hst).trans (hEq s).symm)
    · exact (hEq ⊥).trans hMs.initial
  obtain ⟨hCi,henergy⟩ := stopped_M2_energy P B.F B.mono B.le B.null N C hN hC
    (fun _ => realTimeClamp R) hstop (fun _ => hRt) hNs
  have hCE := hCe R hR (EReal.coe_lt_top R)
  have hEn : (∫ w,(∫ r in 0..R,(G (w,r))^2) ∂P)=∫ w,(M (realTimeClamp R) w)^2 ∂P := by
    rw [←integral_congr_ae hCE,←henergy]
    exact integral_congr_ae ((he R ⟨hR,le_rfl⟩).mono fun w hw => congrArg (fun x : ℝ => x^2) hw)
  refine ⟨hCi.congr hCE,hEn,?_⟩
  rw [hEn]
  have hh := continuous_martingale_increment_energy P B.F B.le M hM (realTimeClamp R) ⊤ le_top
  have hp : 0≤∫ w,(M ⊤ w-M (realTimeClamp R) w)^2 ∂P := integral_nonneg fun _ => sq_nonneg _
  linarith

end Asakura.Chapter11
