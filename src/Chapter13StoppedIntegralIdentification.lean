import Chapter13StoppedField
import Chapter4StoppedBrownianIntegral
import Chapter4BrownianSystem

open MeasureTheory Set
namespace Asakura.Chapter13
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter4
set_option maxHeartbeats 3400000
set_option backward.isDefEq.respectTransparency false

/-- Identify the integral produced by localized Fubini with the stopped
original integral, by construction and uniqueness of actual Ito integrals. -/
theorem stopped_integral_identified {Ω:Type*} {m:MeasurableSpace Ω}
    (P:Measure Ω) [IsProbabilityMeasure P] {d:ℕ} (B:BrownianSystem P d) (i:Fin d)
    (H:Ω × ℝ → ℝ)
    (hp:∀R,0<R → @Measurable _ _ (progressiveSpace (fun t:Icc (0:ℝ) R => B.F (realTimeClamp t.val))) inferInstance
      (fun z:Ω × Icc (0:ℝ) R => H (z.1,z.2.val)))
    (hi:∀R,0≤R → ∀ᵐw∂P,IntervalIntegrable (fun r => H (w,r)^2) volume 0 R)
    (N:HalfClosedTime → Ω → ℝ) (hN:LocalMProcessWitness P B.F N)
    (hNI:ItoCovarianceFormula P B.F (B.W i) H N)
    (R:ℝ) (hR:0≤R) (τ:Ω → HalfClosedTime)
    (hτ:∀t,MeasurableSet[B.F t] {w | τ w≤t})
    (Z:HalfClosedTime → Ω → ℝ) (hZ:LocalMProcessWitness P B.F Z)
    (hZI:ItoCovarianceFormula P B.F (B.W i)
      (fun z => (Ioc (0:ℝ) (finitePrefixTime R hR (τ z.1)).val).indicator (fun r => H (z.1,r)) z.2) Z) :
    ∀ᵐw∂P,∀t,t<⊤ → Z t w=N (min (min (realTimeClamp R) (τ w)) t) w := by
  have hT:(0:EReal)<⊤ := by simp
  obtain ⟨c,hc,hcm,hcT,hct,hcut,hcc⟩:=positive_real_time_exhaustion hT
  have hstop:∀t,MeasurableSet[B.F t] {w | min (realTimeClamp R) (τ w)≤t} := by
    intro t
    by_cases h:realTimeClamp (T:=(⊤:EReal)) R≤t
    · simp [min_le_iff,h]
    · simpa only [min_le_iff,h,false_or] using hτ t
  obtain ⟨Y,hY,hYI,hYe,_,_⟩:=stopped_brownian_integral_constructed P hT B.F B.mono B.le B.null
    (B.W i) (B.C i i) N (B.martingale i) (B.cov i i) hN c hc hcm hcT hct hcut hcc
    (fun n w r hr => B.diagonal_clock i w r hr.1) H (fun n => hp (c n) (hc n))
    (fun n => hi (c n) (hc n).le) hNI (fun w => min (realTimeClamp R) (τ w))
    (fun w => (min_le_left _ _).trans_lt (real_time_below R hR (EReal.coe_lt_top R))) hstop
  have hh:ItoCovarianceFormula P B.F (B.W i)
      (fun z => (Ioc (0:ℝ) (finitePrefixTime R hR (τ z.1)).val).indicator (fun r => H (z.1,r)) z.2) Y := by
    convert hYI using 1
    funext z
    exact stopped_field_indicator R hR (τ z.1) z.2 (H z)
  have hu:=ItoCovarianceFormula.unique P hT B.F B.mono B.le B.null (B.W i) Z Y _
    (B.martingale i) hZ hY hZI hh
  filter_upwards [hu,hYe] with w hw hy
  intro t ht
  exact (hw t ht).trans (hy t ht)
end Asakura.Chapter13
#print axioms Asakura.Chapter13.stopped_integral_identified
