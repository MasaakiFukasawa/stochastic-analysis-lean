import Chapter7ClockHalfTime
import Chapter13FiniteParameterFubini
import Chapter4BrownianTimeMeasure
import Chapter4FinitePathLift

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter13
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter4
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

/-- The energy measure constructed by stochastic Fubini for Brownian motion
is the original probability times Lebesgue time, independently of the
regular quadratic-variation representative chosen by the construction. -/
theorem brownian_energy_measure_identification {Ω:Type} {m:MeasurableSpace Ω}
    (P:Measure Ω) [IsProbabilityMeasure P]
    (F:HalfClosedTime → MeasurableSpace Ω) (hF:Monotone F) (hle:∀t,F t≤m)
    (W C A:HalfClosedTime → Ω → ℝ)
    (hC:LocalCovarianceWitness P F W W C) (hA:LocalCovarianceWitness P F W W A)
    (hclock:∀w r,0≤r → C (realTimeClamp r) w=r)
    (c:ℕ → ℝ) (hc:∀n,0<c n) (hcm:Monotone c) (hco:∀r:ℝ,∃n,r≤c n)
    (hAm:∀n w,MonotoneOn (fun r => A (realTimeClamp r) w) (Icc 0 (c n)))
    (hAc:∀n w,ContinuousOn (fun r => A (realTimeClamp r) w) (Icc 0 (c n)))
    (ν:Measure (Ω × ℝ))
    (he:∀f:Ω × ℝ → ℝ≥0∞,Measurable f → (∫⁻z,f z∂ν)=∫⁻w,⨆n,∫⁻r,f (w,r)
      ∂(intervalStieltjes 0 (c n) (hc n).le (fun r => A (realTimeClamp r) w) (hAm n w)
        (fun r hr => (hAc n w r hr).mono inter_subset_left)).measure∂P) :
    ν=P.prod (volume.restrict (Ioi 0)) := by
  have hCA:=hA.unique P F hF hle hC
  have hun:(⋃n,Ioc (0:ℝ) (c n))=Ioi 0 := by
    ext r
    simp only [mem_iUnion,mem_Ioc,mem_Ioi]
    constructor
    · rintro ⟨n,hr,_⟩;exact hr
    · intro hr
      obtain ⟨n,hn⟩:=hco r
      exact ⟨n,hr,hn⟩
  apply Measure.ext_of_lintegral
  intro f hf
  rw [he f hf,lintegral_prod _ hf.aemeasurable]
  apply lintegral_congr_ae
  filter_upwards [hCA] with w hw
  have hm n:(intervalStieltjes 0 (c n) (hc n).le (fun r => A (realTimeClamp r) w) (hAm n w)
      (fun r hr => (hAc n w r hr).mono inter_subset_left)).measure=volume.restrict (Ioc 0 (c n)) := by
    rw [←clock_stieltjes_measure 0 (c n) (hc n).le]
    congr 1
    apply StieltjesFunction.ext
    intro r
    change A (realTimeClamp (intervalClamp 0 (c n) (hc n).le r)) w=intervalClamp 0 (c n) (hc n).le r
    have hr:=intervalClamp_mem 0 (c n) (hc n).le r
    rw [hw _ (real_time_below _ hr.1 (EReal.coe_lt_top _)),hclock w _ hr.1]
  simp_rw [hm]
  have hd:Directed (· ⊆ ·) (fun n => Ioc (0:ℝ) (c n)) := by
    intro i j
    exact ⟨max i j,Ioc_subset_Ioc_right (hcm (le_max_left _ _)),Ioc_subset_Ioc_right (hcm (le_max_right _ _))⟩
  rw [←setLIntegral_iUnion_of_directed _ hd,hun]
end Asakura.Chapter13
#print axioms Asakura.Chapter13.brownian_energy_measure_identification
