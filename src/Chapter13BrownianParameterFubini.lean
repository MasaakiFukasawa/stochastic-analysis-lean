import Chapter13BrownianEnergyMeasure
import Chapter4BrownianSystem

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter13
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter4
set_option maxHeartbeats 3400000
set_option backward.isDefEq.respectTransparency false

/-- Stochastic Fubini for a Brownian coordinate with the original
probability-time L2 hypothesis, not an abstract energy-measure hypothesis. -/
theorem brownian_parameter_fubini {Ω E:Type} {m:MeasurableSpace Ω} [MeasurableSpace E]
    (P:Measure Ω) [IsProbabilityMeasure P] {d:ℕ} (B:BrownianSystem P d) (i:Fin d)
    (μ:Measure E) [IsFiniteMeasure μ] (H:E × (Ω × ℝ) → ℝ) (hm:Measurable H)
    (hp:∀b,0<b → @Measurable _ _
      ((inferInstance : MeasurableSpace E).prod (progressiveSpace (fun t:Icc (0:ℝ) b => B.F (realTimeClamp t.val)))) inferInstance
      (fun z:E × (Ω × Icc (0:ℝ) b) => H (z.1,(z.2.1,z.2.2.val))))
    (hi:Integrable (fun z => H z^2) (μ.prod (P.prod (volume.restrict (Ioi 0))))) :
    ∃Z:E → continuousM2Terminal P B.F,Integrable Z μ ∧
      (∀ᵐx∂μ,∃Y:HalfClosedTime → Ω → ℝ,∃hY:ContinuousM2Witness P B.F Y,
        ItoCovarianceFormula P B.F (B.W i) (fun z => H (x,z)) Y ∧ Z x=m2TerminalOfProcess P B.F Y hY) ∧
      ∃Ybar:HalfClosedTime → Ω → ℝ,∃hYbar:ContinuousM2Witness P B.F Ybar,
        ItoCovarianceFormula P B.F (B.W i) (fun z => ∫x,H (x,z)∂μ) Ybar ∧
        (∫x,Z x∂μ)=m2TerminalOfProcess P B.F Ybar hYbar := by
  obtain ⟨c,hc,A,hAm,hAc,ν,hA,hν,hcm,hcT,hcc,henergy,L,hmain⟩:=
    finite_parameter_stochastic_fubini P (by simp : (0:EReal)<⊤) B.F B.mono B.le B.null (B.W i) (B.martingale i)
  have hco:∀r:ℝ,∃n,r≤c n := by
    intro r
    by_cases hr:0≤r
    · obtain ⟨n,hn⟩:=hcc (realTimeClamp r) (real_time_below r hr (EReal.coe_lt_top r))
      change (realTimeClamp r:EReal)<(realTimeClamp (c n):EReal) at hn
      rw [real_time_clamp_eq r hr le_top,real_time_clamp_eq (c n) (hc n).le le_top] at hn
      exact ⟨n,(EReal.coe_lt_coe_iff.mp hn).le⟩
    · exact ⟨0,(le_of_not_ge hr).trans (hc 0).le⟩
  have hνeq:=brownian_energy_measure_identification P B.F B.mono B.le (B.W i) (B.C i i) A
    (B.cov i i) hA (B.diagonal_clock i) c hc hcm.monotone hco hAm hAc ν henergy
  have hhi:Integrable (fun z => H z^2) (μ.prod ν) := by rwa [hνeq]
  exact (hmain E μ H (fun n => hp (c n) (hc n)) hm hhi).2
end Asakura.Chapter13
#print axioms Asakura.Chapter13.brownian_parameter_fubini
