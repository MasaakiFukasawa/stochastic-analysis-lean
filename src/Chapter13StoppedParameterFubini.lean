import Chapter13BrownianParameterFubini
import Chapter13ParameterEnergyReorder
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
theorem brownian_fubini_from_stopped_energy {Ω E:Type} {m:MeasurableSpace Ω} [MeasurableSpace E]
    (P:Measure Ω) [IsProbabilityMeasure P] {d:ℕ} (B:BrownianSystem P d) (i:Fin d)
    (μ:Measure E) [IsFiniteMeasure μ] (H:E × (Ω × ℝ) → ℝ) (hm:Measurable H)
    (hp:∀b,0<b → @Measurable _ _
      ((inferInstance : MeasurableSpace E).prod (progressiveSpace (fun t:Icc (0:ℝ) b => B.F (realTimeClamp t.val)))) inferInstance
      (fun z:E × (Ω × Icc (0:ℝ) b) => H (z.1,(z.2.1,z.2.2.val))))
    (hi:∀ᵐw∂P,Integrable (fun z:E × ℝ => H (z.1,(w,z.2))^2) (μ.prod (volume.restrict (Ioi 0))))
    (K:ℝ) (hb:∀ᵐw∂P,(∫z:E × ℝ,H (z.1,(w,z.2))^2∂μ.prod (volume.restrict (Ioi 0)))≤K) :
    ∃Z:E → continuousM2Terminal P B.F,Integrable Z μ ∧
      (∀ᵐx∂μ,∃Y:HalfClosedTime → Ω → ℝ,∃hY:ContinuousM2Witness P B.F Y,
        ItoCovarianceFormula P B.F (B.W i) (fun z => H (x,z)) Y ∧ Z x=m2TerminalOfProcess P B.F Y hY) ∧
      ∃Ybar:HalfClosedTime → Ω → ℝ,∃hYbar:ContinuousM2Witness P B.F Ybar,
        ItoCovarianceFormula P B.F (B.W i) (fun z => ∫x,H (x,z)∂μ) Ybar ∧
        (∫x,Z x∂μ)=m2TerminalOfProcess P B.F Ybar hYbar := by
  exact brownian_parameter_fubini P B i μ H hm hp
    (parameter_energy_reorder P μ (volume.restrict (Ioi 0)) H hm hi K hb)
end Asakura.Chapter13
#print axioms Asakura.Chapter13.brownian_fubini_from_stopped_energy
